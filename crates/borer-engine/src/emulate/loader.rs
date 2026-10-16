//! The loader environment a real process carries and a run without one
//! had to do without: the module list behind the process block, and the
//! export tables a routine that resolves by hash reads.
//!
//! Code that means to survive without an import table does not call
//! `GetProcAddress`; it walks `gs:[0x60]` (x64) or `fs:[0x30]` (x86) to the
//! process block, follows `Ldr` to the loader's module list, hashes each
//! module's name and its export names against constants it carries, and
//! computes the function's address out of the export directory at the
//! module's base. Protector bootstraps, packers and shellcode all do this,
//! whatever their brand, so the emulator plants the walk's every step:
//!
//! * a loader block whose three module lists link one entry per module:
//!   the image itself, `ntdll.dll`, `kernel32.dll`, then every dll the
//!   image imports, in name order;
//! * per dll, a small image with real headers and a real export directory
//!   whose names are the image's own imports from that dll, each pointing
//!   at a cell of its own that is registered as that API's stub, so a call
//!   the walk computes is serviced like a call through the import table.
//!   `ntdll.dll` and `kernel32.dll` also export the names a hash resolver
//!   looks up when the image imports nothing ([`NTDLL_BASELINE`],
//!   [`KERNEL32_BASELINE`]): an empty directory answers every hash with
//!   not-found, and the bootstrap then calls a null pointer.
//!
//! The bytes are planted as setup ([`Emulator::plant`]): they read as
//! memory, they never count as code the run unpacked, and a hash over them
//! matches what the same hash over the real process's tables finds, because
//! the names are the same strings the loader would have written.

use std::collections::BTreeMap;

use super::{Emulator, PEB_AT};
use crate::num::from_usize;
use crate::program::{Program, SymbolKind};

/// Where the loader block lives on a 64-bit target: above the thread
/// block's span, in the gap nothing else uses.
const LOADER_BASE_64: u64 = 0x7fff_e010_0000;

/// Where the loader block lives on a 32-bit target: above the thread
/// block's span, which ends at `0x7ffe_0000`.
const LOADER_BASE_32: u64 = 0x7ffe_1000;

/// Most modules one environment lists; a file that imports from more has
/// the rest of its dlls left out of the walk.
const MODULES_MAX: usize = 64;

/// Most exports one synthesized module carries; a dll whose imports exceed
/// this keeps its first names, in the order the symbols hold.
const EXPORTS_MAX: usize = 256;

/// Names `kernel32.dll` exports even when the image imports none of them.
///
/// A protector with no import table hashes these out of the export
/// directory. `VirtualAlloc` stays first, so a walk that takes the first
/// name still reaches the allocator. Each name is one the emulator
/// services, or a vectored-handler registration whose success is a
/// non-zero handle.
const KERNEL32_BASELINE: &[&str] = &[
    "VirtualAlloc",
    "VirtualAllocEx",
    "VirtualProtect",
    "VirtualFree",
    "LoadLibraryA",
    "LoadLibraryW",
    "GetProcAddress",
    "GetModuleHandleA",
    "GetModuleHandleW",
    "HeapAlloc",
    "IsDebuggerPresent",
    "CheckRemoteDebuggerPresent",
    "GetThreadContext",
    "OutputDebugStringA",
    "OutputDebugStringW",
    "AddVectoredExceptionHandler",
    "RemoveVectoredExceptionHandler",
];

/// Names `ntdll.dll` exports even when the image imports none of them.
///
/// These are the queries whose benign answer is "nothing is attached".
/// An allocator that lives only in `ntdll` is not among them: handing back
/// zero for `NtAllocateVirtualMemory` would make a bootstrap believe the
/// allocation failed.
const NTDLL_BASELINE: &[&str] = &[
    "NtQueryInformationProcess",
    "ZwQueryInformationProcess",
    "NtSetInformationThread",
    "ZwSetInformationThread",
    "NtGetContextThread",
    "ZwGetContextThread",
    "NtQuerySystemInformation",
    "ZwQuerySystemInformation",
];

/// The names a system dll keeps on top of whatever the image imports.
///
/// # Arguments
///
/// * `dll` - The dll's name, any case.
fn baseline(dll: &str) -> &'static [&'static str] {
    if dll.eq_ignore_ascii_case("kernel32.dll") {
        KERNEL32_BASELINE
    } else if dll.eq_ignore_ascii_case("ntdll.dll") {
        NTDLL_BASELINE
    } else {
        &[]
    }
}

/// Appends [`baseline`] names the module does not already export, then
/// holds the list to [`EXPORTS_MAX`].
///
/// Imported names stay in front, so the first export of a dll the image
/// does import is still that import.
///
/// # Arguments
///
/// * `m` - The module, mutated.
fn merge_baseline(m: &mut Module) {
    for name in baseline(&m.dll) {
        if m.exports.iter().any(|e| e.eq_ignore_ascii_case(name)) {
            continue;
        }
        m.exports.push((*name).to_owned());
    }
    m.exports.truncate(EXPORTS_MAX);
}

/// The width-dependent offsets of the loader's structures, Windows' own.
#[derive(Debug, Clone, Copy)]
struct Layout {
    /// `PEB.Ldr` from the process block's base.
    peb_ldr: u64,
    /// `PEB_LDR_DATA.InLoadOrderModuleList` from the loader block.
    load_list: u64,
    /// `PEB_LDR_DATA.InMemoryOrderModuleList`.
    memory_list: u64,
    /// `PEB_LDR_DATA.InInitializationOrderModuleList`.
    init_list: u64,
    /// `LDR_DATA_TABLE_ENTRY.InMemoryOrderLinks` from the entry's base.
    entry_memory: u64,
    /// `LDR_DATA_TABLE_ENTRY.InInitializationOrderLinks`.
    entry_init: u64,
    /// `LDR_DATA_TABLE_ENTRY.EntryPoint`.
    entry_point: u64,
    /// `LDR_DATA_TABLE_ENTRY.DllBase`.
    dll_base: u64,
    /// `LDR_DATA_TABLE_ENTRY.SizeOfImage`.
    image_size: u64,
    /// `LDR_DATA_TABLE_ENTRY.FullDllName`.
    full_name: u64,
    /// `LDR_DATA_TABLE_ENTRY.BaseDllName`.
    base_name: u64,
    /// Bytes of one entry.
    entry_span: u64,
    /// The optional header's `ImageBase` field.
    opt_image_base: u64,
    /// The optional header's `SizeOfImage` field.
    opt_image_size: u64,
    /// The optional header's `NumberOfRvaAndSizes` field.
    opt_dirs_count: u64,
    /// The optional header's first data directory, the export table.
    opt_export_dir: u64,
    /// Bytes of the optional header a `SizeOfOptionalHeader` names.
    opt_span: u64,
}

/// The 64-bit layout, a `PE32+` process.
const LAYOUT_64: Layout = Layout {
    peb_ldr: 0x18,
    load_list: 0x10,
    memory_list: 0x20,
    init_list: 0x30,
    entry_memory: 0x10,
    entry_init: 0x20,
    entry_point: 0x38,
    dll_base: 0x30,
    image_size: 0x40,
    full_name: 0x48,
    base_name: 0x58,
    entry_span: 0x80,
    opt_image_base: 0x18,
    opt_image_size: 0x38,
    opt_dirs_count: 0x6c,
    opt_export_dir: 0x70,
    opt_span: 0xf0,
};

/// The 32-bit layout, a `PE32` process.
const LAYOUT_32: Layout = Layout {
    peb_ldr: 0x0c,
    load_list: 0x0c,
    memory_list: 0x14,
    init_list: 0x1c,
    entry_memory: 0x08,
    entry_init: 0x10,
    entry_point: 0x1c,
    dll_base: 0x18,
    image_size: 0x20,
    full_name: 0x24,
    base_name: 0x2c,
    entry_span: 0x40,
    opt_image_base: 0x1c,
    opt_image_size: 0x30,
    opt_dirs_count: 0x5c,
    opt_export_dir: 0x60,
    opt_span: 0xe0,
};

/// One module of the list: its name and the APIs to export from it.
#[derive(Debug)]
struct Module {
    /// The dll's name as its import symbols spell it, without the `!name`.
    dll: String,
    /// The APIs the image imports from it, as the symbols spell them.
    exports: Vec<String>,
}

/// Reads the image's imports grouped into modules, the loader's order.
///
/// The image itself is not among them; it is always the first entry and is
/// described from the image's own facts. `ntdll.dll` and `kernel32.dll`
/// come before the rest whatever the image imports, because a walk that
/// looks for them stops at the first match and Windows puts them there.
/// The grouping ignores case, as the loader's own lookups do, and keeps
/// each dll's name as its symbols first spelled it.
///
/// # Arguments
///
/// * `p` - The loaded image.
///
/// # Returns
///
/// The modules, `ntdll.dll` and `kernel32.dll` first among the dlls.
fn modules_of(p: &Program) -> Vec<Module> {
    let mut grouped: BTreeMap<String, Module> = BTreeMap::new();
    for s in &p.symbols {
        if s.kind != SymbolKind::Import {
            continue;
        }
        let Some((dll, name)) = s.name.rsplit_once('!') else {
            continue;
        };
        let key = dll.to_lowercase();
        grouped
            .entry(key)
            .and_modify(|m| m.exports.push(name.to_owned()))
            .or_insert_with(|| Module {
                dll: dll.to_owned(),
                exports: vec![name.to_owned()],
            });
    }
    let mut out: Vec<Module> = Vec::new();
    for dll in ["ntdll.dll", "kernel32.dll"] {
        let mut m = grouped.remove(dll).unwrap_or_else(|| Module {
            dll: dll.to_owned(),
            exports: Vec::new(),
        });
        merge_baseline(&mut m);
        out.push(m);
    }
    for (_, mut m) in grouped {
        m.exports.truncate(EXPORTS_MAX);
        out.push(m);
    }
    out.truncate(MODULES_MAX.saturating_sub(1));
    out
}

/// The image's own name as the loader shows it, uppercase.
///
/// # Arguments
///
/// * `p` - The loaded image.
fn image_name(p: &Program) -> String {
    p.path
        .file_name()
        .map_or_else(|| "image".to_owned(), |n| n.to_string_lossy().into_owned())
        .to_uppercase()
}

/// The span the image's sections cover, `SizeOfImage`'s shape.
///
/// # Arguments
///
/// * `p` - The loaded image.
fn image_span(p: &Program) -> u64 {
    p.sections
        .iter()
        .map(|s| s.va.0.saturating_add(s.vsize.max(s.file_size)))
        .fold(p.image_base, u64::max)
        .saturating_sub(p.image_base)
}

impl Emulator<'_> {
    /// Plants the loader environment the process block points at.
    ///
    /// The process block's `Ldr` field leads to a loader block whose three
    /// module lists link the image, the two system dlls and every dll the
    /// image imports; each dll's entry names it (uppercase, as the loader
    /// writes it) and points at a small image whose export directory holds
    /// that dll's imported names, each name's function a cell registered as
    /// its API stub. A hash-resolving walk then reads what a real process
    /// would have let it read, and the call it computes lands where the
    /// emulator services it.
    pub(super) fn plant_loader(&mut self) {
        let layout = if self.bitness == 32 {
            LAYOUT_32
        } else {
            LAYOUT_64
        };
        let base = if self.bitness == 32 {
            LOADER_BASE_32
        } else {
            LOADER_BASE_64
        };
        let (peb, word) = (self.teb + PEB_AT, self.word);
        let modules = modules_of(self.program);
        let count = modules.len() + 1;

        // The loader block, then one entry per module, then the strings and
        // the synthesized images, each at the cursor the last one ended at.
        let mut at = base + 0x40 + from_usize(count) * layout.entry_span;
        let mut entries: Vec<u64> = Vec::with_capacity(count);

        // The image's own entry, from the image's facts: the real base and
        // headers, so a walk that reads them reads the truth.
        self.zero(base, 0x40);
        self.zero(base + 0x40, layout.entry_span);
        entries.push(base + 0x40);
        self.plant(base + 0x40 + layout.dll_base, self.program.image_base, word);
        self.plant(
            base + 0x40 + layout.image_size,
            image_span(self.program).max(0x1000),
            word,
        );
        self.plant(
            base + 0x40 + layout.entry_point,
            self.program.entry.unwrap_or_default(),
            word,
        );
        at = self.plant_unicode_string(
            at,
            base + 0x40 + layout.full_name,
            &format!("\\??\\C:\\{}", image_name(self.program)),
        );
        at = self.plant_unicode_string(
            at,
            base + 0x40 + layout.base_name,
            &image_name(self.program),
        );

        for m in &modules {
            let entry = at;
            at += layout.entry_span;
            self.zero(entry, layout.entry_span);
            entries.push(entry);
            let start = align16(at);
            let end = self.plant_dll_image(start, m, &layout);
            self.plant(entry + layout.dll_base, start, word);
            self.plant(
                entry + layout.image_size,
                end.wrapping_sub(start).max(1),
                word,
            );
            self.plant(entry + layout.entry_point, start + 0x58, word);
            let upper = m.dll.to_uppercase();
            at = self.plant_unicode_string(
                end,
                entry + layout.full_name,
                &format!("\\??\\C:\\WINDOWS\\SYSTEM32\\{upper}"),
            );
            at = self.plant_unicode_string(at, entry + layout.base_name, &upper);
        }

        // The loader block's own fields, then the three circular lists.
        self.plant(base, 0x30, 4);
        self.plant(base + 4, 1, 4);
        self.link_list(base + layout.load_list, &entries, 0);
        self.link_list(base + layout.memory_list, &entries, layout.entry_memory);
        self.link_list(base + layout.init_list, &entries, layout.entry_init);
        self.plant(peb + layout.peb_ldr, base, word);
    }

    /// Writes a `UNICODE_STRING` and its text, returning the cursor after
    /// the text.
    ///
    /// The text lands first, NUL-terminated; the descriptor then names it,
    /// `Length` without the NUL and `MaximumLength` with, as the loader
    /// writes both. The descriptor's buffer pointer sits one pointer width
    /// in, past the two lengths and (on 64 bits) the padding.
    ///
    /// # Arguments
    ///
    /// * `at` - Where the text lands.
    /// * `field` - The descriptor's address, the entry's field.
    /// * `text` - The string, as the descriptor's buffer holds it.
    fn plant_unicode_string(&mut self, at: u64, field: u64, text: &str) -> u64 {
        let units: Vec<u16> = text.encode_utf16().collect();
        for (k, u) in units.iter().enumerate() {
            let bytes = u.to_le_bytes();
            self.plant(at + from_usize(k * 2), u64::from(bytes[0]), 1);
            self.plant(at + from_usize(k * 2 + 1), u64::from(bytes[1]), 1);
        }
        self.plant(at + from_usize(units.len() * 2), 0, 2);
        let len = u64::try_from(units.len()).unwrap_or(0);
        self.plant(field, len, 2);
        self.plant(field + 2, len + 2, 2);
        self.plant(field + from_usize(self.word), at, self.word);
        at + from_usize(units.len() * 2 + 2)
    }

    /// Links one of the loader's circular lists.
    ///
    /// # Arguments
    ///
    /// * `head` - The list's head, a field of the loader block.
    /// * `entries` - The entries' addresses, in order.
    /// * `offset` - The links' offset inside each entry.
    fn link_list(&mut self, head: u64, entries: &[u64], offset: u64) {
        let word = from_usize(self.word);
        let links: Vec<u64> = entries.iter().map(|e| e + offset).collect();
        let mut flink = head;
        for link in &links {
            self.plant(flink, *link, self.word);
            flink = *link;
        }
        self.plant(flink, head, self.word);
        let mut blink = head;
        for link in links.iter().rev() {
            self.plant(link + word, blink, self.word);
            blink = *link;
        }
        self.plant(head + word, blink, self.word);
    }

    /// Writes a dll's small image and returns where the cursor continues.
    ///
    /// The image carries the headers a walk reads (`MZ`, the `PE` signature,
    /// an optional header whose first data directory is the export table)
    /// and an export directory whose names are the image's imports from
    /// this dll, in order, each function a distinct cell registered as that
    /// API's stub. A dll with no names gets the headers and an empty
    /// directory. `ntdll.dll` and `kernel32.dll` are not empty: [`modules_of`]
    /// has already merged the baseline a hash resolver needs.
    ///
    /// # Arguments
    ///
    /// * `at` - Where the image lands, 16-byte aligned.
    /// * `m` - The module.
    /// * `layout` - The width's offsets.
    ///
    /// # Returns
    ///
    /// Where the next structure may land, the image's end.
    fn plant_dll_image(&mut self, at: u64, m: &Module, layout: &Layout) -> u64 {
        let (machine, magic) = if self.bitness == 32 {
            (0x014c_u64, 0x10b_u64)
        } else {
            (0x8664, 0x20b)
        };
        let opt = at + 0x58;
        let export = at + 0x100;
        let funcs = align16(export + 0x28);
        let names = align16(funcs + 4 * from_usize(m.exports.len().max(1)));
        let ords = align16(names + 4 * from_usize(m.exports.len().max(1)));
        let text = align16(ords + 2 * from_usize(m.exports.len().max(1)));
        let mut name_rvas: Vec<u64> = Vec::with_capacity(m.exports.len());
        let mut strings = text;
        for name in &m.exports {
            name_rvas.push(strings.wrapping_sub(at));
            strings += from_usize(name.len()) + 1;
        }
        // The directory's own name, the module's, after the names it sorts.
        let own = strings;
        strings += from_usize(m.dll.len()) + 1;
        let cells = align16(strings);
        let end = align16(cells + 8 * from_usize(m.exports.len().max(1)));
        // The whole image reads as present before anything is written, so a
        // walk in strict mode never faults on a field left at zero.
        self.zero(at, end.wrapping_sub(at));

        for (name, rva) in m.exports.iter().zip(name_rvas.iter()) {
            for (k, b) in name.bytes().enumerate() {
                self.plant(at + *rva + from_usize(k), u64::from(b), 1);
            }
        }
        for (k, b) in m.dll.bytes().enumerate() {
            self.plant(own + from_usize(k), u64::from(b), 1);
        }
        let mut cell_rvas: Vec<u64> = Vec::with_capacity(m.exports.len());
        for (i, name) in m.exports.iter().enumerate() {
            let cell = cells + from_usize(i) * 8;
            cell_rvas.push(cell.wrapping_sub(at));
            self.plant(cell, 0xc3, 1);
            self.apis.insert(cell, format!("{}!{}", m.dll, name));
        }

        self.plant(at, 0x5a4d, 2);
        self.plant(at + 0x3c, 0x40, 4);
        self.plant(at + 0x40, 0x4550, 4);
        self.plant(at + 0x44, machine, 2);
        self.plant(at + 0x54, layout.opt_span, 2);
        self.plant(at + 0x56, 0x2022, 2);
        self.plant(opt, magic, 2);
        self.plant(opt + layout.opt_image_base, at, self.word);
        self.plant(opt + layout.opt_image_size, end.wrapping_sub(at), 4);
        self.plant(opt + layout.opt_dirs_count, 16, 4);
        self.plant(opt + layout.opt_export_dir, export.wrapping_sub(at), 4);
        self.plant(opt + layout.opt_export_dir + 4, 0x28, 4);
        self.plant(export + 0x0c, own.wrapping_sub(at), 4);
        self.plant(export + 0x10, 1, 4);
        self.plant(export + 0x14, from_usize(m.exports.len()), 4);
        self.plant(export + 0x18, from_usize(m.exports.len()), 4);
        self.plant(export + 0x1c, funcs.wrapping_sub(at), 4);
        self.plant(export + 0x20, names.wrapping_sub(at), 4);
        self.plant(export + 0x24, ords.wrapping_sub(at), 4);
        for (i, rva) in cell_rvas.iter().enumerate() {
            self.plant(funcs + from_usize(i) * 4, *rva, 4);
        }
        for (i, rva) in name_rvas.iter().enumerate() {
            self.plant(names + from_usize(i) * 4, *rva, 4);
            self.plant(ords + from_usize(i) * 2, from_usize(i), 2);
        }
        end
    }

    /// Plants zeros over a span, so a field this environment does not fill
    /// reads as zero rather than faulting as unmapped.
    ///
    /// # Arguments
    ///
    /// * `at` - The span's start.
    /// * `span` - The span's bytes.
    fn zero(&mut self, at: u64, span: u64) {
        for k in 0..span {
            self.plant(at.wrapping_add(k), 0, 1);
        }
    }
}

/// Rounds an address up to a 16-byte boundary.
///
/// # Arguments
///
/// * `at` - The address.
fn align16(at: u64) -> u64 {
    at.checked_next_multiple_of(16).unwrap_or(at)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::emulate::TEB_64;
    use crate::program::{Arch, Program, Section, Symbol, SymbolKind};

    /// The 64-bit walk to `VirtualAlloc` through the planted structures.
    ///
    /// `gs:[0x60]` to the process block, `Ldr` to the module list, two
    /// links down to `kernel32`, its base, `e_lfanew`, the export
    /// directory, `AddressOfFunctions[0]` as `AddressOfNames[0]`'s match
    /// (the synthesis writes both in one order), and the call.
    const WALK_64: [u8; 59] = [
        0x65, 0x48, 0x8b, 0x04, 0x25, 0x60, 0x00, 0x00, 0x00, // ASM: mov rax,gs:[0x60]
        0x48, 0x8b, 0x40, 0x18, // ASM: mov rax,[rax+0x18]
        0x48, 0x8b, 0x40, 0x10, // ASM: mov rax,[rax+0x10]
        0x48, 0x8b, 0x00, // ASM: mov rax,[rax]
        0x48, 0x8b, 0x00, // ASM: mov rax,[rax]
        0x48, 0x8b, 0x58, 0x30, // ASM: mov rbx,[rax+0x30]
        0x8b, 0x4b, 0x3c, // ASM: mov ecx,[rbx+0x3c]
        0x48, 0x01, 0xd9, // ASM: add rcx,rbx
        0x8b, 0x91, 0x88, 0x00, 0x00, 0x00, // ASM: mov edx,[rcx+0x88]
        0x48, 0x01, 0xda, // ASM: add rdx,rbx
        0x8b, 0x82, 0x1c, 0x00, 0x00, 0x00, // ASM: mov eax,[rdx+0x1c]
        0x48, 0x01, 0xd8, // ASM: add rax,rbx
        0x8b, 0x00, // ASM: mov eax,[rax]
        0x48, 0x01, 0xd8, // ASM: add rax,rbx
        0xff, 0xd0, // ASM: call rax
        0xc3, // ASM: ret
    ];

    /// The 32-bit walk, the same reading on the 32-bit offsets.
    ///
    /// It reaches the process block through `fs:[0x30]`.
    const WALK_32: [u8; 47] = [
        0x64, 0xa1, 0x30, 0x00, 0x00, 0x00, // ASM: mov eax,fs:[0x30]
        0x8b, 0x40, 0x0c, // ASM: mov eax,[eax+0x0c]
        0x8b, 0x40, 0x0c, // ASM: mov eax,[eax+0x0c]
        0x8b, 0x00, // ASM: mov eax,[eax]
        0x8b, 0x00, // ASM: mov eax,[eax]
        0x8b, 0x58, 0x18, // ASM: mov ebx,[eax+0x18]
        0x8b, 0x4b, 0x3c, // ASM: mov ecx,[ebx+0x3c]
        0x01, 0xd9, // ASM: add ecx,ebx
        0x8b, 0x91, 0x78, 0x00, 0x00, 0x00, // ASM: mov edx,[ecx+0x78]
        0x01, 0xda, // ASM: add edx,ebx
        0x8b, 0x82, 0x1c, 0x00, 0x00, 0x00, // ASM: mov eax,[edx+0x1c]
        0x01, 0xd8, // ASM: add eax,ebx
        0x8b, 0x00, // ASM: mov eax,[eax]
        0x01, 0xd8, // ASM: add eax,ebx
        0xff, 0xd0, // ASM: call eax
        0xc3, // ASM: ret
    ];

    /// A one-import image whose code is the walk.
    ///
    /// The import is `KERNEL32.dll!VirtualAlloc`, mixed case as an import
    /// table spells it, with an IAT slot a run could call through.
    fn image(arch: Arch) -> Program {
        let (base, entry, code) = if arch == Arch::X86_64 {
            (0x1_4000_0000, 0x1_4000_1000, WALK_64.to_vec())
        } else {
            (0x400_000, 0x401_000, WALK_32.to_vec())
        };
        let text = Section::mapped(".text", entry, 0, code.len() as u64, false, true);
        let mut p = Program::raw(code, arch, base, Some(entry), vec![text]);
        p.symbols.push(Symbol {
            name: "KERNEL32.dll!VirtualAlloc".to_owned(),
            addr: entry + 0x800,
            kind: SymbolKind::Import,
        });
        p
    }

    /// Reads `bytes` planted bytes at `at` as a little-endian integer.
    fn planted(emu: &Emulator<'_>, at: u64, bytes: usize) -> u64 {
        (0..bytes).fold(0, |v, k| {
            v | u64::from(emu.peek(at + from_usize(k)).unwrap_or(0)) << (k * 8)
        })
    }

    /// Reads a planted NUL-terminated UTF-16 string at `at`.
    fn planted_text(emu: &Emulator<'_>, at: u64) -> String {
        let mut units = Vec::new();
        let mut k = 0;
        loop {
            let u = u16::try_from(planted(emu, at + from_usize(k * 2), 2)).unwrap_or(0);
            if u == 0 || units.len() > 64 {
                break;
            }
            units.push(u);
            k += 1;
        }
        String::from_utf16_lossy(&units)
    }

    /// Reads a planted NUL-terminated byte string at `at`.
    fn planted_text_ascii(emu: &Emulator<'_>, at: u64) -> String {
        let mut bytes = Vec::new();
        let mut k = 0;
        loop {
            let b = emu.peek(at + from_usize(k)).unwrap_or(0);
            if b == 0 || bytes.len() > 64 {
                break;
            }
            bytes.push(b);
            k += 1;
        }
        String::from_utf8_lossy(&bytes).into_owned()
    }

    /// The loader's module list walks and its exports resolve.
    ///
    /// It holds the image and the system dlls, the dll entries name
    /// themselves uppercase as the loader writes them, and each
    /// synthesized image parses: `MZ`, the export directory, names the
    /// image imports, and the function each name resolves to is that API's
    /// stub.
    ///
    /// # Panics
    ///
    /// When the walk meets a zero link, the wrong name, or an export that
    /// does not resolve to a stub.
    #[test]
    fn the_module_list_walks_and_exports_resolve() {
        let p = image(Arch::X86_64);
        let emu = Emulator::new(&p, 1000).expect("x64 emulates");
        let peb = TEB_64 + PEB_AT;
        let ldr = planted(&emu, peb + LAYOUT_64.peb_ldr, 8);
        assert_ne!(ldr, 0, "the process block names a loader block");

        let head = ldr + LAYOUT_64.load_list;
        let mut entries: Vec<u64> = Vec::new();
        let mut at = planted(&emu, head, 8);
        while at != head {
            entries.push(at);
            assert!(entries.len() <= 8, "the list loops");
            at = planted(&emu, at, 8);
        }
        assert!(entries.len() >= 3, "image, ntdll and kernel32 at least");
        let kernel32 = entries[2];
        let buffer = planted(&emu, kernel32 + LAYOUT_64.base_name + 8, 8);
        assert_eq!(planted_text(&emu, buffer), "KERNEL32.DLL");

        let dll = planted(&emu, kernel32 + LAYOUT_64.dll_base, 8);
        assert_eq!(planted(&emu, dll, 2), 0x5a4d, "MZ");
        let pe = dll + planted(&emu, dll + 0x3c, 4);
        assert_eq!(planted(&emu, pe, 4), 0x4550, "PE signature");
        let export = dll + planted(&emu, pe + 0x18 + LAYOUT_64.opt_export_dir, 4);
        let names = dll + planted(&emu, export + 0x20, 4);
        let count = usize::try_from(planted(&emu, export + 0x18, 4)).unwrap_or(0);
        assert_eq!(
            count,
            KERNEL32_BASELINE.len(),
            "the one import, plus the baseline, with VirtualAlloc not repeated"
        );
        let name_rva = planted(&emu, names, 4);
        assert_eq!(planted_text_ascii(&emu, dll + name_rva), "VirtualAlloc");
        let funcs = dll + planted(&emu, export + 0x1c, 4);
        let cell = dll + planted(&emu, funcs, 4);
        let stub = emu.apis.get(&cell).expect("the export is a stub");
        assert!(stub.contains("VirtualAlloc"), "{stub}");
    }

    /// An image that imports nothing still resolves `VirtualAlloc`.
    ///
    /// The export directory used to be empty in that case, so a hash walk
    /// stored a null and the unpacker called through it. The baseline keeps
    /// `VirtualAlloc` first, which is the name this walk calls.
    ///
    /// # Panics
    ///
    /// When the run does not call the resolved API.
    #[test]
    fn an_importless_image_still_resolves_virtual_alloc() {
        let (base, entry) = (0x1_4000_0000, 0x1_4000_1000);
        let text = Section::mapped(".text", entry, 0, WALK_64.len() as u64, false, true);
        let p = Program::raw(
            WALK_64.to_vec(),
            Arch::X86_64,
            base,
            Some(entry),
            vec![text],
        );
        let mut emu = Emulator::new(&p, 1000).expect("x64 emulates");
        emu.install_imports();
        let run = emu.run(entry);
        assert!(
            emu.api_names().iter().any(|c| c.contains("VirtualAlloc")),
            "{}, {} steps, calls {:?}",
            run.stop,
            run.steps,
            emu.api_names()
        );
    }

    /// A hand-assembled 64-bit walk that resolves `VirtualAlloc` by reading
    /// the planted structures, the way a protector without an import table
    /// does, reaches the stub and is serviced.
    ///
    /// # Panics
    ///
    /// When the run does not call the resolved API.
    #[test]
    fn a_sixty_four_bit_walk_calls_the_resolved_api() {
        let p = image(Arch::X86_64);
        let mut emu = Emulator::new(&p, 1000).expect("x64 emulates");
        emu.install_imports();
        let run = emu.run(0x1_4000_1000);
        assert!(
            emu.api_names().iter().any(|c| c.contains("VirtualAlloc")),
            "{}, {} steps",
            run.stop,
            run.steps
        );
    }

    /// A hand-assembled 32-bit walk that resolves `VirtualAlloc` through
    /// `fs:[0x30]`, on the 32-bit offsets, and is serviced.
    ///
    /// # Panics
    ///
    /// When the run does not call the resolved API.
    #[test]
    fn a_thirty_two_bit_walk_calls_the_resolved_api() {
        let p = image(Arch::X86);
        let mut emu = Emulator::new(&p, 1000).expect("x86 emulates");
        emu.install_imports();
        let run = emu.run(0x401_000);
        assert!(
            emu.api_names().iter().any(|c| c.contains("VirtualAlloc")),
            "{}, {} steps",
            run.stop,
            run.steps
        );
    }
}
