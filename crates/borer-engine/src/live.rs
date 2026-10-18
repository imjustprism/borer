//! A live process beside the image.
//!
//! The static analysis knows where everything is in the file: functions,
//! vtables, singletons, strings, the fields of a class. A running process
//! has the same image at another base and heaps full of the objects the
//! image only describes. This module joins the two for an agent: an
//! address moves between the file and the process ([`Rebase`]), bytes read
//! from the process render as typed values whose pointers are named by
//! what the file has there ([`read_values`]), an object renders as the
//! named fields the analysis recovered for its class ([`object`]), the
//! instances of a class are found by the vtable the analysis knows
//! ([`instances`]), and a [`Snapshot`] of memory diffs against a later
//! read. The process itself sits behind [`Memory`], which the server
//! implements over the operating system and the tests over a buffer, so
//! nothing here opens a handle.

use std::borrow::Cow;
use std::collections::BTreeMap;
use std::fmt::Write as _;

use crate::analysis::classes::class_layout;
use crate::analysis::{Analysis, Overlay, name_of};
use crate::memory::{Kind, Value, decode, le_word, not_text, scalar_text};
use crate::num::{from_usize, lo16, lo32};
use crate::program::Program;
use crate::search::demangled_name;
use crate::strings::cstr_at;

/// Most bytes one read of values, an object or a snapshot takes.
pub const READ_MAX: usize = 1 << 16;

/// Most bytes a scan of a process reads before it stops and says so.
pub const SCAN_MAX: u64 = 4 << 30;

/// Bytes read from a process in one piece while scanning.
const CHUNK: usize = 1 << 20;

/// A page of process memory: the unit a read that fails is stepped over by.
const PAGE: u64 = 0x1000;

/// Longest string a pointer is followed into.
const STR_CAP: usize = 120;

/// A process's memory as the engine reads it.
pub trait Memory {
    /// Reads up to `len` bytes at `va`.
    ///
    /// # Returns
    ///
    /// The bytes, fewer than asked when the range runs into memory that is
    /// not readable; `None` when not even the first byte is.
    fn read(&self, va: u64, len: usize) -> Option<Vec<u8>>;

    /// The committed, readable regions, in address order.
    fn regions(&self) -> Vec<Region>;

    /// The loaded modules.
    fn modules(&self) -> Vec<Module>;
}

/// A committed, readable range of a process.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Region {
    /// First address.
    pub base: u64,
    /// Length in bytes.
    pub size: u64,
    /// Pages may be written.
    pub writable: bool,
    /// Pages may be executed.
    pub executable: bool,
    /// Pages are a mapped image (a module) rather than a heap or a mapping.
    pub image: bool,
}

/// A module loaded in a process.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Module {
    /// File name (`notepad.exe`).
    pub name: String,
    /// Full path on disk.
    pub path: String,
    /// Load address.
    pub base: u64,
    /// Size of the mapped image.
    pub size: u64,
}

/// Where the analysed image sits in the process.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Rebase {
    /// The image's base in the file.
    pub static_base: u64,
    /// One past the image's last byte in the file.
    pub static_end: u64,
    /// The module's base in the process.
    pub live_base: u64,
}

/// The header fields that tell one build of a PE image from another.
///
/// The loader leaves them in memory as the file has them; the image base,
/// which a relocated module's header no longer holds, is not one of them.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct PeStamp {
    /// COFF `Machine`: `0x14c` for x86, `0x8664` for x64.
    machine: u16,
    /// COFF `TimeDateStamp`, the link time or a reproducible build's hash.
    timestamp: u32,
    /// Optional-header `Magic`: `0x10b` for a 32-bit image, `0x20b` for 64.
    magic: u16,
    /// Optional-header `AddressOfEntryPoint`, an RVA.
    entry: u32,
    /// Optional-header `SizeOfImage`, in bytes.
    image_size: u32,
    /// Optional-header `CheckSum`.
    checksum: u32,
}

/// Bytes of a module's first page read for its headers.
const HEADER_READ: usize = 0x1000;

impl PeStamp {
    /// Reads the stamp from the start of an image, the file's or a
    /// module's in memory.
    ///
    /// # Arguments
    ///
    /// * `bytes` - The image from its first byte.
    ///
    /// # Returns
    ///
    /// The stamp, or `None` when the bytes do not start with PE headers.
    fn of(bytes: &[u8]) -> Option<PeStamp> {
        let at = |off: usize, len: usize| bytes.get(off..off.checked_add(len)?);
        let u16_at = |off: usize| at(off, 2).map(|b| lo16(le_word(b)));
        let u32_at = |off: usize| at(off, 4).map(|b| lo32(le_word(b)));
        if at(0, 2)? != b"MZ" {
            return None;
        }
        let pe = usize::try_from(u32_at(0x3c)?).ok()?;
        if at(pe, 4)? != b"PE\0\0" {
            return None;
        }
        let coff = pe.checked_add(4)?;
        let opt = coff.checked_add(20)?;
        Some(PeStamp {
            machine: u16_at(coff)?,
            timestamp: u32_at(coff.checked_add(4)?)?,
            magic: u16_at(opt)?,
            entry: u32_at(opt.checked_add(16)?)?,
            image_size: u32_at(opt.checked_add(56)?)?,
            checksum: u32_at(opt.checked_add(64)?)?,
        })
    }

    /// Says how a module's stamp differs from the file's: its bitness alone
    /// when that differs, which makes every other field moot.
    ///
    /// # Arguments
    ///
    /// * `file` - The file's stamp.
    ///
    /// # Returns
    ///
    /// The differences, comma separated; empty when there are none.
    fn differences(&self, file: &PeStamp) -> String {
        let bits = |magic: u16| if magic == 0x20b { "64-bit" } else { "32-bit" };
        if self.magic != file.magic || self.machine != file.machine {
            return format!(
                "it is {} (machine {:#x}), the file {} (machine {:#x})",
                bits(self.magic),
                self.machine,
                bits(file.magic),
                file.machine
            );
        }
        let mut out = Vec::new();
        for (what, module, file) in [
            ("timestamp", self.timestamp, file.timestamp),
            ("image size", self.image_size, file.image_size),
            ("checksum", self.checksum, file.checksum),
            ("entry RVA", self.entry, file.entry),
        ] {
            if module != file {
                out.push(format!("{what} {module:#x}, the file's {file:#x}"));
            }
        }
        out.join(", ")
    }
}

impl Rebase {
    /// Finds the analysed image among a process's modules: one with the
    /// image's file name whose headers in memory are the file's.
    ///
    /// A file name alone does not identify the image. A WOW64 process
    /// holds a 64-bit and a 32-bit `ntdll.dll`, and another build or an
    /// unrelated file can carry the same name; mapping one of those reads
    /// every static address at the wrong place and every pointer at the
    /// wrong width. So each module with the name is checked against the
    /// file's machine, bitness, link timestamp, image size, checksum and
    /// entry point, read from the module's first page in the process, and
    /// only one that agrees on all of them is the image.
    ///
    /// # Arguments
    ///
    /// * `program` - The analysed image.
    /// * `mem` - The process, with its modules.
    ///
    /// # Returns
    ///
    /// The mapping.
    ///
    /// # Errors
    ///
    /// When the file is not a PE image, no module has its file name, or
    /// none of those that do has its headers; the message says what
    /// differs in each.
    pub fn of(program: &Program, mem: &dyn Memory) -> Result<Rebase, String> {
        let file = program
            .path
            .file_name()
            .map(|n| n.to_string_lossy().into_owned())
            .unwrap_or_default();
        let want = PeStamp::of(&program.bytes).ok_or_else(|| {
            format!("{file} is not a PE image, so no module can be checked to be it")
        })?;
        let modules = mem.modules();
        let named: Vec<&Module> = modules
            .iter()
            .filter(|m| m.name.eq_ignore_ascii_case(&file))
            .collect();
        if named.is_empty() {
            return Err(format!("no module of the process is named {file}"));
        }
        let mut differs = Vec::with_capacity(named.len());
        for module in named {
            let found = mem
                .read(module.base, HEADER_READ)
                .and_then(|b| PeStamp::of(&b));
            match found {
                Some(stamp) if stamp == want => {
                    let end = program
                        .sections
                        .iter()
                        .map(|s| s.va.0.saturating_add(s.vsize))
                        .max()
                        .unwrap_or(program.image_base.saturating_add(module.size))
                        .max(program.image_base.saturating_add(module.size));
                    return Ok(Rebase {
                        static_base: program.image_base,
                        static_end: end,
                        live_base: module.base,
                    });
                }
                Some(stamp) => differs.push(format!(
                    "{} at {:#x} is another build ({})",
                    module.name,
                    module.base,
                    stamp.differences(&want)
                )),
                None => differs.push(format!(
                    "{} at {:#x} has no readable PE headers",
                    module.name, module.base
                )),
            }
        }
        Err(differs.join("; "))
    }

    /// Moves an address of the file into the process.
    ///
    /// # Arguments
    ///
    /// * `va` - An address in the file's image.
    ///
    /// # Returns
    ///
    /// The process address, or `None` when `va` is outside the image.
    pub fn to_live(&self, va: u64) -> Option<u64> {
        (self.static_base..self.static_end)
            .contains(&va)
            .then(|| va - self.static_base + self.live_base)
    }

    /// Moves an address of the process into the file.
    ///
    /// # Arguments
    ///
    /// * `va` - A process address.
    ///
    /// # Returns
    ///
    /// The file address, or `None` when `va` is outside the module.
    pub fn to_static(&self, va: u64) -> Option<u64> {
        let end = self.live_base + (self.static_end - self.static_base);
        (self.live_base..end)
            .contains(&va)
            .then(|| va - self.live_base + self.static_base)
    }

    /// Reads an address an agent gave as a process address: one in the
    /// file's image moves into the process, any other is taken as it is.
    ///
    /// # Arguments
    ///
    /// * `va` - The address as given.
    pub fn live_of(&self, va: u64) -> u64 {
        self.to_live(va).unwrap_or(va)
    }

    /// Says what the file has at a process address, as its reader would.
    ///
    /// That is a function, a vtable, a user-named global, a symbol (an
    /// export, a data record), a string literal, or the offset into its
    /// section (into the image for the headers).
    ///
    /// # Arguments
    ///
    /// * `program` - The analysed image.
    /// * `analysis` - Its analysis.
    /// * `overlay` - User names.
    /// * `live` - A process address.
    ///
    /// # Returns
    ///
    /// The description, or `None` when the address is outside the image.
    pub fn describe(
        &self,
        program: &Program,
        analysis: &Analysis,
        overlay: &Overlay,
        live: u64,
    ) -> Option<String> {
        let va = self.to_static(live)?;
        if let Some(f) = analysis.function_at(va) {
            let name = name_of(analysis, overlay, f.entry);
            return Some(if va == f.entry {
                name
            } else {
                format!("{name}+{:#x}", va - f.entry)
            });
        }
        if let Some(class) = analysis.classes.vtables.get(&va) {
            return Some(format!("vftable of {class}"));
        }
        if let Some(name) = overlay.names.get(&va) {
            return Some(name.clone());
        }
        if let Some(symbol) = analysis.symbol_at(program, va) {
            return Some(demangled_name(&symbol.name));
        }
        if let Some((_, text)) = cstr_at(program, va, 4, STR_CAP) {
            return Some(format!("\"{}\"", text.replace('"', "\\\"")));
        }
        Some(match program.section_at(va) {
            Some(s) => format!("{}+{:#x}", s.name, va - s.va.0),
            None => format!("image+{:#x}", va - self.static_base),
        })
    }
}

/// Finds a thread's block of the image's thread-local storage.
///
/// The thread's TEB holds the TLS array (at `0x58` on x64), the module's
/// `_tls_index` global says which slot of it is this module's, and the
/// slot holds the block; a class whose singleton the analysis placed at a
/// TLS offset sits at that offset in the block.
///
/// # Arguments
///
/// * `mem` - The process.
/// * `rebase` - Where the image sits.
/// * `tls_index_va` - The image's `_tls_index` global (from its headers).
/// * `teb` - The thread's environment block.
///
/// # Returns
///
/// The block's process address, or `None` when a step is not readable or
/// the slot is empty.
pub fn tls_block(mem: &dyn Memory, rebase: &Rebase, tls_index_va: u64, teb: u64) -> Option<u64> {
    let index = lo32(le_word(&mem.read(rebase.to_live(tls_index_va)?, 4)?));
    let array = le_word(&mem.read(teb.checked_add(0x58)?, 8)?);
    if array == 0 {
        return None;
    }
    let slot = array.checked_add(u64::from(index).checked_mul(8)?)?;
    let block = le_word(&mem.read(slot, 8)?);
    (block != 0).then_some(block)
}

/// Reads `count` values of a kind from a process, as [`crate::memory::read_values`]
/// reads them from the file.
///
/// Both go through one decoder ([`crate::memory::decode`]), so a value
/// reads the same from the process as from the file: a string runs to its
/// terminator whatever `count` is, the first one starts at the address
/// given, and padding is stepped over only between strings.
///
/// # Arguments
///
/// * `mem` - The process.
/// * `va` - Process address of the first value.
/// * `kind` - How to read the bytes.
/// * `count` - Most values.
/// * `word` - The pointer width in bytes.
///
/// # Errors
///
/// When not even the first value reads: its first byte is not readable,
/// fewer bytes than one value are, or the bytes there are not text for a
/// string kind; the message says which.
pub fn read_values(
    mem: &dyn Memory,
    va: u64,
    kind: Kind,
    count: usize,
    word: usize,
) -> Result<Vec<Value>, String> {
    let read = |at: u64, max: usize| mem.read(at, max.min(READ_MAX)).map(Cow::Owned);
    let out = decode(read, word == 8, va, kind, count);
    if !out.is_empty() {
        return Ok(out);
    }
    let Some(first) = mem.read(va, 1).and_then(|b| b.first().copied()) else {
        return Err(format!("{va:#x} is not readable in the process"));
    };
    Err(match kind {
        Kind::CStr | Kind::WStr => not_text(kind, first, &format!("{va:#x}")),
        _ => format!(
            "fewer than {} bytes are readable at {va:#x} in the process",
            kind.size(word)
        ),
    })
}

/// The class of the object at a process address, by its vtable.
///
/// # Arguments
///
/// * `mem` - The process.
/// * `rebase` - Where the image sits.
/// * `analysis` - The analysis, with the vtables it knows.
/// * `va` - The object's process address.
/// * `word` - The pointer width in bytes.
///
/// # Returns
///
/// The class whose vtable the first word points at, or `None`.
pub fn class_at(
    mem: &dyn Memory,
    rebase: &Rebase,
    analysis: &Analysis,
    va: u64,
    word: usize,
) -> Option<String> {
    let bytes = mem.read(va, word)?;
    if bytes.len() < word {
        return None;
    }
    let vtable = rebase.to_static(le_word(&bytes))?;
    analysis.classes.vtables.get(&vtable).cloned()
}

/// What a process word points at, for a field's note: an object of a known
/// class, something the file names, a module, or a heap.
///
/// # Arguments
///
/// * `mem` - The process.
/// * `rebase` - Where the image sits.
/// * `program` - The analysed image.
/// * `analysis` - Its analysis.
/// * `overlay` - User names.
/// * `ptr` - The word.
/// * `word` - The pointer width in bytes.
fn pointee(
    mem: &dyn Memory,
    rebase: &Rebase,
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    ptr: u64,
    word: usize,
) -> Option<String> {
    if ptr < 0x1_0000 {
        return None;
    }
    if let Some(what) = rebase.describe(program, analysis, overlay, ptr) {
        return Some(format!("-> {what}"));
    }
    if let Some(class) = class_at(mem, rebase, analysis, ptr, word) {
        return Some(format!("-> {class} object"));
    }
    if let Some(m) = mem
        .modules()
        .into_iter()
        .find(|m| (m.base..m.base + m.size).contains(&ptr))
    {
        return Some(format!("-> {}+{:#x}", m.name, ptr - m.base));
    }
    mem.regions()
        .iter()
        .any(|r| (r.base..r.base + r.size).contains(&ptr))
        .then(|| "-> heap".to_owned())
}

/// Renders the object at a process address with the fields its class has.
///
/// The class is the one given, else the one whose vtable the object's
/// first word points at. Each field of the recovered layout reads at its
/// width: a float as a float, a pointer-sized word with what it points at,
/// the rest in hex; the name is the one the class's asserts gave it, else
/// `field_0x..`, and the type is the one its uses declared.
///
/// # Arguments
///
/// * `mem` - The process.
/// * `program` - The analysed image.
/// * `analysis` - Its analysis.
/// * `overlay` - User names.
/// * `rebase` - Where the image sits.
/// * `va` - The object's process address.
/// * `class` - The class, when the agent knows it.
///
/// # Errors
///
/// When no class is known for the object, the class has no layout, or the
/// object is not readable.
pub fn object(
    mem: &dyn Memory,
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    rebase: &Rebase,
    va: u64,
    class: Option<&str>,
) -> Result<String, String> {
    let word = if program.is_64 { 8 } else { 4 };
    let found = class_at(mem, rebase, analysis, va, word);
    let class = match class {
        Some(c) => c.to_owned(),
        None => found.clone().ok_or_else(|| {
            format!(
                "{va:#x}: no class given and the first word is not a vtable the analysis knows; pass class=..."
            )
        })?,
    };
    let layout = class_layout(program, analysis, overlay, &class)
        .ok_or_else(|| format!("no function belongs to class {class}"))?;
    let size = layout
        .fields
        .iter()
        .map(|(off, f)| off + u64::from(f.widths.iter().max().copied().unwrap_or(64) / 8))
        .max()
        .unwrap_or(0)
        .max(from_usize(word));
    let size = usize::try_from(size).unwrap_or(READ_MAX).min(READ_MAX);
    let bytes = mem
        .read(va, size)
        .ok_or_else(|| format!("{va:#x} is not readable in the process"))?;
    let mut out = String::new();
    let _ = writeln!(
        out,
        "object {class} at {va:#x}: {} fields, {} of {size:#x} bytes readable",
        layout.fields.len(),
        bytes.len()
    );
    match &found {
        Some(f) if *f == class => {
            let _ = writeln!(out, "vtable:  matches {class}");
        }
        Some(f) => {
            let _ = writeln!(out, "vtable:  is {f}'s, not {class}'s");
        }
        None => {
            let _ = writeln!(out, "vtable:  none the analysis knows at +0x0");
        }
    }
    let _ = writeln!(
        out,
        "offset  name                     type              value"
    );
    for (off, f) in &layout.fields {
        let bits = f.widths.iter().max().copied().unwrap_or(64).max(8);
        let width = usize::from(bits / 8);
        let start = usize::try_from(*off).unwrap_or(usize::MAX);
        let name = layout
            .labels
            .get(off)
            .map_or_else(|| format!("field_{off:#x}"), ToString::to_string);
        let ty = f
            .types
            .iter()
            .next()
            .cloned()
            .unwrap_or_else(|| match (f.float, bits) {
                (true, 32) => "float".to_owned(),
                (true, 64) => "double".to_owned(),
                (_, b) => format!("u{b}"),
            });
        if start.saturating_add(width) > bytes.len() {
            let _ = writeln!(out, "+{off:#05x}  {name:<24} {ty:<17} (not readable)");
            continue;
        }
        let field = &bytes[start..start + width];
        let raw = le_word(field);
        let value = match (f.float, bits) {
            (true, 32) => scalar_text(Kind::F32, raw).0,
            (true, 64) => scalar_text(Kind::F64, raw).0,
            _ if width > 8 => wide_hex(field),
            _ if width == word => format!("{raw:#x}"),
            _ => format!("{raw:#x} ({raw})"),
        };
        let note = if width == word && !f.float {
            pointee(mem, rebase, program, analysis, overlay, raw, word).unwrap_or_default()
        } else {
            String::new()
        };
        let _ = writeln!(out, "+{off:#05x}  {name:<24} {ty:<17} {value} {note}");
    }
    Ok(out)
}

/// Spells a value wider than a `u64` as one hex number.
///
/// A `u128` field or a vector reads most significant byte first, as
/// `{:#x}` spells a narrower one; [`le_word`] keeps only the low eight
/// bytes.
///
/// # Arguments
///
/// * `bytes` - The value's bytes, least significant first.
fn wide_hex(bytes: &[u8]) -> String {
    let digits: String = bytes.iter().rev().map(|b| format!("{b:02x}")).collect();
    let digits = digits.trim_start_matches('0');
    format!("0x{}", if digits.is_empty() { "0" } else { digits })
}

/// What a scan of a process found.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Scan {
    /// Process addresses of the words found, in address order.
    pub hits: Vec<u64>,
    /// Bytes read.
    pub bytes: u64,
    /// Regions read.
    pub regions: usize,
    /// The scan stopped at its limit or budget before the end.
    pub truncated: bool,
}

/// Finds the objects of a class in a process by the vtable pointer their
/// first word holds.
///
/// Every vtable the analysis assigns the class is looked for, moved into
/// the process; the data regions (writable, not executable: heaps,
/// mappings, the image's data) are read in pieces and every aligned word
/// equal to one is an instance.
///
/// # Arguments
///
/// * `mem` - The process.
/// * `rebase` - Where the image sits.
/// * `analysis` - The analysis, with the vtables it knows.
/// * `class` - Qualified class name.
/// * `word` - The pointer width in bytes.
/// * `limit` - Most instances to collect.
///
/// # Errors
///
/// When the analysis knows no vtable for the class.
pub fn instances(
    mem: &dyn Memory,
    rebase: &Rebase,
    analysis: &Analysis,
    class: &str,
    word: usize,
    limit: usize,
) -> Result<Scan, String> {
    let mut vtables: Vec<u64> = analysis
        .classes
        .vtables
        .iter()
        .filter(|(_, c)| c.as_str() == class)
        .map(|(v, _)| *v)
        .collect();
    if let Some(v) = analysis.classes.by_name.get(class).and_then(|i| i.vtable) {
        vtables.push(v);
    }
    vtables.sort_unstable();
    vtables.dedup();
    let targets: Vec<u64> = vtables.iter().filter_map(|v| rebase.to_live(*v)).collect();
    if targets.is_empty() {
        return Err(format!("the analysis knows no vtable for {class}"));
    }
    Ok(find_words(mem, &targets, word, limit))
}

/// Most instances a count of a class's objects collects before it says
/// "at least".
pub const COUNT_MAX: usize = 1 << 20;

/// Renders a scan for a class's objects as a page of their addresses.
///
/// # Arguments
///
/// * `scan` - What the scan found.
/// * `class` - The class, for the header.
/// * `offset` - Addresses to skip first.
/// * `limit` - Most addresses shown.
/// * `count_only` - The header alone.
///
/// # Returns
///
/// A `# showing N of M` header (`at least M` when the scan stopped at its
/// limit or budget), then one address per row.
pub fn instances_page(
    scan: &Scan,
    class: &str,
    offset: usize,
    limit: usize,
    count_only: bool,
) -> String {
    let total = if scan.truncated {
        format!("at least {}", scan.hits.len())
    } else {
        scan.hits.len().to_string()
    };
    let read = format!(
        "{} MiB read over {} regions",
        scan.bytes >> 20,
        scan.regions
    );
    if count_only {
        return format!("# {total} instance(s) of {class}; {read}\n");
    }
    let rows: Vec<&u64> = scan.hits.iter().skip(offset).take(limit).collect();
    let mut out = format!(
        "# showing {} of {total} instance(s) of {class}; {read}\n",
        rows.len()
    );
    for h in rows {
        let _ = writeln!(out, "{h:#x}");
    }
    out
}

/// Renders a process's modules as a page of rows: base, size, file name
/// and path, with the module the loaded binary is mapped onto marked.
///
/// # Arguments
///
/// * `modules` - The modules, in the order the system lists them.
/// * `filter` - A lowercase substring of the name or path a row must
///   hold; `None` keeps every row.
/// * `offset` - Matching rows to skip first.
/// * `limit` - Most rows shown.
/// * `image` - Base of the module the loaded binary is mapped onto.
///
/// # Returns
///
/// The number of matching rows, and the page under a `# showing N of M`
/// header.
pub fn modules_page(
    modules: &[Module],
    filter: Option<&str>,
    offset: usize,
    limit: usize,
    image: Option<u64>,
) -> (usize, String) {
    let hits: Vec<&Module> = modules
        .iter()
        .filter(|m| {
            filter.is_none_or(|f| {
                m.name.to_lowercase().contains(f) || m.path.to_lowercase().contains(f)
            })
        })
        .collect();
    let rows: Vec<&&Module> = hits.iter().skip(offset).take(limit).collect();
    let mut out = format!(
        "# showing {} of {} modules\n# base size name path\n",
        rows.len(),
        hits.len()
    );
    for m in rows {
        let mark = if Some(m.base) == image {
            "  <- the loaded binary"
        } else {
            ""
        };
        let _ = writeln!(
            out,
            "{:#x} {:#x} {} {}{mark}",
            m.base, m.size, m.name, m.path
        );
    }
    (hits.len(), out)
}

/// Finds every aligned word of a process's data regions equal to one of
/// `targets`.
///
/// # Arguments
///
/// * `mem` - The process.
/// * `targets` - The words looked for.
/// * `word` - The word width in bytes.
/// * `limit` - Most hits to collect.
pub fn find_words(mem: &dyn Memory, targets: &[u64], word: usize, limit: usize) -> Scan {
    let mut scan = Scan::default();
    let mask = if word == 8 { u64::MAX } else { 0xffff_ffff };
    'regions: for region in mem.regions() {
        if !region.writable || region.executable {
            continue;
        }
        scan.regions += 1;
        let mut at = region.base;
        let end = region.base.saturating_add(region.size);
        while at < end {
            if scan.bytes >= SCAN_MAX {
                scan.truncated = true;
                break 'regions;
            }
            let len = usize::try_from(end - at).unwrap_or(CHUNK).min(CHUNK);
            let Some(bytes) = mem.read(at, len).filter(|b| !b.is_empty()) else {
                at = (at | (PAGE - 1)).saturating_add(1);
                continue;
            };
            scan.bytes += from_usize(bytes.len());
            let mut off = 0usize;
            while off + word <= bytes.len() {
                let v = le_word(&bytes[off..off + word]) & mask;
                if targets.contains(&v) {
                    scan.hits.push(at + from_usize(off));
                    if scan.hits.len() >= limit {
                        scan.truncated = true;
                        break 'regions;
                    }
                }
                off += word;
            }
            at = at.saturating_add(from_usize(bytes.len()));
        }
    }
    scan
}

/// A field of the object a watch holds: what a diff names a change by,
/// and the bytes it reads the change's value from.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Field {
    /// The name the class's asserts gave it, else `field_0x..`.
    pub name: String,
    /// Width in bytes, at least one.
    pub len: usize,
}

/// The fields of a class by offset, for a watch on one of its objects.
///
/// # Arguments
///
/// * `program` - The analysed image.
/// * `analysis` - Its analysis.
/// * `overlay` - User names.
/// * `class` - Qualified class name.
///
/// # Returns
///
/// The fields, or `None` when no function belongs to the class (the
/// analysis does not know it).
pub fn fields_of(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    class: &str,
) -> Option<BTreeMap<u64, Field>> {
    let layout = class_layout(program, analysis, overlay, class)?;
    Some(
        layout
            .fields
            .iter()
            .map(|(off, f)| {
                let bits = f.widths.iter().max().copied().unwrap_or(64).max(8);
                let name = layout
                    .labels
                    .get(off)
                    .map_or_else(|| format!("field_{off:#x}"), ToString::to_string);
                (
                    *off,
                    Field {
                        name,
                        len: usize::from(bits / 8),
                    },
                )
            })
            .collect(),
    )
}

/// Bytes of a process kept to diff against a later read.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Snapshot {
    /// First address.
    pub va: u64,
    /// Bytes the watch covers, at most [`READ_MAX`].
    pub len: usize,
    /// The bytes as they were: all `len` of them, or the readable start of
    /// the range when its end was not readable.
    pub bytes: Vec<u8>,
}

/// One value that changed between a snapshot and now.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Change {
    /// Offset of the value from the snapshot's first address.
    pub offset: u64,
    /// The value's bytes as they were.
    pub old: Vec<u8>,
    /// The value's bytes as they are.
    pub new: Vec<u8>,
    /// The bytes are a whole value - a field, or an aligned word inside the
    /// watch - so the number they make is the value's; `false` for a word
    /// the watch's ends cut.
    pub whole: bool,
}

/// What a second read of a snapshot's range found.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Diff {
    /// The values that changed, in offset order.
    pub changes: Vec<Change>,
    /// The range as read now: what a later diff compares against.
    pub now: Snapshot,
}

impl Snapshot {
    /// Reads `len` bytes at `va` to keep.
    ///
    /// # Arguments
    ///
    /// * `mem` - The process.
    /// * `va` - First address.
    /// * `len` - Bytes, capped at [`READ_MAX`].
    ///
    /// # Errors
    ///
    /// When the first byte is not readable.
    pub fn take(mem: &dyn Memory, va: u64, len: usize) -> Result<Snapshot, String> {
        let len = len.clamp(1, READ_MAX);
        let bytes = mem
            .read(va, len)
            .ok_or_else(|| format!("{va:#x} is not readable in the process"))?;
        Ok(Snapshot { va, len, bytes })
    }

    /// Reads the range again and lists the values that changed.
    ///
    /// Each change is one whole value, so its bytes make its number: the
    /// field that holds the changed bytes when the object's fields are
    /// known, else the naturally aligned word that does (aligned in the
    /// process, not from the watch's start). Bytes readable at only one of
    /// the two reads are not compared; the new snapshot says how many are
    /// readable now, and [`render_changes`] says what was lost or gained.
    ///
    /// # Arguments
    ///
    /// * `mem` - The process.
    /// * `fields` - The object's fields by offset; empty when unknown.
    /// * `word` - The process's word width in bytes.
    ///
    /// # Errors
    ///
    /// When not even the first byte is readable now.
    pub fn diff(
        &self,
        mem: &dyn Memory,
        fields: &BTreeMap<u64, Field>,
        word: usize,
    ) -> Result<Diff, String> {
        let now = mem.read(self.va, self.len).ok_or_else(|| {
            format!(
                "none of the {} bytes at {:#x} is readable now; the watch keeps the bytes it had",
                self.len, self.va
            )
        })?;
        let n = now.len().min(self.bytes.len());
        let changed = |i: usize| self.bytes[i] != now[i];
        let mut changes: Vec<Change> = Vec::new();
        let mut floor = 0usize;
        let mut i = 0usize;
        while i < n {
            if !changed(i) {
                i += 1;
                continue;
            }
            let (start, end, whole) = value_at(self.va, i, floor, n, fields, word);
            changes.push(Change {
                offset: from_usize(start),
                old: self.bytes[start..end].to_vec(),
                new: now[start..end].to_vec(),
                whole,
            });
            floor = end;
            i = end;
        }
        Ok(Diff {
            changes,
            now: Snapshot {
                va: self.va,
                len: self.len,
                bytes: now,
            },
        })
    }
}

/// The value a changed byte belongs to, as offsets from a watch's start.
///
/// # Arguments
///
/// * `va` - The watch's first address, which aligns the words.
/// * `at` - Offset of the changed byte.
/// * `floor` - Where the previous change ended; a value starts no earlier.
/// * `n` - Bytes compared; a value ends no later.
/// * `fields` - The object's fields by offset.
/// * `word` - The word width in bytes.
///
/// # Returns
///
/// `(start, end, whole)`: the field holding the byte, else the aligned word
/// (stopping short of the next field); `whole` is false when the watch's
/// ends or a neighbour cut the value.
fn value_at(
    va: u64,
    at: usize,
    floor: usize,
    n: usize,
    fields: &BTreeMap<u64, Field>,
    word: usize,
) -> (usize, usize, bool) {
    let at64 = from_usize(at);
    if let Some((off, f)) = fields.range(..=at64).next_back()
        && let Ok(start) = usize::try_from(*off)
        && start.saturating_add(f.len) > at
    {
        let (s, e) = (start.max(floor), start.saturating_add(f.len).min(n));
        return (s, e, s == start && e == start.saturating_add(f.len));
    }
    let next = fields
        .range(at64.saturating_add(1)..)
        .next()
        .and_then(|(off, _)| usize::try_from(*off).ok())
        .unwrap_or(usize::MAX);
    let skip = usize::try_from(va.wrapping_add(at64) % from_usize(word.max(1))).unwrap_or(0);
    let (start, end) = (at.wrapping_sub(skip), at + (word.max(1) - skip));
    let (s, e) = (
        if skip > at { 0 } else { start }.max(floor),
        end.min(n).min(next),
    );
    (s, e, skip <= at && s == start && e == end)
}

/// Renders a diff as rows, one changed value each.
///
/// A row holds the offset, the field name when one is known, the value's
/// bytes before and after, and the numbers a whole value makes; lines
/// before the rows say which bytes stopped or started being readable.
///
/// # Arguments
///
/// * `was` - The snapshot the diff was taken against.
/// * `diff` - What the second read found.
/// * `fields` - The object's fields by offset, from its class.
pub fn render_changes(was: &Snapshot, diff: &Diff, fields: &BTreeMap<u64, Field>) -> String {
    let (before, now) = (was.bytes.len(), diff.now.bytes.len());
    let mut out = String::new();
    let _ = writeln!(
        out,
        "# {} change(s) in {} of {} bytes at {:#x}",
        diff.changes.len(),
        before.min(now),
        was.len,
        was.va
    );
    if now < before {
        let _ = writeln!(
            out,
            "# +{now:#x}..+{before:#x}: {} byte(s) were readable and are not now",
            before - now
        );
    } else if now > before {
        let _ = writeln!(
            out,
            "# +{before:#x}..+{now:#x}: {} byte(s) are readable now that were not; compared from the next diff",
            now - before
        );
    }
    let from = now.max(before);
    if now < was.len && from < was.len {
        let _ = writeln!(
            out,
            "# +{from:#x}..+{:#x}: not readable, then or now",
            was.len
        );
    }
    if diff.changes.is_empty() {
        return out;
    }
    let _ = writeln!(out, "offset  field                    was -> now");
    for c in &diff.changes {
        let field = fields
            .range(..=c.offset)
            .next_back()
            .filter(|(off, f)| c.offset - **off < from_usize(f.len))
            .map(|(off, f)| {
                if *off == c.offset {
                    f.name.clone()
                } else {
                    format!("{}+{:#x}", f.name, c.offset - off)
                }
            })
            .unwrap_or_default();
        let hex = |b: &[u8]| {
            b.iter()
                .map(|x| format!("{x:02x}"))
                .collect::<Vec<_>>()
                .join(" ")
        };
        let words = if c.whole && c.old.len() <= 8 {
            format!(" ({} -> {})", le_word(&c.old), le_word(&c.new))
        } else {
            String::new()
        };
        let _ = writeln!(
            out,
            "+{:#05x}  {field:<24} {} -> {}{words}",
            c.offset,
            hex(&c.old),
            hex(&c.new)
        );
    }
    out
}

#[cfg(test)]
#[expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]
mod tests {
    use super::*;

    /// A process of one writable region whose listed pages do not read, as
    /// a live heap's do once decommitted mid-scan.
    struct Holey {
        /// Where the region starts.
        base: u64,
        /// Its bytes.
        data: Vec<u8>,
        /// Start addresses of the pages that do not read.
        holes: Vec<u64>,
    }

    impl Memory for Holey {
        fn read(&self, va: u64, len: usize) -> Option<Vec<u8>> {
            let end = self.base + self.data.len() as u64;
            if va < self.base || va >= end || self.holes.contains(&(va & !(PAGE - 1))) {
                return None;
            }
            let mut stop = (va + len as u64).min(end);
            for &h in &self.holes {
                if h > va && h < stop {
                    stop = h;
                }
            }
            let from = usize::try_from(va - self.base).ok()?;
            let to = usize::try_from(stop - self.base).ok()?;
            Some(self.data[from..to].to_vec())
        }

        fn regions(&self) -> Vec<Region> {
            vec![Region {
                base: self.base,
                size: self.data.len() as u64,
                writable: true,
                executable: false,
                image: false,
            }]
        }

        fn modules(&self) -> Vec<Module> {
            Vec::new()
        }
    }

    /// A page that does not read costs the scan that page only: words past
    /// a hole inside the region, and after a hole at its start, are found.
    #[test]
    fn a_scan_steps_over_only_the_pages_that_do_not_read() {
        const WORD: u64 = 0x5a5a_1234_abcd_0001;
        let base = 0x10_000;
        let mut data = vec![0u8; 4 * 0x1000];
        for off in [0x10usize, 0x2020, 0x3008] {
            data[off..off + 8].copy_from_slice(&WORD.to_le_bytes());
        }
        let middle = Holey {
            base,
            data: data.clone(),
            holes: vec![base + 0x1000],
        };
        let scan = find_words(&middle, &[WORD], 8, 16);
        assert_eq!(scan.hits, vec![base + 0x10, base + 0x2020, base + 0x3008]);
        let first = Holey {
            base,
            data,
            holes: vec![base],
        };
        let scan = find_words(&first, &[WORD], 8, 16);
        assert_eq!(scan.hits, vec![base + 0x2020, base + 0x3008]);
    }

    /// A process that is one buffer at one address, with the modules it
    /// says are loaded in it.
    struct Fake {
        base: u64,
        data: Vec<u8>,
        modules: Vec<Module>,
    }

    impl Fake {
        /// A process of one buffer and no modules.
        fn new(base: u64, data: Vec<u8>) -> Fake {
            Fake {
                base,
                data,
                modules: Vec::new(),
            }
        }
    }

    impl Memory for Fake {
        fn read(&self, va: u64, len: usize) -> Option<Vec<u8>> {
            let start = usize::try_from(va.checked_sub(self.base)?).ok()?;
            if start >= self.data.len() {
                return None;
            }
            let end = start.saturating_add(len).min(self.data.len());
            Some(self.data[start..end].to_vec())
        }

        fn regions(&self) -> Vec<Region> {
            vec![Region {
                base: self.base,
                size: self.data.len() as u64,
                writable: true,
                executable: false,
                image: false,
            }]
        }

        fn modules(&self) -> Vec<Module> {
            self.modules.clone()
        }
    }

    /// Values read from a process decode as the file's would: integers in
    /// hex and decimal, floats as floats, strings quoted and stepped over.
    #[test]
    fn values_decode_from_process_bytes() {
        let mut data = vec![0u8; 64];
        data[..4].copy_from_slice(&7u32.to_le_bytes());
        data[4..8].copy_from_slice(&1.5f32.to_bits().to_le_bytes());
        data[16..19].copy_from_slice(b"ab\0");
        data[20..23].copy_from_slice(b"cd\0");
        let mem = Fake::new(0x1000, data);
        let v = read_values(&mem, 0x1000, Kind::U32, 1, 8).unwrap();
        assert_eq!(v[0].text, "0x7");
        let v = read_values(&mem, 0x1004, Kind::F32, 1, 8).unwrap();
        assert_eq!(v[0].text, "1.5");
        let v = read_values(&mem, 0x1010, Kind::CStr, 2, 8).unwrap();
        assert_eq!(v.len(), 2, "{v:?}");
        assert_eq!(v[1].at, 0x1014);
        assert!(v[1].text.starts_with("\"cd\""), "{}", v[1].text);
        assert!(read_values(&mem, 0x5000, Kind::U8, 1, 8).is_err());
    }

    /// A process string reads as the file's reader reads one.
    ///
    /// It runs to its terminator whatever the count asked, a leading NUL is
    /// no string, and bytes that are there but are not text are refused as
    /// not text rather than as unreadable.
    #[test]
    fn process_strings_read_as_the_files_do() {
        let mut data = vec![0u8; 4096];
        data[1..1001].fill(b'A');
        data[1100] = 0x90;
        for unit in data[2000..2600].chunks_mut(2) {
            unit[0] = b'W';
        }
        let mem = Fake::new(0x1000, data);
        let v = read_values(&mem, 0x1001, Kind::CStr, 1, 8).unwrap();
        assert!(v[0].text.ends_with("...\" (len 1000)"), "{}", v[0].text);
        let v = read_values(&mem, 0x17d0, Kind::WStr, 1, 8).unwrap();
        assert!(v[0].text.ends_with("(len 300)"), "{}", v[0].text);
        let lead = read_values(&mem, 0x1000, Kind::CStr, 2, 8).unwrap_err();
        assert_eq!(
            lead,
            "no CStr at 0x1000: the byte there is 0x00, not printable text; read it as u8 or hexdump it"
        );
        let code = read_values(&mem, 0x144c, Kind::CStr, 1, 8).unwrap_err();
        assert!(code.contains("the byte there is 0x90"), "{code}");
        let gone = read_values(&mem, 0x9000, Kind::CStr, 1, 8).unwrap_err();
        assert_eq!(gone, "0x9000 is not readable in the process");
        let short = read_values(&mem, 0x1ffc, Kind::U64, 1, 8).unwrap_err();
        assert_eq!(
            short,
            "fewer than 8 bytes are readable at 0x1ffc in the process"
        );
    }

    /// A value wider than eight bytes spells all of its bytes, not the low
    /// eight.
    #[test]
    fn a_wide_value_spells_every_byte() {
        let mut v = [0u8; 16];
        v[0] = 0x01;
        v[15] = 0x80;
        assert_eq!(wide_hex(&v), "0x80000000000000000000000000000001");
        assert_eq!(wide_hex(&[0u8; 16]), "0x0");
    }

    /// Instances page with offset and limit, say "at least" when the scan
    /// stopped early, and count alone on request.
    #[test]
    fn instances_page_and_count() {
        let scan = Scan {
            hits: vec![0x10, 0x20, 0x30],
            bytes: 3 << 20,
            regions: 2,
            truncated: true,
        };
        assert_eq!(
            instances_page(&scan, "Foo", 1, 1, false),
            "# showing 1 of at least 3 instance(s) of Foo; 3 MiB read over 2 regions\n0x20\n"
        );
        assert_eq!(
            instances_page(&scan, "Foo", 0, 10, true),
            "# at least 3 instance(s) of Foo; 3 MiB read over 2 regions\n"
        );
    }

    /// Modules page by filter, offset and limit, the loaded binary marked.
    #[test]
    fn modules_page_and_filter() {
        let module = |name: &str, base| Module {
            name: name.to_owned(),
            path: format!("C:\\w\\{name}"),
            base,
            size: 0x1000,
        };
        let all = [
            module("a.exe", 0x1000),
            module("ntdll.dll", 0x2000),
            module("kernel32.dll", 0x3000),
        ];
        let (n, page) = modules_page(&all, Some("dll"), 1, 5, Some(0x3000));
        assert_eq!(n, 2);
        assert_eq!(
            page,
            "# showing 1 of 2 modules\n# base size name path\n0x3000 0x1000 kernel32.dll C:\\w\\kernel32.dll  <- the loaded binary\n"
        );
    }

    /// A word found in a region is an instance; the scan stops at its limit.
    #[test]
    fn words_are_found_aligned_in_data_regions() {
        let mut data = vec![0u8; 64];
        data[8..16].copy_from_slice(&0x1122_3344u64.to_le_bytes());
        data[40..48].copy_from_slice(&0x1122_3344u64.to_le_bytes());
        data[49..57].copy_from_slice(&0x1122_3344u64.to_le_bytes());
        let mem = Fake::new(0x2000, data);
        let scan = find_words(&mem, &[0x1122_3344], 8, 10);
        assert_eq!(scan.hits, vec![0x2008, 0x2028], "unaligned copy is no hit");
        assert!(!scan.truncated);
        let scan = find_words(&mem, &[0x1122_3344], 8, 1);
        assert_eq!(scan.hits, vec![0x2008]);
        assert!(scan.truncated);
    }

    /// A snapshot diff lists each changed value whole: the field that holds
    /// the changed bytes, named, with the number the whole field makes.
    #[test]
    fn snapshots_diff_by_field() {
        let mut data = vec![0u8; 32];
        data[4..8].copy_from_slice(&100u32.to_le_bytes());
        let mut mem = Fake::new(0x3000, data);
        let mut fields = BTreeMap::new();
        for (off, name, len) in [(4u64, "Gold", 4), (16, "Pos", 8)] {
            fields.insert(
                off,
                Field {
                    name: name.to_owned(),
                    len,
                },
            );
        }
        let snap = Snapshot::take(&mem, 0x3000, 32).unwrap();
        assert!(snap.diff(&mem, &fields, 8).unwrap().changes.is_empty());
        mem.data[4..8].copy_from_slice(&101u32.to_le_bytes());
        mem.data[20] = 9;
        let diff = snap.diff(&mem, &fields, 8).unwrap();
        assert_eq!(diff.changes.len(), 2, "{diff:?}");
        assert_eq!(diff.changes[0].offset, 4);
        assert_eq!(le_word(&diff.changes[0].new), 101);
        assert_eq!(diff.changes[1].offset, 16);
        assert_eq!(diff.changes[1].new.len(), 8);
        let text = render_changes(&snap, &diff, &fields);
        assert!(text.contains("+0x004  Gold"), "{text}");
        assert!(text.contains("(100 -> 101)"), "{text}");
        assert!(text.contains("+0x010  Pos"), "{text}");
        assert!(text.contains("(0 -> 38654705664)"), "{text}");
    }

    /// Without fields a change is the aligned word holding it.
    ///
    /// The word is aligned in the process, not from an unaligned watch's
    /// start; a word the watch's start cuts shows its bytes but no number.
    #[test]
    fn snapshots_diff_by_aligned_word() {
        let mem = Fake::new(0x3000, vec![0u8; 32]);
        let snap = Snapshot::take(&mem, 0x3003, 24).unwrap();
        let mut mem = mem;
        mem.data[0x5] = 1;
        mem.data[0x12] = 2;
        mem.data[0x15] = 3;
        let none = BTreeMap::new();
        let diff = snap.diff(&mem, &none, 8).unwrap();
        assert_eq!(diff.changes.len(), 2, "{diff:?}");
        assert_eq!((diff.changes[0].offset, diff.changes[0].new.len()), (0, 5));
        assert!(!diff.changes[0].whole);
        assert_eq!(
            (diff.changes[1].offset, diff.changes[1].new.len()),
            (0xd, 8)
        );
        assert!(diff.changes[1].whole);
        let text = render_changes(&snap, &diff, &none);
        assert!(
            text.contains(" 00 00 00 00 00 -> 00 00 01 00 00\n"),
            "{text}"
        );
        assert!(
            text.contains("-> 00 00 02 00 00 03 00 00 (0 -> 3298535014400)"),
            "{text}"
        );
    }

    /// A range that stops being readable says so rather than shrinking the
    /// watch silently, and one that becomes readable again says that too.
    #[test]
    fn a_diff_says_what_stopped_being_readable() {
        let mut mem = Fake::new(0x3000, vec![0u8; 32]);
        let none = BTreeMap::new();
        let snap = Snapshot::take(&mem, 0x3000, 64).unwrap();
        assert_eq!((snap.len, snap.bytes.len()), (64, 32));
        mem.data.truncate(20);
        let diff = snap.diff(&mem, &none, 8).unwrap();
        let text = render_changes(&snap, &diff, &none);
        assert!(
            text.starts_with("# 0 change(s) in 20 of 64 bytes at 0x3000\n# +0x14..+0x20: 12 byte(s) were readable and are not now\n# +0x20..+0x40: not readable, then or now\n"),
            "{text}"
        );
        assert_eq!(diff.now.len, 64, "the watch keeps its length");
        mem.data.resize(32, 0);
        let again = diff.now.diff(&mem, &none, 8).unwrap();
        let text = render_changes(&diff.now, &again, &none);
        assert!(
            text.contains("# +0x14..+0x20: 12 byte(s) are readable now that were not"),
            "{text}"
        );
        mem.data.clear();
        let gone = again.now.diff(&mem, &none, 8).unwrap_err();
        assert!(
            gone.starts_with("none of the 64 bytes at 0x3000 is readable now"),
            "{gone}"
        );
    }

    /// Addresses move between the file and the process and back.
    #[test]
    fn addresses_rebase_both_ways() {
        let r = Rebase {
            static_base: 0x1_4000_0000,
            static_end: 0x1_4010_0000,
            live_base: 0x7ff6_0000_0000,
        };
        assert_eq!(r.to_live(0x1_4000_1234), Some(0x7ff6_0000_1234));
        assert_eq!(r.to_static(0x7ff6_0000_1234), Some(0x1_4000_1234));
        assert_eq!(r.to_live(0x1_4010_0000), None);
        assert_eq!(r.live_of(0x7ff6_0000_1234), 0x7ff6_0000_1234);
        assert_eq!(r.live_of(0x1_4000_1234), 0x7ff6_0000_1234);
    }

    /// A pointer into the image is named as the file's reader names it.
    ///
    /// The symbol at it names it, else its offset into its section, never
    /// its offset from the image base under a section's name.
    #[test]
    fn a_pointer_note_names_symbols_and_section_offsets() {
        use crate::program::{Arch, Section, Symbol, SymbolKind};
        let text = Section::mapped(".text", 0x1000, 0, 0x100, false, true);
        let data = Section::mapped(".data", 0x2000, 0x100, 0x100, true, false);
        let mut program = Program::raw(
            vec![0xc3; 0x200],
            Arch::X86_64,
            0,
            Some(0x1000),
            vec![text, data],
        );
        program.symbols.push(Symbol {
            name: "g_state".to_owned(),
            addr: 0x2040,
            kind: SymbolKind::Data,
        });
        let analysis = Analysis::compute(&program);
        let overlay = Overlay::default();
        let r = Rebase {
            static_base: 0,
            static_end: 0x2100,
            live_base: 0x7000_0000,
        };
        let note = |live| r.describe(&program, &analysis, &overlay, live);
        assert_eq!(note(0x7000_2040).as_deref(), Some("g_state"));
        assert_eq!(note(0x7000_2010).as_deref(), Some(".data+0x10"));
        assert_eq!(note(0x7000_0040).as_deref(), Some("image+0x40"));
    }

    /// PE headers for a test image: `MZ`, the PE signature at `0x80`, the
    /// COFF machine and timestamp, and the optional header's magic and
    /// image size.
    fn headers(machine: u16, magic: u16, timestamp: u32, image_size: u32) -> Vec<u8> {
        let mut b = vec![0u8; 0x200];
        b[..2].copy_from_slice(b"MZ");
        b[0x3c..0x40].copy_from_slice(&0x80u32.to_le_bytes());
        b[0x80..0x84].copy_from_slice(b"PE\0\0");
        b[0x84..0x86].copy_from_slice(&machine.to_le_bytes());
        b[0x88..0x8c].copy_from_slice(&timestamp.to_le_bytes());
        b[0x98..0x9a].copy_from_slice(&magic.to_le_bytes());
        b[0xd0..0xd4].copy_from_slice(&image_size.to_le_bytes());
        b
    }

    /// The image is the module whose headers in memory are the file's.
    ///
    /// Of three modules with its name, the 64-bit one and another build are
    /// passed over, and a file no module agrees with is refused with what
    /// differs in each.
    #[test]
    fn the_image_is_matched_by_its_headers_not_its_name() {
        let file = headers(0x14c, 0x10b, 0x1234, 0x5000);
        let mut program = Program::raw(
            file.clone(),
            crate::program::Arch::X86,
            0x40_0000,
            None,
            Vec::new(),
        );
        program.path = std::path::PathBuf::from("C:/w/ntdll.dll");
        let mut data = vec![0u8; 0x3000];
        data[..0x200].copy_from_slice(&headers(0x8664, 0x20b, 0x9999, 0x8000));
        data[0x1000..0x1200].copy_from_slice(&headers(0x14c, 0x10b, 0x7777, 0x5000));
        data[0x2000..0x2200].copy_from_slice(&file);
        let module = |base, size| Module {
            name: "NTDLL.DLL".to_owned(),
            path: String::new(),
            base,
            size,
        };
        let mut mem = Fake {
            base: 0x10_0000,
            data,
            modules: vec![
                module(0x10_0000, 0x8000),
                module(0x10_1000, 0x5000),
                module(0x10_2000, 0x5000),
            ],
        };
        let r = Rebase::of(&program, &mem).unwrap();
        assert_eq!(r.live_base, 0x10_2000);
        assert_eq!(r.to_live(0x40_1000), Some(0x10_3000));
        mem.modules.pop();
        let refused = Rebase::of(&program, &mem).unwrap_err();
        assert!(
            refused.contains("NTDLL.DLL at 0x100000 is another build (it is 64-bit (machine 0x8664), the file 32-bit (machine 0x14c));"),
            "{refused}"
        );
        assert!(
            refused.contains(
                "NTDLL.DLL at 0x101000 is another build (timestamp 0x7777, the file's 0x1234)"
            ),
            "{refused}"
        );
        program.path = std::path::PathBuf::from("other.dll");
        assert_eq!(
            Rebase::of(&program, &mem).unwrap_err(),
            "no module of the process is named other.dll"
        );
    }
}
