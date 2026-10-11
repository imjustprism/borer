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

use std::collections::BTreeMap;
use std::fmt::Write as _;

use crate::analysis::classes::class_layout;
use crate::analysis::{Analysis, Overlay, name_of};
use crate::memory::{Kind, Value, le_word, scalar_text};
use crate::num::lo32;
use crate::program::Program;
use crate::strings::cstr_at;

/// Most bytes one read of values, an object or a snapshot takes.
pub const READ_MAX: usize = 1 << 16;

/// Most bytes a scan of a process reads before it stops and says so.
pub const SCAN_MAX: u64 = 4 << 30;

/// Bytes read from a process in one piece while scanning.
const CHUNK: usize = 1 << 20;

/// Longest string a pointer is followed into.
const STR_CAP: usize = 120;

/// Longest string read as a value.
const VALUE_STR_CAP: usize = 200;

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

impl Rebase {
    /// Finds the analysed image among a process's modules, by file name.
    ///
    /// # Arguments
    ///
    /// * `program` - The analysed image.
    /// * `modules` - The process's modules.
    ///
    /// # Returns
    ///
    /// The mapping, or `None` when no module has the image's file name.
    pub fn of(program: &Program, modules: &[Module]) -> Option<Rebase> {
        let file = program.path.file_name()?.to_string_lossy().to_lowercase();
        let module = modules.iter().find(|m| m.name.to_lowercase() == file)?;
        let end = program
            .sections
            .iter()
            .map(|s| s.va.saturating_add(s.vsize))
            .max()
            .unwrap_or(program.image_base.saturating_add(module.size))
            .max(program.image_base.saturating_add(module.size));
        Some(Rebase {
            static_base: program.image_base,
            static_end: end,
            live_base: module.base,
        })
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

    /// Says what the file has at a process address: a function, a vtable,
    /// a named global, a string literal, or a section.
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
        if let Some((_, text)) = cstr_at(program, va, 4, STR_CAP) {
            return Some(format!("\"{}\"", text.replace('"', "\\\"")));
        }
        let section = program.section_at(va).map_or("image", |s| s.name.as_str());
        Some(format!("{section}+{:#x}", va - self.static_base))
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
/// Strings are read one after another, stepping over the padding between
/// them; integers, floats and pointers are consecutive.
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
/// When the first value is not readable.
pub fn read_values(
    mem: &dyn Memory,
    va: u64,
    kind: Kind,
    count: usize,
    word: usize,
) -> Result<Vec<Value>, String> {
    let size = kind.size(word);
    let span = match kind {
        Kind::CStr | Kind::WStr => (VALUE_STR_CAP + 16) * count * size,
        _ => size * count,
    }
    .min(READ_MAX);
    let bytes = mem
        .read(va, span)
        .ok_or_else(|| format!("{va:#x} is not readable in the process"))?;
    let mut out = Vec::with_capacity(count);
    let mut at = 0usize;
    for _ in 0..count {
        if at + size > bytes.len() {
            break;
        }
        let cur = va + at as u64;
        match kind {
            Kind::CStr | Kind::WStr => {
                let unit = size;
                while at + unit <= bytes.len() && bytes[at..at + unit].iter().all(|b| *b == 0) {
                    at += unit;
                }
                let (len, text) = if kind == Kind::CStr {
                    let len = bytes[at..]
                        .iter()
                        .position(|b| !(0x20..0x7f).contains(b))
                        .unwrap_or(bytes.len() - at);
                    (
                        len,
                        String::from_utf8_lossy(&bytes[at..at + len]).into_owned(),
                    )
                } else {
                    let mut units: Vec<u16> = Vec::new();
                    let mut i = at;
                    while i + 2 <= bytes.len() {
                        let u = u16::from_le_bytes([bytes[i], bytes[i + 1]]);
                        if !(0x20..0x7f).contains(&u) {
                            break;
                        }
                        units.push(u);
                        i += 2;
                    }
                    (units.len(), String::from_utf16_lossy(&units))
                };
                if len == 0 {
                    break;
                }
                let shown: String = text.chars().take(VALUE_STR_CAP).collect();
                let prefix = if kind == Kind::WStr { "L" } else { "" };
                out.push(Value {
                    at: va + at as u64,
                    text: format!("{prefix}\"{}\" (len {len})", shown.replace('"', "\\\"")),
                    target: None,
                    size: (len + 1) * unit,
                });
                at += (len + 1) * unit;
            }
            _ => {
                let raw = le_word(&bytes[at..at + size]);
                let (text, target) = scalar_text(kind, raw);
                out.push(Value {
                    at: cur,
                    text,
                    target,
                    size,
                });
                at += size;
            }
        }
    }
    if out.is_empty() {
        return Err(format!("{va:#x} is not readable in the process"));
    }
    Ok(out)
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
        .max(word as u64);
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
        let raw = le_word(&bytes[start..start + width]);
        let value = match (f.float, bits) {
            (true, 32) => scalar_text(Kind::F32, raw).0,
            (true, 64) => scalar_text(Kind::F64, raw).0,
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
            let Some(bytes) = mem.read(at, len) else {
                // A page inside a region can stop being readable while the
                // scan runs - a live process decommits and recommits - and
                // the words past it still stand, so the chunk is stepped
                // over instead of ending the region.
                at = at.saturating_add(len as u64);
                continue;
            };
            scan.bytes += bytes.len() as u64;
            let mut off = 0usize;
            while off + word <= bytes.len() {
                let v = le_word(&bytes[off..off + word]) & mask;
                if targets.contains(&v) {
                    scan.hits.push(at + off as u64);
                    if scan.hits.len() >= limit {
                        scan.truncated = true;
                        break 'regions;
                    }
                }
                off += word;
            }
            if bytes.len() < len {
                break;
            }
            at += bytes.len() as u64;
        }
    }
    scan
}

/// Bytes of a process kept to diff against a later read.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Snapshot {
    /// First address.
    pub va: u64,
    /// The bytes as they were.
    pub bytes: Vec<u8>,
}

/// One run of bytes that changed between a snapshot and now.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Change {
    /// Offset of the run from the snapshot's first address.
    pub offset: u64,
    /// The bytes as they were.
    pub old: Vec<u8>,
    /// The bytes as they are.
    pub new: Vec<u8>,
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
        let bytes = mem
            .read(va, len.clamp(1, READ_MAX))
            .ok_or_else(|| format!("{va:#x} is not readable in the process"))?;
        Ok(Snapshot { va, bytes })
    }

    /// Reads the same bytes again and lists the runs that changed.
    ///
    /// Changed bytes a byte apart are one run; a run is cut at an
    /// eight-byte boundary so each reads as at most one word.
    ///
    /// # Arguments
    ///
    /// * `mem` - The process.
    ///
    /// # Errors
    ///
    /// When the range is no longer readable.
    pub fn diff(&self, mem: &dyn Memory) -> Result<Vec<Change>, String> {
        let now = mem
            .read(self.va, self.bytes.len())
            .ok_or_else(|| format!("{:#x} is no longer readable in the process", self.va))?;
        let n = now.len().min(self.bytes.len());
        let mut changes: Vec<Change> = Vec::new();
        let mut i = 0usize;
        while i < n {
            if self.bytes[i] == now[i] {
                i += 1;
                continue;
            }
            let start = i;
            let boundary = (start / 8 + 1) * 8;
            while i < n
                && i < boundary
                && (self.bytes[i] != now[i] || (i + 1 < n && self.bytes[i + 1] != now[i + 1]))
            {
                i += 1;
            }
            changes.push(Change {
                offset: start as u64,
                old: self.bytes[start..i].to_vec(),
                new: now[start..i].to_vec(),
            });
        }
        Ok(changes)
    }
}

/// Renders changes as rows: offset, the field name when one is known, the
/// bytes before and after, and the words they make.
///
/// # Arguments
///
/// * `snapshot` - What the changes are relative to.
/// * `changes` - The runs that changed.
/// * `names` - Field names by offset, from the object's class.
pub fn render_changes(
    snapshot: &Snapshot,
    changes: &[Change],
    names: &BTreeMap<u64, String>,
) -> String {
    let mut out = String::new();
    let _ = writeln!(
        out,
        "# {} change(s) in {} bytes at {:#x}",
        changes.len(),
        snapshot.bytes.len(),
        snapshot.va
    );
    if changes.is_empty() {
        return out;
    }
    let _ = writeln!(out, "offset  field                    was -> now");
    for c in changes {
        let field = names
            .range(..=c.offset)
            .next_back()
            .map(|(off, name)| {
                if *off == c.offset {
                    name.clone()
                } else {
                    format!("{name}+{:#x}", c.offset - off)
                }
            })
            .unwrap_or_default();
        let hex = |b: &[u8]| {
            b.iter()
                .map(|x| format!("{x:02x}"))
                .collect::<Vec<_>>()
                .join(" ")
        };
        let words = if c.old.len() <= 8 {
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

    /// A process that is one buffer at one address.
    struct Fake {
        base: u64,
        data: Vec<u8>,
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
            Vec::new()
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
        let mem = Fake { base: 0x1000, data };
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

    /// A word found in a region is an instance; the scan stops at its limit.
    #[test]
    fn words_are_found_aligned_in_data_regions() {
        let mut data = vec![0u8; 64];
        data[8..16].copy_from_slice(&0x1122_3344u64.to_le_bytes());
        data[40..48].copy_from_slice(&0x1122_3344u64.to_le_bytes());
        data[49..57].copy_from_slice(&0x1122_3344u64.to_le_bytes());
        let mem = Fake { base: 0x2000, data };
        let scan = find_words(&mem, &[0x1122_3344], 8, 10);
        assert_eq!(scan.hits, vec![0x2008, 0x2028], "unaligned copy is no hit");
        assert!(!scan.truncated);
        let scan = find_words(&mem, &[0x1122_3344], 8, 1);
        assert_eq!(scan.hits, vec![0x2008]);
        assert!(scan.truncated);
    }

    /// A snapshot diff lists the runs that changed, cut at word boundaries,
    /// and names the field a run falls in.
    #[test]
    fn snapshots_diff_by_run() {
        let mut data = vec![0u8; 32];
        data[4..8].copy_from_slice(&100u32.to_le_bytes());
        let mut mem = Fake { base: 0x3000, data };
        let snap = Snapshot::take(&mem, 0x3000, 32).unwrap();
        assert!(snap.diff(&mem).unwrap().is_empty());
        mem.data[4..8].copy_from_slice(&101u32.to_le_bytes());
        mem.data[20] = 9;
        let changes = snap.diff(&mem).unwrap();
        assert_eq!(changes.len(), 2, "{changes:?}");
        assert_eq!(changes[0].offset, 4);
        assert_eq!(le_word(&changes[0].new), 101);
        assert_eq!(changes[1].offset, 20);
        let mut names = BTreeMap::new();
        names.insert(4u64, "Gold".to_owned());
        names.insert(16u64, "Pos".to_owned());
        let text = render_changes(&snap, &changes, &names);
        assert!(text.contains("Gold"), "{text}");
        assert!(text.contains("Pos+0x4"), "{text}");
        assert!(text.contains("(100 -> 101)"), "{text}");
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
}
