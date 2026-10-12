//! Binary loading: parses PE, ELF and Mach-O (and detects archives) into a
//! normalized, immutable [`Program`] that every analysis query reads from.
//!
//! Design rule: a `Program` holds only facts derived from the file. User
//! annotations (renames, comments, types) live in a separate overlay, so
//! analysis stays a pure function of the input.

use std::path::{Path, PathBuf};

use std::collections::{BTreeMap, BTreeSet};

use anyhow::{Context, anyhow};

use crate::entropy::shannon;
use crate::headers::Headers;
use crate::isa::Isa;

/// Container format of the loaded file.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinaryFormat {
    /// Windows Portable Executable (EXE, DLL, SYS).
    Pe,
    /// Executable and Linkable Format (Linux, BSD).
    Elf,
    /// Apple Mach-O: a thin image, or the x86-64 slice of a fat file.
    MachO,
    /// A static library archive; detected only.
    Archive,
    /// Not recognized by the loader; no sections, no symbols.
    Raw,
}

impl BinaryFormat {
    /// Returns the display name used in summaries (`PE`, `ELF`, `Mach-O`, ...).
    pub fn name(self) -> &'static str {
        match self {
            BinaryFormat::Pe => "PE",
            BinaryFormat::Elf => "ELF",
            BinaryFormat::MachO => "Mach-O",
            BinaryFormat::Archive => "archive",
            BinaryFormat::Raw => "raw",
        }
    }
}

/// Instruction-set architectures the engine recognizes.
///
/// What the engine does with each one's code is [`Arch::supports`]; an
/// architecture it does not analyze is still identified from the headers
/// so the summary can say what a file is.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Arch {
    /// 32-bit x86.
    X86,
    /// 64-bit x86 (AMD64).
    X86_64,
    /// 64-bit ARM (AArch64).
    Arm64,
    /// Anything else, or a header the loader could not read.
    Unknown,
}

impl Arch {
    /// Returns the display name used in summaries (`x86`, `x86-64`, `arm64`, `unknown`).
    pub fn name(self) -> &'static str {
        match self {
            Arch::X86 => "x86",
            Arch::X86_64 => "x86-64",
            Arch::Arm64 => "arm64",
            Arch::Unknown => "unknown",
        }
    }

    /// Returns the decoder bitness for architectures the disassembler supports.
    ///
    /// # Returns
    ///
    /// `32` or `64` for x86 variants, `None` for everything else.
    pub fn bitness(self) -> Option<u32> {
        match self {
            Arch::X86 => Some(32),
            Arch::X86_64 => Some(64),
            _ => None,
        }
    }

    /// Returns the instruction set this architecture's code is written in.
    ///
    /// # Returns
    ///
    /// The instruction set, or `None` for [`Arch::Unknown`].
    pub fn isa(self) -> Option<Isa> {
        match self {
            Arch::X86 => Some(Isa::X86 { bits: 32 }),
            Arch::X86_64 => Some(Isa::X86 { bits: 64 }),
            Arch::Arm64 => Some(Isa::A64),
            Arch::Unknown => None,
        }
    }

    /// Tells whether the engine does `feature` with this architecture's code.
    ///
    /// The one table of what each instruction set supports: a stage lands
    /// for an instruction set by flipping its arm here, and every gate
    /// ([`Program::refuses`]) follows.
    ///
    /// # Arguments
    ///
    /// * `feature` - What a tool asks of the code.
    pub fn supports(self, feature: Feature) -> bool {
        match self.isa() {
            Some(Isa::X86 { .. }) => true,
            Some(Isa::A64) => match feature {
                Feature::Disasm | Feature::Discover | Feature::Emulate | Feature::Decompile => {
                    false
                }
            },
            None => false,
        }
    }
}

/// What a code tool asks the engine to do with a program's instructions.
///
/// Support arrives one instruction set and one stage at a time, so a tool
/// names the stage it needs ([`Program::refuses`]) instead of reading
/// support off [`Arch::bitness`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Feature {
    /// Decoding instructions to text: a linear listing at an address.
    Disasm,
    /// Function discovery, and every answer read from the analysis it
    /// builds (functions, references, the call graph).
    Discover,
    /// Running code in the emulator.
    Emulate,
    /// Lifting functions to pseudo-C.
    Decompile,
}

/// One mapped section of the image.
#[derive(Debug, Clone)]
pub struct Section {
    /// Section name as stored in the file (`.text`, `.rdata`, ...).
    pub name: String,
    /// Virtual address of the first byte when the image is loaded.
    pub va: u64,
    /// Size in memory, in bytes (may exceed `file_size`: zero-filled tail).
    pub vsize: u64,
    /// Offset of the section's bytes in the file.
    pub file_off: u64,
    /// Number of bytes backed by the file (`0` for `.bss`-style sections).
    pub file_size: u64,
    /// Section is readable when mapped.
    pub readable: bool,
    /// Section is writable when mapped.
    pub writable: bool,
    /// Section is executable when mapped.
    pub executable: bool,
}

impl Section {
    /// A section backed by `size` bytes of the file at `file_off`, mapped
    /// at `va` with the same size.
    ///
    /// # Arguments
    ///
    /// * `name` - The section's name.
    /// * `va` - Where the first byte maps.
    /// * `file_off` - Where its bytes sit in the file.
    /// * `size` - Bytes, in the file and in memory alike.
    /// * `writable` - Mapped writable.
    /// * `executable` - Mapped executable.
    #[must_use]
    pub fn mapped(
        name: &str,
        va: u64,
        file_off: u64,
        size: u64,
        writable: bool,
        executable: bool,
    ) -> Section {
        Section {
            name: name.to_owned(),
            va,
            vsize: size,
            file_off,
            file_size: size,
            readable: true,
            writable,
            executable,
        }
    }

    /// Returns the permissions as a three-character `rwx` string (`-` for absent bits).
    pub fn perms(&self) -> String {
        format!(
            "{}{}{}",
            if self.readable { "r" } else { "-" },
            if self.writable { "w" } else { "-" },
            if self.executable { "x" } else { "-" }
        )
    }
}

/// Where a symbol comes from.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SymbolKind {
    /// Resolved from another module at load time.
    Import,
    /// Provided by this module for others.
    Export,
    /// Named by the static symbol table (ELF `.symtab`) without being exported.
    Local,
    /// Exported by name but forwarded to another module (`NTDLL.RtlX`): the
    /// address holds that text, not code, so it seeds no function.
    Forwarder,
    /// Named data at an address (an applied PDB's data records): a static,
    /// a global or a string constant. Names the address the way an
    /// overlay-named global is named, and seeds no function - what it marks
    /// is data, and the data sections are not executable.
    Data,
}

impl SymbolKind {
    /// Returns the lowercase name used in tool output (`import`, `export`,
    /// `local`, `forward` or `data`).
    pub fn name(self) -> &'static str {
        match self {
            SymbolKind::Import => "import",
            SymbolKind::Export => "export",
            SymbolKind::Local => "local",
            SymbolKind::Forwarder => "forward",
            SymbolKind::Data => "data",
        }
    }
}

/// One named address from the file's symbol tables.
#[derive(Debug, Clone)]
pub struct Symbol {
    /// Symbol name; PE imports are `DLL!name`.
    pub name: String,
    /// Virtual address: the IAT or GOT slot of an import, the entry of an
    /// export or local function; `0` for an import without a known slot.
    pub addr: u64,
    /// Import, export or local.
    pub kind: SymbolKind,
}

/// An immutable, fully parsed binary.
#[derive(Debug, Clone)]
pub struct Program {
    /// Path the file was loaded from (informational; nothing re-reads it).
    pub path: PathBuf,
    /// The whole file.
    pub bytes: Vec<u8>,
    /// Container format.
    pub format: BinaryFormat,
    /// Instruction-set architecture.
    pub arch: Arch,
    /// Pointer size is 8 bytes.
    pub is_64: bool,
    /// Virtual address of the entry point, if any.
    pub entry: Option<u64>,
    /// Preferred load base (PE); `0` for formats whose addresses are absolute (ELF).
    pub image_base: u64,
    /// Mapped sections in file order.
    pub sections: Vec<Section>,
    /// Imports, exports, local and data symbols in file order.
    pub symbols: Vec<Symbol>,
    /// Function extents the file declares, `(start, end)` virtual addresses,
    /// sorted: x64 exception-table entries (chained chunks excluded), sized
    /// `STT_FUNC` symbols, and the extents an applied PDB's procedures
    /// state where an executable section holds them whole. Discovery seeds
    /// from them and treats a jump into one as a tail call.
    pub function_ranges: Vec<(u64, u64)>,
    /// Header-level facts (link time, mitigations, debug id, libraries, ...).
    pub headers: Headers,
    /// Functions the debug information names, by address.
    ///
    /// Facts the compiler recorded: the name, and often the parameter names,
    /// of every function it saw. Empty when the program carries no readable
    /// debug information, which is the common case for a shipped binary.
    pub debug_functions: Vec<crate::dwarf::Subprogram>,
    /// The struct layouts and enum constants the debug information states,
    /// by type name, in the shape [`crate::analysis::utypes::UserType`]
    /// spells: a fact the file states, not an annotation, so it lives here
    /// and not in the overlay - nothing applies it until an agent chooses
    /// to, by stating the same entry as a user type.
    pub debug_types: BTreeMap<String, crate::analysis::utypes::UserType>,
    /// What applying the PDB the debug record named did: how many of its
    /// function symbols joined [`Program::symbols`], or why a found PDB was
    /// skipped. `None` when the image names no PDB or none was on disk to
    /// read, which changes nothing.
    pub pdb: Option<crate::pdb::Outcome>,
    /// The `CodeView` record itself when the image names a PDB, held for a
    /// caller that wants the name, GUID and age after the load: a symbol
    /// server fetch asks for exactly those when the companion is missing.
    pub pdb_record: Option<crate::pdb::Record>,
    /// The companion PDB that applied, as the resolved path the record
    /// matched and the record itself, for the lazy source-line walk
    /// ([`crate::pdb::sources`]); `None` when no PDB applied. Held instead
    /// of the PDB's bytes, which a full build's companion would double the
    /// program's memory with for rows no load answers from.
    pub pdb_source: Option<(PathBuf, crate::pdb::Record)>,
    /// The section table was unusable and a flat file mapping was synthesized.
    pub flat_fallback: bool,
}

/// The container a file's first bytes name, for a parse that fails.
///
/// # Arguments
///
/// * `bytes` - The file.
///
/// # Returns
///
/// `a PE`, `an ELF image`, `a Mach-O image`, `a fat Mach-O (or a Java
/// class file)` or `an archive`, or `None` when the magic is none of them.
fn magic_name(bytes: &[u8]) -> Option<&'static str> {
    // SPEC: the Mach-O magics in either byte order, the fat magic (which a
    // Java class file shares), and the `ar` signature.
    let word = bytes.first_chunk::<4>().map(|b| u32::from_be_bytes(*b));
    match word {
        _ if bytes.first_chunk::<2>() == Some(b"MZ") => Some("a PE"),
        Some(0x7f45_4c46) => Some("an ELF image"),
        Some(0xfeed_face | 0xfeed_facf | 0xcefa_edfe | 0xcffa_edfe) => Some("a Mach-O image"),
        Some(0xcafe_babe) => Some("a fat Mach-O (or a Java class file)"),
        _ if bytes.starts_with(b"!<arch>\n") => Some("an archive"),
        _ => None,
    }
}

/// Parses a byte image into a goblin object, retrying a damaged one leniently.
///
/// A protector rewrites the section table and data directories so a strict
/// parse of the exception, import or relocation directory can fail on a file
/// that still loads and runs, and one bad byte in a header the loader never
/// reads (a section name that is not UTF-8, a symbol table offset past the
/// end) failed the whole file. When the strict parse fails, an `MZ` file
/// is parsed again in permissive mode, an ELF image in permissive mode and
/// a Mach-O image lossily: each keeps what it can read and drops what it
/// cannot, so the code is available to analyze even when the headers lie,
/// and what the strict parse said is kept for the summary to show.
///
/// # Arguments
///
/// * `bytes` - The file image.
/// * `parse_imports` - Whether a PE's import directory is read; `false`
///   when [`implausible_imports`] refused it.
///
/// # Returns
///
/// The object, with what the strict parse said when only the lenient one
/// read the file. A file whose magic names no format is
/// [`goblin::Object::Unknown`], however short.
///
/// # Errors
///
/// When a file whose magic names a format fails both parses, with what
/// each said.
fn parse_object(
    bytes: &[u8],
    parse_imports: bool,
) -> anyhow::Result<(goblin::Object<'_>, Option<String>)> {
    use goblin::pe::options::{ParseMode, ParseOptions};
    if bytes.first_chunk::<2>() == Some(b"MZ") {
        let strict = ParseOptions::default().with_parse_imports(parse_imports);
        return match caught(|| goblin::pe::PE::parse_with_opts(bytes, &strict))? {
            Ok(pe) => Ok((goblin::Object::PE(pe), None)),
            Err(strict_err) => {
                let permissive = strict.with_parse_mode(ParseMode::Permissive);
                let pe = caught(|| goblin::pe::PE::parse_with_opts(bytes, &permissive))?
                    .map_err(|permissive| anyhow!("{strict_err}; permissive: {permissive}"))?;
                Ok((goblin::Object::PE(pe), Some(strict_err.to_string())))
            }
        };
    }
    let strict_err = match caught(|| goblin::Object::parse(bytes))? {
        Ok(obj) => return Ok((obj, None)),
        Err(e) => e,
    };
    let lenient = match bytes.first_chunk::<4>().map(|b| u32::from_be_bytes(*b)) {
        Some(0x7f45_4c46) => caught(|| {
            goblin::elf::Elf::parse_with_opts(bytes, &goblin::options::ParseOptions::permissive())
        })?
        .map(goblin::Object::Elf),
        Some(0xfeed_face | 0xfeed_facf | 0xcefa_edfe | 0xcffa_edfe | 0xcafe_babe) => {
            caught(|| goblin::mach::Mach::parse_lossy(bytes))?.map(goblin::Object::Mach)
        }
        _ if magic_name(bytes).is_none() => return Ok((goblin::Object::Unknown(0), None)),
        _ => return Err(anyhow!("{strict_err}")),
    };
    lenient
        .map(|obj| (obj, Some(strict_err.to_string())))
        .map_err(|lenient| anyhow!("{strict_err}; lenient: {lenient}"))
}

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
fn loosen_pe(bytes: &mut [u8]) -> (Vec<Patch>, Vec<String>) {
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
    let count_at = match le_u16(bytes, opt) {
        Some(0x10b) => opt + 92,
        Some(0x20b) => opt + 108,
        _ => return (patches, notes),
    };
    if let Some(count) = le_u32(bytes, count_at).filter(|&c| c > DIRECTORIES_MAX)
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
struct Patch {
    /// File offset of the first byte.
    at: usize,
    /// What the bytes held.
    saved: [u8; 4],
}

impl Patch {
    /// Saves four bytes and zeroes them.
    ///
    /// # Arguments
    ///
    /// * `at` - The bytes' file offset.
    /// * `slot` - The four bytes, zeroed in place.
    fn zeroed(at: usize, slot: &mut [u8]) -> Patch {
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
fn restore(bytes: &mut [u8], patches: &[Patch]) {
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
const EXPORTS_MAX: u32 = 1 << 16;

/// Bytes of one data directory entry: a virtual address and a size.
const DIRECTORY_ENTRY: usize = 8;

/// Bytes of one section table row.
const SECTION_ROW: usize = 40;

/// Largest section size a sane image carries (1 GiB), in memory or in the file.
const SANE_MAX: u64 = 1 << 30;

/// Most sections the summary's table and [`Program::section_list`] name.
///
/// A damaged count of 65,535 rows made one `binary_info` answer 4.6 MB.
const SECTIONS_SHOWN: usize = 64;

/// What fitting a section table to its file left out or cut short.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub(crate) struct Fit {
    /// Rows dropped because the file cannot hold what they state.
    pub dropped: usize,
    /// The furthest file offset a kept row states, when that is past the end
    /// of the file: the file is truncated, and the row keeps what it holds.
    pub cut: Option<u64>,
}

impl Fit {
    /// Adds what fitting another table found.
    ///
    /// # Arguments
    ///
    /// * `other` - The other table's fit.
    fn add(&mut self, other: Fit) {
        self.dropped += other.dropped;
        if let Some(end) = other.cut {
            self.note_cut(end);
        }
    }

    /// Records a row that states file bytes up to `end`, past the end of the file.
    ///
    /// # Arguments
    ///
    /// * `end` - The file offset the row's bytes end at.
    fn note_cut(&mut self, end: u64) {
        self.cut = Some(self.cut.map_or(end, |c| c.max(end)));
    }
}

/// Fits a section table to the file that states it.
///
/// A section's sizes are numbers in a header, and a damaged or hostile one
/// states sizes the file has never held: an ELF `.data` of 2^55 bytes made
/// every walk over a section's file bytes run for hours, reading nothing.
/// A row is dropped when it is not a section any image could hold: its
/// bytes start past the end of the file, a size passes [`SANE_MAX`], or its
/// end passes the top of the address space. A row that starts inside the
/// file and runs past its end is the section a truncated file cuts, and
/// keeps the bytes the file holds. Afterwards every kept row's file extent
/// lies inside the file, so a walk over it is bounded by the file's length.
///
/// # Arguments
///
/// * `sections` - The rows as the format states them, fitted in place.
/// * `file_len` - The file's length in bytes.
///
/// # Returns
///
/// How many rows were dropped and how far the furthest cut one reached.
pub(crate) fn fit_sections(sections: &mut Vec<Section>, file_len: u64) -> Fit {
    let mut fit = Fit::default();
    sections.retain_mut(|s| {
        let sane = s.vsize <= SANE_MAX
            && s.file_size <= SANE_MAX
            && (s.file_size == 0 || s.file_off < file_len)
            && s.va.checked_add(s.vsize.max(s.file_size)).is_some();
        if !sane {
            fit.dropped += 1;
            return false;
        }
        let end = s.file_off.saturating_add(s.file_size);
        if end > file_len {
            fit.note_cut(end);
            s.file_size = file_len - s.file_off;
        }
        true
    });
    fit
}

/// Reads a little-endian `u16` at a file offset.
///
/// # Arguments
///
/// * `bytes` - The file.
/// * `at` - The offset.
fn le_u16(bytes: &[u8], at: usize) -> Option<u16> {
    let b = bytes.get(at..at.checked_add(2)?)?;
    Some(u16::from_le_bytes(b.try_into().ok()?))
}

/// Reads a little-endian `u32` at a file offset.
///
/// # Arguments
///
/// * `bytes` - The file.
/// * `at` - The offset.
pub(crate) fn le_u32(bytes: &[u8], at: usize) -> Option<u32> {
    let b = bytes.get(at..at.checked_add(4)?)?;
    Some(u32::from_le_bytes(b.try_into().ok()?))
}

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
    let pe = usize::try_from(le_u32(bytes, 0x3c)?).ok()?;
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
    // SPEC: the directory count sits 92 bytes into a PE32 optional header
    // and 108 into a PE32+ one; the entries follow it.
    let (count_at, plus) = match le_u16(bytes, opt)? {
        0x10b => (opt + 92, false),
        0x20b => (opt + 108, true),
        _ => return None,
    };
    if usize::try_from(le_u32(bytes, count_at)?).ok()? <= index {
        return None;
    }
    Some((count_at + 4 + index * DIRECTORY_ENTRY, plus))
}

/// A row of the section table as the file states it, before any sanity check.
#[derive(Debug, Clone, Copy)]
struct RawSection {
    /// Where the section maps, relative to the image base.
    rva: u64,
    /// Where its bytes sit in the file.
    file_off: u64,
    /// How many of its bytes the file holds.
    file_size: u64,
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
fn raw_sections(bytes: &[u8]) -> Option<Vec<RawSection>> {
    let pe = pe_signature(bytes)?;
    let count = usize::from(le_u16(bytes, pe + 6)?);
    let table = pe + 24 + usize::from(le_u16(bytes, pe + 20)?);
    let rows = count.min(bytes.len().saturating_sub(table) / SECTION_ROW);
    let file_len = crate::num::from_usize(bytes.len());
    (0..rows)
        .map(|i| {
            let row = table + i * SECTION_ROW;
            let file_off = u64::from(le_u32(bytes, row + 20)?);
            let file_size =
                u64::from(le_u32(bytes, row + 16)?).min(file_len.saturating_sub(file_off));
            Some(RawSection {
                rva: u64::from(le_u32(bytes, row + 12)?),
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
fn sound_section_table(
    bytes: &[u8],
    rows: &[goblin::pe::section_table::SectionTable],
    size_of_headers: u32,
) -> bool {
    let Some(pe) = pe_signature(bytes) else {
        return false;
    };
    let Some(optional) = le_u16(bytes, pe + 20) else {
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
fn implausible_imports(bytes: &[u8]) -> Option<u64> {
    /// Bytes of one import descriptor.
    const DESCRIPTOR: usize = 20;
    let (entry, plus) = directory_entry(bytes, 1)?;
    let word = if plus { 8 } else { 4 };
    let sections = raw_sections(bytes)?;
    let mut at = file_offset(&sections, u64::from(le_u32(bytes, entry)?))?;
    let limit = crate::num::from_usize(bytes.len() / word).min(IMPORTS_MAX);
    let mut total = 0u64;
    while let Some(descriptor) = bytes.get(at..at + DESCRIPTOR) {
        let field = |k: usize| le_u32(descriptor, k).unwrap_or(0);
        // SPEC: a null descriptor ends the table; the parser also stops at
        // one without a name or an address table.
        if field(12) == 0 || field(16) == 0 {
            break;
        }
        let table = file_offset(&sections, u64::from(field(0)))
            .or_else(|| file_offset(&sections, u64::from(field(16))));
        if let Some(off) = table
            && let Some(words) = bytes.get(off..)
        {
            let room = usize::try_from(limit + 1 - total).unwrap_or(usize::MAX);
            total += crate::num::from_usize(
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
fn c_name(bytes: &[u8], at: usize) -> Option<String> {
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
fn delay_imports(bytes: &[u8], image_base: u64, is_64: bool) -> Vec<Symbol> {
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
    let (Some(rva), Some(sections)) = (le_u32(bytes, entry), raw_sections(bytes)) else {
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
    let limit = crate::num::from_usize(bytes.len() / 4).min(IMPORTS_MAX);
    while let Some(descriptor) = bytes.get(at..at + DESCRIPTOR) {
        let field = |k: usize| le_u32(descriptor, k).unwrap_or(0);
        // SPEC: ImgDelayDescr is grAttrs, rvaDLLName, rvaHmod, rvaIAT,
        // rvaINT, rvaBoundIAT, rvaUnloadIAT, dwTimeStamp; a zeroed one
        // ends the table.
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
                if crate::num::from_usize(out.len()) >= limit {
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
                            le_u32(bytes, k).map(u64::from)
                        }
                    })
                    .filter(|&t| t != 0)
                else {
                    break;
                };
                let import = if thunk & ordinal_bit != 0 {
                    format!("ORDINAL {}", thunk & 0xffff)
                } else {
                    // SPEC: a name entry is a two-byte hint and the name.
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
fn ordinal_exports(pe: &goblin::pe::PE<'_>) -> Vec<Symbol> {
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
struct Disarmed {
    /// File offset of the entry.
    at: usize,
    /// What the entry held.
    saved: [u8; DIRECTORY_ENTRY],
    /// The larger of the counts that condemned it.
    count: u32,
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
/// [`Headers`] is taken over the zeroed bytes meanwhile, and the directory
/// list it renders lacks `export`.
///
/// # Arguments
///
/// * `bytes` - The whole file, patched in place.
///
/// # Returns
///
/// What was zeroed, or `None` when the table is plausible or absent.
fn disarm_exports(bytes: &mut [u8]) -> Option<Disarmed> {
    let (at, _) = directory_entry(bytes, 0)?;
    let table = file_offset(&raw_sections(bytes)?, u64::from(le_u32(bytes, at)?))?;
    // SPEC: the address table's entry count sits 20 bytes into the export
    // directory, the name pointer count 24.
    let count = le_u32(bytes, table + 20)?.max(le_u32(bytes, table + 24)?);
    if count <= EXPORTS_MAX {
        return None;
    }
    let slot = bytes.get_mut(at..at + DIRECTORY_ENTRY)?;
    let saved: [u8; DIRECTORY_ENTRY] = slot.try_into().ok()?;
    slot.fill(0);
    Some(Disarmed { at, saved, count })
}

/// Runs a parse that may panic on a damaged file, and reports the panic as an error.
///
/// The parser indexes the file by the offsets the file's own headers state. A truncated
/// download, a protector that rewrote a data directory, or anything hostile can state an
/// offset past the end, and the slice that follows panics rather than failing. A panic is
/// not a parse error: it unwinds past every `Result` the caller was ready for, and in a
/// server it takes the session with it.
///
/// Hostile and damaged files are the job rather than the exception here, so the panic is
/// caught and told as what it is. A backtrace on stderr about a file the caller already knows
/// is broken is noise, and a caller reading the error learns more from it, so a panic hook
/// installed once stays quiet on a thread while it parses and hands every other panic to
/// the hook that was there before. Swapping the process-wide hook for each parse instead
/// left the quiet one installed for good when two parses overlapped: each put back what it
/// took, and the second had taken the first one's quiet hook.
///
/// # Arguments
///
/// * `parse` - The parse to attempt.
///
/// # Errors
///
/// When the parse panicked, naming the file as unreadable rather than the panic's location.
fn caught<T>(parse: impl FnOnce() -> T) -> anyhow::Result<T> {
    thread_local! {
        /// Whether this thread is inside a parse whose panic is reported as an error.
        static PARSING: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
    }
    static QUIET: std::sync::Once = std::sync::Once::new();
    QUIET.call_once(|| {
        let before = std::panic::take_hook();
        std::panic::set_hook(Box::new(move |info| {
            if !PARSING.with(std::cell::Cell::get) {
                before(info);
            }
        }));
    });
    let was = PARSING.with(|p| p.replace(true));
    let out = std::panic::catch_unwind(std::panic::AssertUnwindSafe(parse));
    PARSING.with(|p| p.set(was));
    out.map_err(|_| {
        anyhow!(
            "the file's headers name offsets outside it, and reading them faulted: it is truncated or damaged rather than a program this can load"
        )
    })
}

/// Why a path cannot be a file, when it cannot.
///
/// Public because a path from a caller is opened in more than one place: the
/// loader here, the fingerprint sidecar a diff reads, and a saved project.
/// Each of those refused a bad path in
/// its own words, or in the operating system's, which for an empty path was
/// "The system cannot find the path specified" with a blank where the path
/// should be.
///
/// Windows resolves a handful of names to character devices in every
/// directory and under any extension, so `con`, `C:/tmp/con` and `con.exe`
/// are all the console, and `CONIN$`/`CONOUT$` its two halves. Reading one
/// is not reading a file: `con` blocks on console input, and inside the MCP
/// server - whose stdin carries the protocol - that took the session's own
/// stream and ended it silently, with no reply to the call that asked. A
/// path in the device namespace (`\\.\pipe\x`, `\\.\PhysicalDrive0`, the
/// same with `/`) is refused whole unless it spells a drive path, and so is
/// an unparsed `\\?\` path that is neither a drive nor a `UNC` path.
///
/// # Arguments
///
/// * `path` - The path as given.
///
/// # Returns
///
/// The reason, ready to put in a message, or `None` when the path is an
/// ordinary one. Only emptiness is checked off Windows, where these names
/// are names like any other.
#[must_use]
pub fn unusable_path(path: &Path) -> Option<String> {
    if path.as_os_str().is_empty() {
        return Some("the path is empty".to_owned());
    }
    if !cfg!(windows) {
        return None;
    }
    let spelled = path.as_os_str().to_string_lossy().replace('/', "\\");
    // SPEC: `\\.\` opens the device namespace and `\\?\` hands the rest to
    // the object manager unparsed; either reaches a file only through a
    // drive (`X:\`) or, for `\\?\`, a `UNC\` share.
    let drive = |rest: &str| {
        let b = rest.as_bytes();
        b.len() >= 3 && b[0].is_ascii_alphabetic() && b[1] == b':' && b[2] == b'\\'
    };
    let device = spelled
        .strip_prefix("\\\\.\\")
        .is_some_and(|rest| !drive(rest))
        || spelled
            .strip_prefix("\\\\?\\")
            .is_some_and(|rest| !drive(rest) && !rest.to_ascii_uppercase().starts_with("UNC\\"));
    if device {
        return Some(format!("{spelled} names a device, not a file"));
    }
    // SPEC: the reserved names, matched on the stem so `con.txt` is caught,
    // and case-insensitively because the filesystem is.
    const DEVICES: [&str; 9] = [
        "con", "prn", "aux", "nul", "com", "lpt", "conin$", "conout$", "clock$",
    ];
    let stem = path.file_stem()?.to_str()?;
    let lower = stem.to_lowercase();
    let named = DEVICES.iter().any(|d| {
        // COM1..COM9 and LPT1..LPT9 carry a digit; the rest stand alone.
        lower == *d
            || (matches!(*d, "com" | "lpt")
                && lower.len() == 4
                && lower.starts_with(d)
                && lower.ends_with(|c: char| c.is_ascii_digit() && c != '0'))
    });
    named.then(|| format!("{stem} is a device, not a file"))
}

impl Program {
    /// A program built from bytes in memory, with no symbols, ranges,
    /// headers or debug information: a fixture, or a dump that has no file.
    ///
    /// # Arguments
    ///
    /// * `bytes` - The whole image, in file order.
    /// * `arch` - The instruction set; `is_64` follows it.
    /// * `image_base` - The preferred load base.
    /// * `entry` - The entry point, when there is one.
    /// * `sections` - The mapped sections.
    #[must_use]
    pub fn raw(
        bytes: Vec<u8>,
        arch: Arch,
        image_base: u64,
        entry: Option<u64>,
        sections: Vec<Section>,
    ) -> Program {
        Program {
            path: PathBuf::new(),
            bytes,
            format: BinaryFormat::Raw,
            is_64: matches!(arch.isa(), Some(Isa::X86 { bits: 64 } | Isa::A64)),
            arch,
            entry,
            image_base,
            sections,
            symbols: Vec::new(),
            function_ranges: Vec::new(),
            headers: Headers::default(),
            debug_functions: Vec::new(),
            debug_types: BTreeMap::new(),
            pdb: None,
            pdb_record: None,
            pdb_source: None,
            flat_fallback: false,
        }
    }

    /// Loads and parses the file at `path`.
    ///
    /// # Arguments
    ///
    /// * `path` - A PE, ELF, Mach-O or other file; unknown formats load as
    ///   [`BinaryFormat::Raw`].
    ///
    /// # Errors
    ///
    /// Returns the I/O error of reading the file, the refusal of a name that
    /// is a device, a directory or anything else that is not a regular
    /// file, or the parse error from [`Program::from_bytes`].
    pub fn load(path: &Path) -> anyhow::Result<Program> {
        Self::load_with(path, true)
    }

    /// Loads a file, saying whether the companion PDB a PE's debug record
    /// names may apply.
    ///
    /// A test or a tool pinning the image's own facts wants the binary
    /// alone, whatever sits beside it or at the recorded path.
    ///
    /// # Arguments
    ///
    /// * `path` - The file to read.
    /// * `apply_pdb` - Whether a companion PDB's symbols apply.
    ///
    /// # Errors
    ///
    /// As [`Program::load`].
    pub fn load_with(path: &Path, apply_pdb: bool) -> anyhow::Result<Program> {
        Self::load_with_symsrv(path, apply_pdb, None)
    }

    /// Loads a file, with a symbol-server cache as a third place the
    /// companion PDB a PE's debug record names may sit.
    ///
    /// The same load as [`Program::load_with`], reading no cache when
    /// `symsrv` is `None`; with one, an entry laid out
    /// `{name}/{guid+age}/{name}` under the root joins the recorded path
    /// and the loaded file's directory as the last candidate
    /// ([`crate::pdb`]). Nothing is fetched: a cache that holds nothing
    /// changes nothing, so the answer still depends only on what is on
    /// disk.
    ///
    /// # Arguments
    ///
    /// * `path` - The file to read.
    /// * `apply_pdb` - Whether a companion PDB's symbols apply.
    /// * `symsrv` - The root of a symbol-server cache, `None` for the two
    ///   on-disk places alone.
    ///
    /// # Errors
    ///
    /// As [`Program::load`].
    pub fn load_with_symsrv(
        path: &Path,
        apply_pdb: bool,
        symsrv: Option<&Path>,
    ) -> anyhow::Result<Program> {
        if let Some(why) = unusable_path(path) {
            return Err(anyhow!("{why}; give a path to a program to analyze"));
        }
        let shown = crate::text::short_path(&path.display().to_string());
        if path.is_dir() {
            return Err(anyhow!(
                "{shown} is a directory; give the path of a program file inside it"
            ));
        }
        let mut file = std::fs::File::open(path).with_context(|| format!("reading {shown}"))?;
        // INVARIANT: only a regular file is read: a handle that reaches a
        // device or a pipe under another spelling reads forever or blocks.
        let meta = file
            .metadata()
            .with_context(|| format!("reading {shown}"))?;
        if !meta.is_file() {
            return Err(anyhow!(
                "{shown} is not a regular file (a device or a pipe); give a path to a program to analyze"
            ));
        }
        let mut bytes = Vec::new();
        std::io::Read::read_to_end(&mut file, &mut bytes)
            .with_context(|| format!("reading {shown}"))?;
        Self::from_bytes_with(path.to_path_buf(), bytes, apply_pdb, symsrv)
    }

    /// Parses an in-memory file image.
    ///
    /// PE: the COFF machine field selects the architecture (`0x8664` AMD64,
    /// `0x014c` i386, `0xaa64` ARM64). Hand-built or damaged PEs carry garbage
    /// section tables, so only entries whose file extents fit the actual file
    /// are kept, save one of a sound table ([`sound_section_table`]) that
    /// starts inside the file and runs past its end, the section a truncated
    /// download cuts, which keeps the bytes the file holds and reads the rest
    /// as its zero-filled tail; when that leaves nothing and the header names
    /// an entry point, the whole file becomes one readable, writable,
    /// executable `<flat>` section and [`Program::flat_fallback`] is set. An
    /// import table that
    /// names more entries than fit in the file, or an export table that
    /// claims more than an ordinal reaches, is not read
    /// ([`Headers::implausible_imports`], [`Headers::implausible_exports`]).
    /// Imports record their IAT
    /// slot address, exports their entry; x64 exception-table entries whose
    /// unwind info is not chained become [`Program::function_ranges`]. The
    /// debug directory's `CodeView` record names a PDB, applied when it is on
    /// disk at the recorded path, beside the loaded file or in the symbol
    /// cache and states the record's GUID and age (the DBI age): its function
    /// symbols become [`SymbolKind::Local`] symbols, its procedure extents
    /// join [`Program::function_ranges`] where an executable section holds
    /// them whole, the signatures its type stream states become
    /// [`Program::debug_functions`], and its data records become
    /// [`SymbolKind::Data`] symbols where a non-executable section maps
    /// them ([`crate::pdb::apply`]); the record itself is kept as
    /// [`Program::pdb_record`]. ELF:
    /// non-allocated sections (no virtual address) are skipped, `SHT_NOBITS`
    /// sections get a zero file size, and the ALLOC flag stands in for
    /// readability since ELF has no explicit read bit; imports take the GOT
    /// slot their PLT or `GLOB_DAT` relocation fills, `.symtab` functions
    /// become [`SymbolKind::Local`] symbols and, when sized, function ranges,
    /// and every `.eh_frame` FDE whose start lies in executable code outside
    /// the PLT adds its extent to the ranges (stripped binaries keep unwind
    /// data, so their functions are still seeded).
    /// Mach-O: the segments' sections, the symbol table with the import
    /// slots the indirect symbols name, and the linker's function starts as
    /// the ranges ([`crate::macho`]); of a fat file, the x86-64 slice.
    /// An ELF file with no section table to read (stripped, or past the
    /// end) maps its `PT_LOAD` segments in its place, as the system loader
    /// does, and says so.
    /// ELF and Mach-O section tables are fitted to the file
    /// ([`fit_sections`]): a row the file cannot hold is dropped
    /// ([`Headers::dropped_sections`]) and one it ends inside keeps what it
    /// holds ([`Headers::truncated`]).
    /// Archives are detected but not parsed.
    ///
    /// # Arguments
    ///
    /// * `path` - Recorded as [`Program::path`]; not opened.
    /// * `bytes` - The file contents, moved into the program.
    ///
    /// # Errors
    ///
    /// Returns an error when goblin recognizes none of its formats.
    pub fn from_bytes(path: PathBuf, bytes: Vec<u8>) -> anyhow::Result<Program> {
        Self::from_bytes_with(path, bytes, true, None)
    }

    /// Builds a program from bytes, saying whether the companion PDB a PE's
    /// debug record names may apply.
    ///
    /// # Arguments
    ///
    /// * `path` - The path the bytes came from (informational; also where a
    ///   companion PDB is looked for).
    /// * `bytes` - The whole file.
    /// * `apply_pdb` - Whether a companion PDB's symbols apply.
    /// * `symsrv` - The root of a symbol-server cache, the last place a
    ///   companion PDB is looked for; `None` for the two on-disk places.
    ///
    /// # Errors
    ///
    /// As [`Program::from_bytes`].
    pub fn from_bytes_with(
        path: PathBuf,
        mut bytes: Vec<u8>,
        apply_pdb: bool,
        symsrv: Option<&Path>,
    ) -> anyhow::Result<Program> {
        let mut phases = crate::timing::Phases::new();
        if bytes.is_empty() {
            return Err(anyhow!("the file is empty: there is nothing to load"));
        }
        let refused_imports = implausible_imports(&bytes);
        let disarmed = disarm_exports(&mut bytes);
        let (patches, mut lenient) = loosen_pe(&mut bytes);
        let (obj, strict) = parse_object(&bytes, refused_imports.is_none()).map_err(|e| {
            match magic_name(&bytes) {
                Some(kind) => anyhow!(
                    "the file starts like {kind} but its headers do not parse, even leniently: it is truncated or damaged ({} bytes; {e})",
                    bytes.len()
                ),
                None => anyhow!("unrecognized format: {e}"),
            }
        })?;
        if let Some(why) = strict {
            lenient.push(format!(
                "the headers do not all parse ({why}); read leniently, what does not parse is skipped"
            ));
        }
        phases.mark("load parse");

        let mut format = BinaryFormat::Raw;
        let mut arch = Arch::Unknown;
        let mut is_64 = false;
        let mut entry: Option<u64> = None;
        let mut image_base = 0u64;
        let mut sections: Vec<Section> = Vec::new();
        let mut unmapped: Vec<Section> = Vec::new();
        let mut symbols: Vec<Symbol> = Vec::new();
        let mut function_ranges: Vec<(u64, u64)> = Vec::new();
        let mut exception_handlers: Vec<crate::headers::ExceptionHandler> = Vec::new();
        let mut chained_chunks: Vec<(u64, u64)> = Vec::new();
        let mut headers = Headers::default();
        let mut flat_fallback = false;
        let file_len = crate::num::from_usize(bytes.len());
        let mut fit = Fit::default();
        let mut pdb_record: Option<crate::pdb::Record> = None;

        match &obj {
            goblin::Object::PE(pe) => {
                format = BinaryFormat::Pe;
                arch = match pe.header.coff_header.machine {
                    0x8664 => Arch::X86_64,
                    0x014c => Arch::X86,
                    0xaa64 => Arch::Arm64,
                    _ => Arch::Unknown,
                };
                is_64 = pe.is_64;
                image_base = pe.image_base;
                if pe.entry != 0 {
                    entry = pe.image_base.checked_add(u64::from(pe.entry));
                }

                /// `IMAGE_SCN_MEM_EXECUTE`.
                const EXEC: u32 = 0x2000_0000;
                /// `IMAGE_SCN_MEM_READ`.
                const READ: u32 = 0x4000_0000;
                /// `IMAGE_SCN_MEM_WRITE`.
                const WRITE: u32 = 0x8000_0000;
                let sound = pe.header.optional_header.is_some_and(|o| {
                    sound_section_table(&bytes, &pe.sections, o.windows_fields.size_of_headers)
                });
                sections = pe
                    .sections
                    .iter()
                    .filter_map(|s| {
                        let rawsz = u64::from(s.size_of_raw_data);
                        let rawoff = u64::from(s.pointer_to_raw_data);
                        let fits = rawoff + rawsz.min(file_len) <= file_len;
                        // INVARIANT: a row the file cannot hold is garbage,
                        // not a section: a damaged section count runs the
                        // table into code, where a row in fifty happens to
                        // fit the file and the rest name sizes it has not.
                        // Only a sound table's row that starts inside the
                        // file and runs past its end is a truncated section,
                        // kept with the bytes the file holds.
                        let cut = !fits && sound && rawoff < file_len;
                        let va = pe.image_base.checked_add(u64::from(s.virtual_address));
                        let sane = rawsz <= SANE_MAX
                            && u64::from(s.virtual_size) <= SANE_MAX
                            && rawoff <= file_len
                            && (fits || cut);
                        let Some(va) = va.filter(|_| sane) else {
                            fit.dropped += 1;
                            return None;
                        };
                        if cut {
                            fit.note_cut(rawoff + rawsz);
                        }
                        Some(Section {
                            // SPEC: PE/COFF section names over 8 bytes are stored as `/NN`,
                            // an offset into the COFF string table; goblin resolves that into
                            // `real_name`, and `name()` prefers it.
                            name: s.name().map_or_else(
                                |_| {
                                    String::from_utf8_lossy(&s.name)
                                        .trim_end_matches('\0')
                                        .to_owned()
                                },
                                str::to_owned,
                            ),
                            va,
                            vsize: u64::from(s.virtual_size),
                            file_off: rawoff,
                            file_size: if cut { file_len - rawoff } else { rawsz },
                            readable: s.characteristics & READ != 0,
                            writable: s.characteristics & WRITE != 0,
                            executable: s.characteristics & EXEC != 0,
                        })
                    })
                    .collect();
                if fit.dropped > 0 && sections.is_empty() && pe.entry != 0 {
                    sections.push(Section {
                        name: "<flat>".to_owned(),
                        va: pe.image_base,
                        vsize: file_len,
                        file_off: 0,
                        file_size: file_len,
                        readable: true,
                        writable: true,
                        executable: true,
                    });
                    flat_fallback = true;
                }

                let va_of_off = |off: u64| -> u64 {
                    sections
                        .iter()
                        .find_map(|s| {
                            if s.file_size > 0
                                && off >= s.file_off
                                && off < s.file_off + s.file_size
                            {
                                Some(s.va + (off - s.file_off))
                            } else {
                                None
                            }
                        })
                        .unwrap_or(0)
                };
                for imp in &pe.imports {
                    let name = if imp.name.is_empty() {
                        "(unnamed)".to_owned()
                    } else {
                        imp.name.to_string()
                    };
                    let dll = imp.dll.trim_end_matches('\0');
                    // SPEC: goblin's `Import::offset` is the IAT slot RVA; `rva` is the hint/name entry.
                    let addr = if imp.offset != 0 {
                        pe.image_base.wrapping_add(imp.offset as u64)
                    } else {
                        va_of_off(imp.rva as u64)
                    };
                    symbols.push(Symbol {
                        name: format!("{dll}!{name}"),
                        addr,
                        kind: SymbolKind::Import,
                    });
                }
                for exp in &pe.exports {
                    let name = exp
                        .name
                        .map_or_else(|| format!("sub_{:x}", exp.rva), |n| n.to_owned());
                    symbols.push(Symbol {
                        name,
                        addr: pe.image_base.wrapping_add(exp.rva as u64),
                        kind: if exp.reexport.is_some() {
                            SymbolKind::Forwarder
                        } else {
                            SymbolKind::Export
                        },
                    });
                }
                symbols.extend(ordinal_exports(pe));
                let delayed = if refused_imports.is_none() {
                    delay_imports(&bytes, pe.image_base, pe.is_64)
                } else {
                    Vec::new()
                };
                let mut delay_slots: Vec<u64> = delayed.iter().map(|s| s.addr).collect();
                delay_slots.sort_unstable();
                symbols.extend(delayed);
                if arch == Arch::X86_64
                    && let Some(ex) = &pe.exception_data
                {
                    // The walk indexes the file by the offsets the exception
                    // directory states, and a truncated or rewritten file
                    // states offsets outside it. Losing the ranges costs
                    // discovery a seed it has other ways to find; losing the
                    // program costs everything.
                    let (found, registered, chunks) = caught(|| {
                        let mut out = Vec::new();
                        let mut handlers = Vec::new();
                        let mut chunks = Vec::new();
                        for rf in ex.functions().flatten() {
                            if rf.begin_address >= rf.end_address {
                                continue;
                            }
                            let Ok(u) = ex.get_unwind_info(rf, &pe.sections) else {
                                out.push((
                                    image_base + u64::from(rf.begin_address),
                                    image_base + u64::from(rf.end_address),
                                ));
                                continue;
                            };
                            if u.chained_info.is_some() {
                                chunks.push((
                                    image_base + u64::from(rf.begin_address),
                                    image_base + u64::from(rf.end_address),
                                ));
                                continue;
                            }
                            let function = image_base + u64::from(rf.begin_address);
                            out.push((function, image_base + u64::from(rf.end_address)));
                            // The handler's data is a slice of the file; its
                            // place in the file is its place in the image.
                            let Some(
                                goblin::pe::exception::UnwindHandler::ExceptionHandler(
                                    handler,
                                    data,
                                )
                                | goblin::pe::exception::UnwindHandler::TerminationHandler(
                                    handler,
                                    data,
                                ),
                            ) = u.handler
                            else {
                                continue;
                            };
                            let off =
                                (data.as_ptr() as usize).wrapping_sub(bytes.as_ptr() as usize);
                            if off < bytes.len() {
                                handlers.push(crate::headers::ExceptionHandler {
                                    function,
                                    handler: image_base + u64::from(handler),
                                    data: va_of_off(off as u64),
                                });
                            }
                        }
                        (out, handlers, chunks)
                    })
                    .unwrap_or_default();
                    function_ranges.extend(found);
                    exception_handlers = registered;
                    chained_chunks = chunks;
                    chained_chunks.sort_unstable();
                }
                // The header facts are read through the same directories, so
                // the same damaged file can fault here too.
                headers = caught(|| {
                    crate::headers::from_pe(pe, &bytes, file_len, &sections, function_ranges.len())
                })
                .unwrap_or_default();
                headers.exception_handlers = exception_handlers;
                headers.chained_chunks = chained_chunks;
                headers.delay_imports = delay_slots;
                pdb_record = pe
                    .debug_data
                    .as_ref()
                    .and_then(|d| d.codeview_pdb70_debug_info.as_ref())
                    .map(crate::pdb::Record::from_debug_info);
            }
            goblin::Object::Elf(elf) => {
                format = BinaryFormat::Elf;
                is_64 = elf.is_64;
                arch = match elf.header.e_machine {
                    62 => Arch::X86_64,
                    3 => Arch::X86,
                    183 => Arch::Arm64,
                    _ => Arch::Unknown,
                };
                entry = (elf.entry != 0).then_some(elf.entry);

                /// `SHF_WRITE`.
                const WRITE: u64 = 0x1;
                /// `SHF_ALLOC`: mapped, hence readable (ELF has no read bit).
                const ALLOC: u64 = 0x2;
                /// `SHF_EXECINSTR`.
                const EXEC: u64 = 0x4;
                for sh in &elf.section_headers {
                    let name = elf.shdr_strtab.get_at(sh.sh_name).unwrap_or("");
                    let nobits = sh.sh_type == goblin::elf::section_header::SHT_NOBITS;
                    if sh.sh_addr == 0 {
                        if name.starts_with(".debug_") && !nobits {
                            unmapped.push(Section {
                                name: name.to_owned(),
                                va: 0,
                                vsize: 0,
                                file_off: sh.sh_offset,
                                file_size: sh.sh_size,
                                readable: false,
                                writable: false,
                                executable: false,
                            });
                        }
                        continue;
                    }
                    sections.push(Section {
                        name: name.to_owned(),
                        va: sh.sh_addr,
                        vsize: sh.sh_size,
                        file_off: sh.sh_offset,
                        file_size: if nobits { 0 } else { sh.sh_size },
                        readable: sh.sh_flags & ALLOC != 0,
                        writable: sh.sh_flags & WRITE != 0,
                        executable: sh.sh_flags & EXEC != 0,
                    });
                }
                if elf.section_headers.is_empty() {
                    /// `PT_LOAD`.
                    const PT_LOAD: u32 = 1;
                    /// `PF_X`, `PF_W`, `PF_R`.
                    const PF: (u32, u32, u32) = (1, 2, 4);
                    for (i, ph) in elf
                        .program_headers
                        .iter()
                        .filter(|p| p.p_type == PT_LOAD)
                        .enumerate()
                    {
                        sections.push(Section {
                            name: format!("LOAD{i}"),
                            va: ph.p_vaddr,
                            vsize: ph.p_memsz,
                            file_off: ph.p_offset,
                            file_size: ph.p_filesz,
                            readable: ph.p_flags & PF.2 != 0,
                            writable: ph.p_flags & PF.1 != 0,
                            executable: ph.p_flags & PF.0 != 0,
                        });
                    }
                    if !sections.is_empty() {
                        lenient.push(
                            "no section table to read; the PT_LOAD segments are mapped in its place"
                                .to_owned(),
                        );
                    }
                }
                fit.add(fit_sections(&mut sections, file_len));
                fit.add(fit_sections(&mut unmapped, file_len));

                let mut slot_of: BTreeMap<usize, u64> = BTreeMap::new();
                for r in elf
                    .pltrelocs
                    .iter()
                    .chain(elf.dynrelas.iter())
                    .chain(elf.dynrels.iter())
                {
                    if r.r_sym != 0 {
                        slot_of.entry(r.r_sym).or_insert(r.r_offset);
                    }
                }
                let strs = &elf.dynstrtab;
                for (i, sym) in elf.dynsyms.iter().enumerate() {
                    let Some(name) = strs.get_at(sym.st_name) else {
                        continue;
                    };
                    if name.is_empty() {
                        continue;
                    }
                    if sym.st_shndx == 0 {
                        symbols.push(Symbol {
                            name: name.to_owned(),
                            addr: slot_of.get(&i).copied().unwrap_or(0),
                            kind: SymbolKind::Import,
                        });
                    } else if sym.st_value != 0 {
                        symbols.push(Symbol {
                            name: name.to_owned(),
                            addr: sym.st_value,
                            kind: SymbolKind::Export,
                        });
                    }
                }
                let exported: BTreeSet<(u64, &str)> =
                    symbols.iter().map(|s| (s.addr, s.name.as_str())).collect();
                let mut locals: Vec<Symbol> = Vec::new();
                for sym in &elf.syms {
                    let kind = goblin::elf::sym::st_type(sym.st_info);
                    let is_code = kind == goblin::elf::sym::STT_FUNC
                        || kind == goblin::elf::sym::STT_GNU_IFUNC;
                    if !is_code || sym.st_value == 0 {
                        continue;
                    }
                    let Some(name) = elf.strtab.get_at(sym.st_name) else {
                        continue;
                    };
                    if name.is_empty() {
                        continue;
                    }
                    if sym.st_size != 0 {
                        function_ranges.push((sym.st_value, sym.st_value + sym.st_size));
                    }
                    if !exported.contains(&(sym.st_value, name)) {
                        locals.push(Symbol {
                            name: name.to_owned(),
                            addr: sym.st_value,
                            kind: SymbolKind::Local,
                        });
                    }
                }
                symbols.extend(locals);
                let mut unwind = 0usize;
                if let Some(sec) = sections.iter().find(|s| s.name == ".eh_frame")
                    && let (Ok(off), Ok(size)) = (
                        usize::try_from(sec.file_off),
                        usize::try_from(sec.file_size),
                    )
                    && let Some(slice) = off.checked_add(size).and_then(|end| bytes.get(off..end))
                {
                    let in_code = |va: u64| {
                        sections.iter().any(|s| {
                            s.executable
                                && !s.name.starts_with(".plt")
                                && va >= s.va
                                && va < s.va.saturating_add(s.vsize)
                        })
                    };
                    for (start, end) in crate::eh_frame::function_ranges(slice, sec.va, is_64) {
                        if in_code(start) {
                            unwind += 1;
                            function_ranges.push((start, end));
                        }
                    }
                }
                headers = crate::headers::from_elf(elf, &bytes);
                headers.unwind_functions = unwind;
            }
            goblin::Object::Mach(mach) => {
                format = BinaryFormat::MachO;
                let loaded = crate::macho::load(&bytes, mach)?;
                arch = loaded.arch;
                is_64 = loaded.is_64;
                entry = loaded.entry;
                image_base = loaded.image_base;
                sections = loaded.sections;
                symbols = loaded.symbols;
                function_ranges = loaded.function_ranges;
                headers = loaded.headers;
                fit.add(loaded.fit);
                if let Some(why) = loaded.lenient {
                    lenient.push(why);
                }
            }
            goblin::Object::Archive(_) => format = BinaryFormat::Archive,
            _ => {}
        }
        drop(obj);
        phases.mark("load headers+symbols");
        if let Some(d) = disarmed
            && let Some(slot) = bytes.get_mut(d.at..d.at + DIRECTORY_ENTRY)
        {
            slot.copy_from_slice(&d.saved);
        }
        restore(&mut bytes, &patches);
        headers.lenient = lenient;
        headers.dropped_sections = fit.dropped;
        headers.truncated = fit.cut;
        headers.implausible_imports = refused_imports;
        headers.implausible_exports = disarmed.map(|d| d.count);
        // The compiler's own names, where it left them. These are facts from
        // the file, not guesses, so they take precedence over a synthesized
        // `sub_` name the way any other symbol does. A stripped image keeps
        // its DWARF often enough to be worth reading: on a MinGW build the
        // runtime's whole startup path comes back named.
        let debug = crate::dwarf::read(&sections, &unmapped, &bytes);
        let mut named = debug.subprograms;
        phases.mark("load dwarf");
        // The PDB the debug record names, when it is on disk where the
        // record or the loaded file says: the compiler's names for every
        // function it saw, applied the way the DWARF names are, so a
        // PDB's name wins nowhere an export or import already holds the
        // address and DWARF fills nothing a PDB already named. Its
        // procedure extents join the function ranges where an executable
        // section holds each one whole, the signatures its type stream
        // states join the debug functions, and its data records name the
        // globals as data symbols where a non-executable section maps
        // them.
        let pdb = if apply_pdb {
            pdb_record.as_ref().and_then(|rec| {
                crate::pdb::apply(
                    &path,
                    symsrv,
                    rec,
                    image_base,
                    i64::from(arch.bitness().unwrap_or(64) / 8),
                    &sections,
                    &mut symbols,
                    &mut function_ranges,
                    &mut named,
                )
            })
        } else {
            None
        };
        phases.mark("load pdb");
        // The applied PDB's own facts, for the source lines a first header
        // asks for: the lines stay unread until one does, so a load never
        // pays for rows no one asked of it.
        let pdb_source = match (&pdb, &pdb_record) {
            (Some(crate::pdb::Outcome::Applied { .. }), Some(rec)) => {
                crate::pdb::resolved(&path, rec, symsrv).map(|p| (p, rec.clone()))
            }
            _ => None,
        };
        // INVARIANT: a data symbol marks data, so it blocks no function
        // name: a DWARF subprogram at an address still takes it over a PDB
        // data record that disagrees.
        let already: BTreeSet<u64> = symbols
            .iter()
            .filter(|s| s.kind != SymbolKind::Data)
            .map(|s| s.addr)
            .collect();
        for sub in &named {
            if sub.low_pc != 0 && !already.contains(&sub.low_pc) {
                symbols.push(Symbol {
                    name: sub.name.clone(),
                    addr: sub.low_pc,
                    kind: SymbolKind::Local,
                });
            }
        }
        // Every name above came out of the file, and the file is the thing
        // under analysis: a name holding a newline forges a row in any
        // listing that prints it, and one holding a terminal escape rewrites
        // what surrounds it. Defusing them here covers each of the listings
        // downstream, and any that is added later.
        for s in &mut sections {
            s.name = crate::text::one_line(&s.name);
        }
        for s in &mut symbols {
            s.name = crate::text::one_line(&s.name);
        }
        for f in &mut named {
            f.name = crate::text::one_line(&f.name);
        }

        function_ranges.sort_unstable();
        function_ranges.dedup();
        phases.mark("load finish");

        Ok(Program {
            path,
            bytes,
            format,
            arch,
            is_64,
            entry,
            image_base,
            sections,
            symbols,
            function_ranges,
            headers,
            debug_functions: named,
            debug_types: debug.types,
            pdb,
            pdb_record,
            pdb_source,
            flat_fallback,
        })
    }

    /// The addresses of the pointer-sized words a PE's base relocation
    /// table fixes up: every absolute address the image holds, as an
    /// instruction's operand or as data.
    ///
    /// A 32-bit image names its function pointers nowhere else: a table of
    /// callbacks kept in `.text` (a linker without `.rdata` puts it there)
    /// is a run of relocated words, where a scan of the data sections never
    /// looks. Only `HIGHLOW` entries count in a 32-bit image and `DIR64` in
    /// a 64-bit one.
    ///
    /// # Returns
    ///
    /// The fixed-up words' addresses in table order, at most a million;
    /// empty for a file that is not PE or has no relocations.
    #[must_use]
    pub fn relocated_words(&self) -> Vec<u64> {
        /// Most relocated words read, whatever the table claims.
        const WORDS_MAX: usize = 1 << 20;
        /// `IMAGE_REL_BASED_HIGHLOW`, a 32-bit address.
        const HIGHLOW: u16 = 3;
        /// `IMAGE_REL_BASED_DIR64`, a 64-bit address.
        const DIR64: u16 = 10;
        let mut out = Vec::new();
        if self.format != BinaryFormat::Pe {
            return out;
        }
        let bytes = &self.bytes;
        let Some((entry, _)) = directory_entry(bytes, 5) else {
            return out;
        };
        let (Some(rva), Some(size)) = (le_u32(bytes, entry), le_u32(bytes, entry + 4)) else {
            return out;
        };
        let Some(table) = self.read_va(self.image_base + u64::from(rva), size as usize) else {
            return out;
        };
        let wanted = if self.is_64 { DIR64 } else { HIGHLOW };
        let mut at = 0usize;
        while at + 8 <= table.len() && out.len() < WORDS_MAX {
            let page = u32::from_le_bytes([table[at], table[at + 1], table[at + 2], table[at + 3]]);
            let block =
                u32::from_le_bytes([table[at + 4], table[at + 5], table[at + 6], table[at + 7]])
                    as usize;
            if block < 8 {
                break;
            }
            let end = (at + block).min(table.len());
            for e in table[at + 8..end].chunks_exact(2) {
                let entry = u16::from_le_bytes([e[0], e[1]]);
                if entry >> 12 == wanted {
                    out.push(self.image_base + u64::from(page) + u64::from(entry & 0xfff));
                }
            }
            at += block;
        }
        out.truncate(WORDS_MAX);
        out
    }

    /// Finds the file-backed section containing `va`.
    ///
    /// # Arguments
    ///
    /// * `va` - A virtual address.
    ///
    /// # Returns
    ///
    /// The section whose span (the larger of its memory and file sizes) holds
    /// `va`, or `None` when the address is unmapped or only in `.bss`-style
    /// memory.
    pub fn section_at(&self, va: u64) -> Option<&Section> {
        self.sections.iter().find(|s| {
            let span = s.vsize.max(s.file_size);
            s.file_size > 0 && va >= s.va && va < s.va.saturating_add(span)
        })
    }

    /// Converts a virtual address to its file offset.
    ///
    /// # Arguments
    ///
    /// * `va` - A virtual address inside a file-backed section.
    ///
    /// # Returns
    ///
    /// The offset, or `None` when [`Program::section_at`] finds no section.
    pub fn va_to_offset(&self, va: u64) -> Option<u64> {
        let s = self.section_at(va)?;
        Some(s.file_off + (va - s.va))
    }

    /// Converts a file offset to the virtual address it is mapped at.
    ///
    /// # Arguments
    ///
    /// * `off` - An offset into the file.
    ///
    /// # Returns
    ///
    /// The address, or `None` when no section's file extent covers `off`.
    pub fn offset_to_va(&self, off: u64) -> Option<u64> {
        self.sections.iter().find_map(|s| {
            if s.file_size > 0 && off >= s.file_off && off < s.file_off.saturating_add(s.file_size)
            {
                Some(s.va + (off - s.file_off))
            } else {
                None
            }
        })
    }

    /// Returns the runs of file bytes that no section's file extent covers.
    ///
    /// The headers before the first section, the gaps between sections, an
    /// overlay appended after the last one, and the whole of a file with no
    /// sections: bytes the file holds that have no virtual address, read by
    /// file offset ([`Program::read_off_upto`]).
    ///
    /// # Returns
    ///
    /// `(file offset, bytes)` per run, in file order; empty when the
    /// sections cover the whole file.
    pub fn unmapped(&self) -> Vec<(u64, &[u8])> {
        let mut covered: Vec<(u64, u64)> = self
            .sections
            .iter()
            .filter(|s| self.section_bytes(s).is_some())
            .map(|s| (s.file_off, s.file_off + s.file_size))
            .collect();
        covered.sort_unstable();
        let len = crate::num::from_usize(self.bytes.len());
        let mut runs = Vec::new();
        let mut next = 0u64;
        for (start, end) in covered.into_iter().chain([(len, len)]) {
            if start > next
                && let Some(bytes) = self
                    .bytes
                    .get(crate::num::saturating_usize(next)..crate::num::saturating_usize(start))
            {
                runs.push((next, bytes));
            }
            next = next.max(end);
        }
        runs
    }

    /// Reads up to `max` bytes at a file offset, clamped at the end of the
    /// file.
    ///
    /// The read for bytes no section maps (see [`Program::unmapped`]), and
    /// for any byte of the file by where it sits rather than where it loads.
    ///
    /// # Arguments
    ///
    /// * `off` - File offset of the first byte.
    /// * `max` - Upper bound on the number of bytes.
    ///
    /// # Returns
    ///
    /// A non-empty slice, or `None` when `off` is at or past the end of the
    /// file.
    pub fn read_off_upto(&self, off: u64, max: usize) -> Option<&[u8]> {
        let start = usize::try_from(off).ok()?;
        let end = start.saturating_add(max).min(self.bytes.len());
        self.bytes.get(start..end).filter(|b| !b.is_empty())
    }

    /// Returns the raw bytes of a section's file extent.
    ///
    /// # Arguments
    ///
    /// * `s` - A section of this program.
    ///
    /// # Returns
    ///
    /// The bytes, or `None` when the extent runs past the end of the file.
    pub fn section_bytes(&self, s: &Section) -> Option<&[u8]> {
        let start = usize::try_from(s.file_off).ok()?;
        let end = usize::try_from(s.file_off.checked_add(s.file_size)?).ok()?;
        self.bytes.get(start..end)
    }

    /// Reads up to `max` bytes at `va`, clamped at the end of the section.
    ///
    /// Scans that must not fail at a section edge (string reads, disassembly
    /// windows) use this; [`Program::read_va`] is the exact-length form.
    ///
    /// # Arguments
    ///
    /// * `va` - Virtual address of the first byte.
    /// * `max` - Upper bound on the number of bytes.
    ///
    /// # Returns
    ///
    /// A non-empty slice, or `None` when `va` is unmapped or at the very end
    /// of its section's file bytes.
    pub fn read_va_upto(&self, va: u64, max: usize) -> Option<&[u8]> {
        let Some(s) = self.section_at(va) else {
            // The headers are mapped but are not a section; a short read of
            // them is the same read as a short read of anything else.
            let first = self.sections.first()?;
            let cap = first.va.checked_sub(self.image_base)?.min(first.file_off);
            let off = va.checked_sub(self.image_base)?;
            let room = usize::try_from(cap.checked_sub(off)?).ok()?;
            return self.header_slice(va, max.min(room));
        };
        let off = s.file_off + (va - s.va);
        let limit = (s.file_off + s.file_size).min(self.bytes.len() as u64);
        let end = (off + max as u64).min(limit);
        self.bytes
            .get(usize::try_from(off).ok()?..usize::try_from(end).ok()?)
            .filter(|b| !b.is_empty())
    }

    /// Reads exactly `len` bytes at `va` from one section's file bytes.
    ///
    /// A read past the section's file extent (its zero-filled tail, or the
    /// next section) is refused instead of returning unrelated bytes.
    ///
    /// # Arguments
    ///
    /// * `va` - Virtual address of the first byte.
    /// * `len` - Exact number of bytes.
    ///
    /// # Returns
    ///
    /// The bytes, or `None` when the range is not entirely file-backed.
    pub fn read_va(&self, va: u64, len: usize) -> Option<&[u8]> {
        let Some(s) = self.section_at(va) else {
            return self.header_slice(va, len);
        };
        let off = s.file_off + (va - s.va);
        let end = off.checked_add(len as u64)?;
        if end > s.file_off + s.file_size {
            return None;
        }
        self.bytes
            .get(usize::try_from(off).ok()?..usize::try_from(end).ok()?)
    }

    /// The mapped headers at `va`, when `va` is inside them.
    ///
    /// A PE's headers are mapped at the image base, one to one with the start
    /// of the file, and they are not a section: nothing in the section table
    /// covers them, so every reader that goes through the table refuses the
    /// one address a binary is most often opened at. Asking a program for its
    /// image base is asking for the `MZ`, which is a fair question, and the
    /// live reader has always answered it.
    ///
    /// The extent is where the first section begins, in the image and in the
    /// file, whichever comes first: below that offset a file holds headers and
    /// nothing else, so the mapping is exact rather than assumed.
    ///
    /// # Arguments
    ///
    /// * `va` - Virtual address of the first byte.
    /// * `len` - Exact number of bytes.
    ///
    /// # Returns
    ///
    /// The bytes, or `None` when the range is not entirely inside the headers.
    fn header_slice(&self, va: u64, len: usize) -> Option<&[u8]> {
        if self.format != BinaryFormat::Pe || va < self.image_base {
            return None;
        }
        let first = self.sections.first()?;
        let cap = first.va.checked_sub(self.image_base)?.min(first.file_off);
        let off = va - self.image_base;
        let end = off.checked_add(len as u64)?;
        if end > cap {
            return None;
        }
        self.bytes
            .get(usize::try_from(off).ok()?..usize::try_from(end).ok()?)
    }

    /// Tells whether `va` lies in a PE's mapped headers: the image's first
    /// bytes, up to its first section, which no section maps.
    ///
    /// # Arguments
    ///
    /// * `va` - A virtual address.
    #[must_use]
    pub fn in_headers(&self, va: u64) -> bool {
        self.header_slice(va, 1).is_some()
    }

    /// Says why the engine cannot do `feature` with this program's code,
    /// when it cannot.
    ///
    /// An unrecognized file loads as raw bytes of no architecture, and a
    /// program for another instruction set loads with its sections and
    /// symbols; neither has code borer can disassemble. The answer names
    /// the format so the reader knows which of the two it has, and points
    /// at the tools that read any file.
    ///
    /// # Arguments
    ///
    /// * `feature` - What the tool asks of the code.
    ///
    /// # Returns
    ///
    /// `None` when [`Arch::supports`] the feature; otherwise the sentence
    /// a code tool answers with.
    pub fn refuses(&self, feature: Feature) -> Option<String> {
        (!self.arch.supports(feature)).then(|| {
            format!(
                "{} file, arch '{}': borer analyzes only x86 and x86-64 code, so no code analysis applies; triage, entropy and strings read any file",
                self.format.name(),
                self.arch.name()
            )
        })
    }

    /// Returns a compact `name(start..end)` listing of the sections.
    ///
    /// Error messages about unmapped addresses append it so an agent can
    /// correct the address without another call; `none` for a file with no
    /// sections, so the message does not end on an empty list. At most
    /// [`SECTIONS_SHOWN`] are named, then `... N more`.
    pub fn section_list(&self) -> String {
        if self.sections.is_empty() {
            return "none".to_owned();
        }
        let more = self.sections.len().saturating_sub(SECTIONS_SHOWN);
        self.sections
            .iter()
            .take(SECTIONS_SHOWN)
            .map(|s| {
                format!(
                    "{}({:#x}..{:#x})",
                    s.name,
                    s.va,
                    s.va.saturating_add(s.vsize.max(s.file_size))
                )
            })
            .chain((more > 0).then(|| format!("... {more} more")))
            .collect::<Vec<_>>()
            .join(" ")
    }

    /// Renders the `binary_info` summary.
    ///
    /// # Returns
    ///
    /// Path, size, format and architecture (its width only when the
    /// architecture is known), why no code analysis applies and the
    /// container magic when there are, base and entry, a flat-mapping
    /// warning when it applies, the section table with permissions and
    /// entropy (at most [`SECTIONS_SHOWN`] rows, under a `# showing N of M
    /// sections` line when there are more), and import/export counts with
    /// up to ten sample names each.
    pub fn summary(&self) -> String {
        let mut out = String::new();
        out.push_str(&format!("path:    {}\n", self.path.display()));
        out.push_str(&format!("size:    {} bytes\n", self.bytes.len()));
        out.push_str(&format!(
            "format:  {}   arch: {}{}\n",
            self.format.name(),
            self.arch.name(),
            match (self.arch, self.is_64) {
                (Arch::Unknown, _) => "",
                (_, true) => " (64-bit)",
                (_, false) => " (32-bit)",
            }
        ));
        if let Some(machine) = &self.headers.machine {
            out.push_str(&format!("machine: {machine}\n"));
        }
        if let Some(why) = self.refuses(Feature::Discover) {
            out.push_str(&format!("code:    {why}\n"));
        }
        if let Some(magic) = crate::headers::sniff_file(&self.bytes) {
            out.push_str(&format!("magic:   {magic}\n"));
        }
        match self.entry {
            Some(e) => out.push_str(&format!(
                "base:    {:#x}   entry: {:#x}\n",
                self.image_base, e
            )),
            None => out.push_str(&format!("base:    {:#x}   entry: -\n", self.image_base)),
        }
        if self.flat_fallback {
            out.push_str("# warning: section table corrupt; using a flat file mapping\n");
        }
        for note in &self.headers.lenient {
            out.push_str(&format!("# warning: {note}\n"));
        }
        if self.format == BinaryFormat::Elf
            && self.sections.is_empty()
            && self.headers.kind == Some("ET_REL")
        {
            out.push_str("# note: a relocatable object (ET_REL): its sections have no load addresses, so none is mapped and there is no code to analyze until it is linked; strings, entropy and symbols still read it\n");
        }
        if self.headers.dropped_sections > 0 {
            out.push_str(&format!(
                "# warning: {} section(s) dropped: the table states offsets or sizes the file cannot hold (past its end, or over 1 GiB)\n",
                self.headers.dropped_sections
            ));
        }
        if let Some(end) = self.headers.truncated {
            out.push_str(&format!(
                "# warning: truncated: the sections state bytes up to file offset {end:#x} and the file ends at {:#x}; what it does not hold is not analyzed\n",
                self.bytes.len()
            ));
        }
        out.push_str(&format!("sections ({}):\n", self.sections.len()));
        if self.sections.len() > SECTIONS_SHOWN {
            out.push_str(&format!(
                "# showing {SECTIONS_SHOWN} of {} sections\n",
                self.sections.len()
            ));
        }
        out.push_str("  name           va            vsize     file_off  size      rwx  entropy\n");
        for s in self.sections.iter().take(SECTIONS_SHOWN) {
            // A `/NN` name is a COFF string-table offset this file no
            // longer resolves, so the content is asked what it is.
            let guess = if s.name.starts_with('/') {
                self.section_bytes(s)
                    .and_then(crate::headers::sniff_section)
                    .map_or_else(String::new, |g| format!("  looks like {g}"))
            } else {
                String::new()
            };
            out.push_str(&format!(
                "  {:<14} {:<12} {:<9} {:<9} {:<9} {}  {:>5.2}{}\n",
                s.name,
                format!("{:#x}", s.va),
                format!("{:#x}", s.vsize),
                format!("{:#x}", s.file_off),
                format!("{:#x}", s.file_size),
                s.perms(),
                self.section_entropy(s),
                guess
            ));
        }
        let imports: Vec<&Symbol> = self
            .symbols
            .iter()
            .filter(|s| s.kind == SymbolKind::Import)
            .collect();
        let exports: Vec<&Symbol> = self
            .symbols
            .iter()
            .filter(|s| matches!(s.kind, SymbolKind::Export | SymbolKind::Forwarder))
            .collect();
        out.push_str(&format!("imports: {}", imports.len()));
        if !self.headers.delay_imports.is_empty() {
            out.push_str(&format!(
                " ({} delay-loaded)",
                self.headers.delay_imports.len()
            ));
        }
        if !imports.is_empty() {
            let sample: Vec<String> = imports
                .iter()
                .take(10)
                .map(|s| crate::search::demangled_name(&s.name))
                .collect();
            out.push_str(&format!("  [{}]", sample.join(", ")));
            if imports.len() > 10 {
                out.push_str(", ...");
            }
        }
        out.push('\n');
        out.push_str(&format!("exports: {}", exports.len()));
        let forwarded = exports
            .iter()
            .filter(|s| s.kind == SymbolKind::Forwarder)
            .count();
        if forwarded > 0 {
            out.push_str(&format!(" ({forwarded} forwarded)"));
        }
        if !exports.is_empty() {
            let sample: Vec<String> = exports
                .iter()
                .take(10)
                .map(|s| format!("{:#x} {}", s.addr, crate::search::demangled_name(&s.name)))
                .collect();
            out.push_str(&format!("  [{}]", sample.join(", ")));
            if exports.len() > 10 {
                out.push_str(", ...");
            }
        }
        out.push('\n');
        let locals = self
            .symbols
            .iter()
            .filter(|s| s.kind == SymbolKind::Local)
            .count();
        if locals > 0 {
            out.push_str(&format!("locals:  {locals} named functions\n"));
        }
        if let Some(outcome) = &self.pdb {
            out.push_str(&format!("pdb:     {}\n", outcome.render()));
        }
        out.push_str(&self.headers.render());
        out
    }

    /// Computes a section's entropy for the summary.
    ///
    /// Sections above 1 MiB are sampled with a stride so `binary_info` stays
    /// instant on large images.
    ///
    /// # Arguments
    ///
    /// * `s` - A section of this program.
    ///
    /// # Returns
    ///
    /// Bits per byte, or `0.0` when the section has no file bytes.
    fn section_entropy(&self, s: &Section) -> f64 {
        let Some(data) = self.section_bytes(s) else {
            return 0.0;
        };
        if data.len() > 1 << 20 {
            let stride = data.len() / (1 << 20) + 1;
            shannon(&data.iter().step_by(stride).copied().collect::<Vec<u8>>())
        } else {
            shannon(data)
        }
    }
}

#[cfg(test)]
impl Program {
    /// Builds a raw x86-64 image for a unit test: one executable section at
    /// `0x1000` holding `code`, entered at its first byte, padded with `int3`.
    ///
    /// # Arguments
    ///
    /// * `code` - The bytes placed at `0x1000`; at most one page.
    pub(crate) fn raw_x64(code: &[u8]) -> Program {
        /// Bytes in the one section.
        const PAGE: usize = 0x1000;
        let mut bytes = vec![0xcc; PAGE];
        bytes[..code.len().min(PAGE)].copy_from_slice(&code[..code.len().min(PAGE)]);
        let text = Section::mapped(
            ".text",
            0x1000,
            0,
            crate::num::from_usize(PAGE),
            false,
            true,
        );
        Program::raw(bytes, Arch::X86_64, 0, Some(0x1000), vec![text])
    }
}

#[cfg(test)]
mod tests {
    use super::{Arch, Program, caught, unusable_path};

    /// The summary of a file with no code says why code tools have nothing
    /// to read and what its magic names, and claims no width for an
    /// architecture it does not know; it read `arch: unknown (32-bit)`.
    ///
    /// # Panics
    ///
    /// When a line is missing or the width is claimed.
    #[test]
    fn the_summary_of_a_file_with_no_code_says_so() {
        let p = Program::raw(
            b"PK\x03\x04\x14\0\0\0".to_vec(),
            Arch::Unknown,
            0,
            None,
            Vec::new(),
        );
        let s = p.summary();
        assert!(s.contains("arch: unknown\n"), "{s}");
        assert!(s.contains("code:    raw file, arch 'unknown': "), "{s}");
        assert!(s.contains("magic:   zip archive\n"), "{s}");
        let code = Program::raw_x64(&[0xc3]).summary();
        assert!(code.contains("arch: x86-64 (64-bit)\n"), "{code}");
        assert!(
            !code.contains("code:") && !code.contains("magic:"),
            "{code}"
        );
    }

    /// A raw arm64 program has eight-byte pointers, as a loaded arm64
    /// image does; `is_64` followed the x86 decoder width, which arm64 has
    /// none of, and the summary called the program 32-bit.
    ///
    /// # Panics
    ///
    /// When the program is not 64-bit or the summary says otherwise.
    #[test]
    fn a_raw_arm64_program_is_64_bit() {
        let p = Program::raw(vec![0; 4], Arch::Arm64, 0, None, Vec::new());
        assert!(p.is_64);
        let s = p.summary();
        assert!(
            s.contains(
                "arch: arm64 (64-bit)
"
            ),
            "{s}"
        );
        assert!(!Program::raw(vec![0xc3], Arch::X86, 0, None, Vec::new()).is_64);
    }

    /// A section table of thousands of rows is listed up to the cap.
    ///
    /// The summary and the compact list error messages append both stop
    /// there, under a line that says how many there are: 65,535 rows made one
    /// `binary_info` answer 4.6 MB.
    ///
    /// # Panics
    ///
    /// When a row past the cap is listed or the counts are not said.
    #[test]
    fn a_huge_section_table_is_listed_up_to_the_cap() {
        let sections = (0u64..1000)
            .map(|i| super::Section::mapped(&format!("s{i}"), 0x1000 * (i + 1), 0, 1, false, false))
            .collect();
        let p = Program::raw(vec![0xc3], Arch::X86_64, 0, None, sections);
        let s = p.summary();
        assert!(
            s.contains("sections (1000):\n# showing 64 of 1000 sections\n"),
            "{s}"
        );
        assert!(s.contains("  s63 ") && !s.contains("  s64 "), "{s}");
        let list = p.section_list();
        assert!(
            list.ends_with("s63(0x40000..0x40001) ... 936 more"),
            "{list}"
        );
    }

    /// A device name is refused instead of read.
    ///
    /// Windows resolves these in every directory and under any extension, and
    /// reading the console blocks on its input: inside the MCP server, whose
    /// stdin carries the protocol, that consumed the session's own stream and
    /// ended it with no reply to the call that asked for it.
    ///
    /// # Panics
    ///
    /// When a device is treated as a file, or a file as a device.
    #[test]
    fn a_device_name_is_not_a_file() {
        let is_device = |p: &str| unusable_path(std::path::Path::new(p)).is_some();
        if cfg!(windows) {
            assert!(is_device("con"), "the console");
            assert!(is_device("CON"), "the filesystem does not care about case");
            assert!(is_device("con.txt"), "an extension does not make it a file");
            assert!(is_device(r"C:\tmp\con"), "nor does a directory");
            assert!(is_device("com1") && is_device("LPT9"), "the numbered ports");
            assert!(Program::load(std::path::Path::new("con")).is_err());
            assert!(
                is_device("CONIN$") && is_device("conout$"),
                "the console halves"
            );
            assert!(is_device(r"\\.\pipe\borer"), "a pipe");
            assert!(
                is_device("//./PhysicalDrive0"),
                "a disk, spelled with slashes"
            );
            assert!(is_device(r"\\?\GLOBALROOT\Device\Null"), "an object path");
            assert!(!is_device(r"\\?\C:\tmp\a.exe"), "a long drive path");
            assert!(!is_device(r"\\?\UNC\host\share\a.exe"), "a long share path");
            assert!(
                !is_device(r"\\.\C:\tmp\a.exe"),
                "a drive path in the device space"
            );
            let dir = std::env::temp_dir();
            let refused = Program::load(&dir).expect_err("a directory is no program");
            assert!(refused.to_string().contains("is a directory"), "{refused}");
        }
        // Names that only look like one.
        assert!(!is_device("control.dll"), "a real name starting with con");
        assert!(!is_device("com0"), "there is no COM0");
        assert!(!is_device("com10"), "nor a two-digit port");
        assert!(!is_device("borer.exe"));
        // An empty path is refused too, and says so rather than letting
        // the operating system report a blank one as missing.
        assert!(unusable_path(std::path::Path::new("")).is_some());
    }

    /// A name out of the file cannot forge a row in a listing.
    ///
    /// Section names are eight raw bytes the file chooses freely, and every
    /// listing borer prints is one record to a line. A name holding a newline
    /// therefore reads as two records, the second of them invented by the file
    /// under analysis and indistinguishable from a real one; a terminal escape
    /// in the same place rewrites whatever is around it. The running test
    /// binary is the fixture, so the name comes through the real parser rather
    /// than a constructed `Section`.
    ///
    /// # Panics
    ///
    /// When a hostile name survives into a section name.
    #[test]
    fn a_name_out_of_the_file_cannot_forge_a_row() {
        let exe = std::env::current_exe().expect("the test binary has a path");
        let mut bytes = std::fs::read(&exe).expect("the test binary is readable");
        // Only PE stores a section name as raw bytes in the table; an ELF
        // build of these tests has nothing to overwrite in place.
        if bytes.first_chunk::<2>() != Some(b"MZ") {
            return;
        }
        let at = |b: &[u8], off: usize, n: usize| -> usize {
            let mut v = 0usize;
            for (i, byte) in b.iter().skip(off).take(n).enumerate() {
                v |= (*byte as usize) << (8 * i);
            }
            v
        };
        let lfanew = at(&bytes, 0x3c, 4);
        let table = lfanew + 4 + 20 + at(&bytes, lfanew + 4 + 16, 2);
        let Some(name) = bytes.get_mut(table..table + 8) else {
            panic!("the test binary has no section table at {table:#x}");
        };
        name.copy_from_slice(b".t\nEVIL\x1b");

        let program = Program::from_bytes(exe, bytes).expect("a PE with an odd name still loads");
        let first = &program.sections.first().expect("it has sections").name;
        assert!(
            !first.contains(char::is_control),
            "a row can be forged: {first:?}"
        );
        assert!(
            first.starts_with(".t"),
            "the readable part is kept: {first:?}"
        );
    }

    /// A parse that faults on a damaged file is an error, not a crash.
    ///
    /// The parser indexes a file by the offsets the file's own headers state,
    /// and a truncated or rewritten file states offsets outside it. That
    /// faults rather than failing, which unwinds past every `Result` the
    /// caller was ready for - and in a server it takes the session with it.
    /// Damaged and hostile files are the job here, so the fault is caught and
    /// told as what it is.
    ///
    /// # Panics
    ///
    /// When a fault reaches the caller, or a sound parse does not.
    #[test]
    fn a_parse_that_faults_is_told_as_an_error() {
        let faulted = caught(|| {
            // The offset comes through a black box so the compiler cannot
            // prove the fault and refuse to build it, which is the same
            // reason a real one only shows on a file nobody checked.
            let small = [0u8; 4];
            let past = std::hint::black_box(small.len() + 5);
            #[expect(clippy::indexing_slicing, reason = "the fault under test")]
            small[past]
        });
        assert!(faulted.is_err(), "the fault reached the caller");
        let said = faulted.unwrap_err().to_string();
        assert!(
            said.contains("truncated or damaged"),
            "the error does not say what happened: {said}"
        );
        assert!(
            !said.contains("  "),
            "the message reads as one line: {said}"
        );
    }

    /// A file too short or too damaged to parse says what it is.
    ///
    /// An empty file is refused in those words, a few bytes of no known
    /// format load as raw bytes as a longer one does, and a file whose magic
    /// names a format but whose headers do not parse is called truncated or
    /// damaged, not an unrecognized format.
    ///
    /// # Panics
    ///
    /// When a file loads or is refused otherwise.
    #[test]
    fn a_short_file_says_what_it_is() {
        let load = |b: &[u8]| Program::from_bytes(std::path::PathBuf::from("short"), b.to_vec());
        let empty = load(b"").expect_err("an empty file is no program");
        assert!(empty.to_string().contains("the file is empty"), "{empty}");
        let one = load(b"x").expect("one byte of nothing known loads raw");
        assert_eq!(one.format, super::BinaryFormat::Raw);
        for (bytes, kind) in [(&b"MZ"[..], "a PE"), (b"ELF", "an ELF image")] {
            let said = load(bytes).expect_err("a header too short").to_string();
            assert!(
                said.starts_with(&format!(
                    "the file starts like {kind} but its headers do not parse"
                )),
                "{said}"
            );
            assert!(said.contains("truncated or damaged"), "{said}");
        }
    }

    /// A parse that does not fault is returned untouched.
    ///
    /// # Panics
    ///
    /// When a sound parse is reported as a fault.
    #[test]
    fn a_parse_that_holds_is_returned_as_it_is() {
        assert_eq!(caught(|| 7u32).ok(), Some(7));
    }

    /// The panic hook is put back, so a later fault still reports itself,
    /// also after two parses overlapped.
    ///
    /// Silencing the hook for the length of the parse keeps a backtrace about
    /// a file the caller already knows is broken off stderr. Leaving it
    /// silenced would hide every unrelated panic the process goes on to have.
    ///
    /// # Panics
    ///
    /// When the hook is not restored.
    #[test]
    fn the_panic_hook_is_put_back_after_a_parse() {
        let marker = std::sync::Arc::new(std::sync::atomic::AtomicBool::new(false));
        let seen = std::sync::Arc::clone(&marker);
        std::panic::set_hook(Box::new(move |_| {
            seen.store(true, std::sync::atomic::Ordering::SeqCst);
        }));
        let _ = caught(|| panic!("under test"));
        let out = std::panic::catch_unwind(|| panic!("after"));
        assert!(out.is_err());
        assert!(
            marker.load(std::sync::atomic::Ordering::SeqCst),
            "the hook this test installed never ran again"
        );
        let both = std::sync::Arc::new(std::sync::Barrier::new(2));
        let overlapping: Vec<_> = (0..2)
            .map(|_| {
                let both = std::sync::Arc::clone(&both);
                std::thread::spawn(move || {
                    let _ = caught(|| {
                        both.wait();
                        panic!("overlapping")
                    });
                })
            })
            .collect();
        for t in overlapping {
            t.join().expect("a parse thread finishes");
        }
        marker.store(false, std::sync::atomic::Ordering::SeqCst);
        let out = std::panic::catch_unwind(|| panic!("after two at once"));
        assert!(out.is_err());
        assert!(
            marker.load(std::sync::atomic::Ordering::SeqCst),
            "two overlapping parses left the process without its hook"
        );
        let _ = std::panic::take_hook();
    }
}
