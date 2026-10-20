//! Binary loading: parses PE, ELF and Mach-O (and detects archives) into a
//! normalized, immutable [`Program`] that every analysis query reads from.
//!
//! Design rule: a `Program` holds only facts derived from the file. User
//! annotations (renames, comments, types) live in a separate overlay, so
//! analysis stays a pure function of the input.

use std::path::{Path, PathBuf};

use std::collections::{BTreeMap, BTreeSet};

use anyhow::anyhow;

use crate::entropy::shannon;
use crate::headers::Headers;
use crate::isa::Isa;
use crate::num::{from_usize, saturating_usize, u32_le};

mod arm;
pub(crate) mod file;
pub(crate) mod pe;

pub use file::{Parent, read_regular, unusable_path};
use file::{Take, magic_name, parse_object, read_program_bytes};
use pe::{
    DIRECTORY_ENTRY, SANE_MAX, arm64_pdata, delay_imports, directory_entry, disarm_exports,
    implausible_imports, loosen_pe, name_ordinal_imports, ordinal_exports, restore,
    sound_section_table,
};

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
    /// 32-bit ARM: A32 and T32 (Thumb-2) code, which instruction set at
    /// which address told by [`Program::modes`].
    Arm,
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
            Arch::Arm => "arm",
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
            Arch::Arm => Some(Isa::A32),
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
                Feature::Disasm | Feature::Discover | Feature::Emulate | Feature::Decompile => true,
            },
            Some(Isa::A32) => match feature {
                Feature::Disasm | Feature::Discover | Feature::Decompile => true,
                Feature::Emulate => false,
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

/// A virtual address: where a byte sits once the image is mapped.
///
/// Newtype over the `u64` virtual addresses the whole engine speaks, so a
/// file offset ([`FileOff`]) or a size cannot silently stand in for one:
/// the two meet only where one says so, through `.0` at a boundary that
/// names the choice. Sizes stay bare `u64`, and an address becomes a file
/// offset only through [`Program::va_to_offset`], and the other way only
/// through [`Program::offset_to_va`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Va(
    /// The address, in bytes.
    pub u64,
);

/// A file offset: where a byte sits in the file the image was loaded from.
///
/// Newtype over the `u64` file offsets, the mirror of [`Va`]: the loader
/// reads the file by these and the analysis reads the image by addresses,
/// and a value of one kind reaching code of the other is a mixup the
/// compiler rejects instead of one a query answers wrongly with.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct FileOff(
    /// The offset, in bytes from the start of the file.
    pub u64,
);

/// One mapped section of the image.
#[derive(Debug, Clone)]
pub struct Section {
    /// Section name as stored in the file (`.text`, `.rdata`, ...).
    pub name: String,
    /// Virtual address of the first byte when the image is loaded.
    pub va: Va,
    /// Size in memory, in bytes (may exceed `file_size`: zero-filled tail).
    pub vsize: u64,
    /// Offset of the section's bytes in the file.
    pub file_off: FileOff,
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
    /// The fixture boundary for building a [`Section`] by hand: `va` and
    /// `file_off` stay bare `u64` here and convert to [`Va`] and
    /// [`FileOff`], so the test images that state an address and an offset
    /// as numbers keep compiling while the fields carry the types.
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
            va: Va(va),
            vsize: size,
            file_off: FileOff(file_off),
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
    /// Mapped sections in file order; a stated layout's in the order it
    /// names them ([`crate::layout::Layout::program`]). Final at
    /// construction: [`Program::section_at`]'s index is built from them,
    /// so a section pushed after construction is never found.
    pub sections: Vec<Section>,
    /// Address-ordered rows behind [`Program::section_at`]'s binary
    /// search, built from [`Program::sections`] when the program is.
    pub(crate) section_index: Vec<SectionRow>,
    /// Imports, exports, local and data symbols in file order.
    pub symbols: Vec<Symbol>,
    /// Function extents the file declares, `(start, end)` virtual addresses,
    /// sorted: x64 exception-table entries (chained chunks excluded), ARM64
    /// `.pdata` entries (fragments excluded), sized `STT_FUNC` symbols,
    /// `.eh_frame` FDEs, a Mach-O image's function starts, and the extents
    /// an applied PDB's procedures
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
    /// The typedefs the debug information states, by name, with the C
    /// type each stands for ([`crate::dwarf::Debug::typedefs`]).
    pub debug_typedefs: BTreeMap<String, String>,
    /// The variables of static storage the debug information states, as
    /// [`crate::dwarf::Debug::globals`] orders them: a fact the file
    /// states, which types the globals a decompiled text reads.
    pub debug_globals: Vec<crate::dwarf::Global>,
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
    /// What an ELF's dynamic relocations or a Mach-O's fixups write into
    /// the image: every read of the mapped image ([`Program::read_va`],
    /// [`Program::section_bytes`]) sees the relocated words, while
    /// [`Program::bytes`] stays the file.
    pub relocs: crate::reloc::Relocs,
    /// The Go function table, when the program carries one that validates:
    /// the provenance of the names it gave [`Program::symbols`], and the
    /// mark of which functions take Go's arguments ([`crate::go`]).
    pub go: Option<crate::go::Pclntab>,
    /// The .NET metadata of a PE with a CLR runtime header
    /// ([`crate::clr`]): `None` without one, `Some(Err)` with the reason
    /// when its header or metadata does not hold, else what triage reads
    /// of it, the provenance of the method names it gave
    /// [`Program::symbols`].
    pub clr: Option<Result<crate::clr::Clr, String>>,
    /// The file this program was carved from and where, when it was loaded
    /// as `<file>@<offset>` ([`Program::load`]); `None` for a file loaded
    /// whole.
    pub parent: Option<Parent>,
    /// Which instruction set the code at each address is in, for ARM32
    /// code ([`Arch::Arm`]): empty, which is A32 throughout, for every
    /// other architecture.
    pub modes: crate::isa::a32::Modes,
}

/// Rows of [`Program::section_index`]: one stretch of addresses and the
/// first-declared file-backed section holding all of it.
#[derive(Debug, Clone, Copy)]
pub(crate) struct SectionRow {
    /// The stretch's first virtual address.
    va: u64,
    /// One past its last.
    end: u64,
    /// The section's index in [`Program::sections`]: the lowest of every
    /// file-backed section whose span (the larger of its memory and file
    /// sizes) holds the stretch, the one a linear scan in file order finds.
    index: usize,
}

/// Finds the first-declared file-backed section holding an address, by a
/// binary search of a table's rows ([`Program::index_sections`]).
///
/// # Arguments
///
/// * `sections` - The section table.
/// * `index` - Its rows.
/// * `va` - A virtual address.
///
/// # Returns
///
/// The section, or `None` when no file-backed section holds `va`.
pub(crate) fn section_in<'s>(
    sections: &'s [Section],
    index: &[SectionRow],
    va: u64,
) -> Option<&'s Section> {
    let row = index.get(index.partition_point(|r| r.va <= va).checked_sub(1)?)?;
    (va < row.end).then(|| sections.get(row.index)).flatten()
}

/// The union of some spans, sorted and merged, so whether an address falls
/// in one of them costs a binary search instead of a scan of every span.
#[derive(Debug, Clone, Default)]
pub(crate) struct Spans(Vec<(u64, u64)>);

impl Spans {
    /// Merges spans.
    ///
    /// # Arguments
    ///
    /// * `spans` - Each as `(first address, one past the last)`; an empty
    ///   one is left out.
    ///
    /// # Returns
    ///
    /// Their union.
    pub(crate) fn of(spans: impl IntoIterator<Item = (u64, u64)>) -> Self {
        let mut sorted: Vec<(u64, u64)> = spans.into_iter().filter(|(a, b)| b > a).collect();
        sorted.sort_unstable();
        let mut merged: Vec<(u64, u64)> = Vec::with_capacity(sorted.len());
        for (a, b) in sorted {
            match merged.last_mut() {
                Some(last) if a <= last.1 => last.1 = last.1.max(b),
                Some(_) | None => merged.push((a, b)),
            }
        }
        Spans(merged)
    }

    /// Whether one of the spans holds an address.
    ///
    /// # Arguments
    ///
    /// * `va` - The address.
    ///
    /// # Returns
    ///
    /// `true` when a span holds it.
    pub(crate) fn holds(&self, va: u64) -> bool {
        self.0
            .partition_point(|&(a, _)| a <= va)
            .checked_sub(1)
            .and_then(|k| self.0.get(k))
            .is_some_and(|&(_, b)| va < b)
    }
}

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
            && (s.file_size == 0 || s.file_off.0 < file_len)
            && s.va.0.checked_add(s.vsize.max(s.file_size)).is_some();
        if !sane {
            fit.dropped += 1;
            return false;
        }
        let end = s.file_off.0.saturating_add(s.file_size);
        if end > file_len {
            fit.note_cut(end);
            s.file_size = file_len - s.file_off.0;
        }
        true
    });
    fit
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
pub(crate) fn caught<T>(parse: impl FnOnce() -> T) -> anyhow::Result<T> {
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

/// Maps a file offset to the virtual address its section places it at.
///
/// The one scan behind [`Program::offset_to_va`] and the PE reader's
/// file-offset lookups: the first section declared whose file extent
/// covers the offset wins, and the extent saturates rather than
/// overflows on a hostile row.
///
/// # Arguments
///
/// * `sections` - The image's sections, in declaration order.
/// * `off` - An offset into the file.
///
/// # Returns
///
/// The address, or `None` when no section's file extent covers `off`.
fn offset_to_va_in(sections: &[Section], off: u64) -> Option<u64> {
    sections.iter().find_map(|s| {
        (s.file_size > 0 && off >= s.file_off.0 && off < s.file_off.0.saturating_add(s.file_size))
            .then(|| s.va.0 + (off - s.file_off.0))
    })
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
        let section_index = Program::index_sections(&sections);
        Program {
            path: PathBuf::new(),
            bytes,
            format: BinaryFormat::Raw,
            is_64: matches!(arch.isa(), Some(Isa::X86 { bits: 64 } | Isa::A64)),
            arch,
            entry,
            image_base,
            sections,
            section_index,
            symbols: Vec::new(),
            function_ranges: Vec::new(),
            headers: Headers::default(),
            debug_functions: Vec::new(),
            debug_types: BTreeMap::new(),
            debug_typedefs: BTreeMap::new(),
            debug_globals: Vec::new(),
            pdb: None,
            pdb_record: None,
            pdb_source: None,
            flat_fallback: false,
            relocs: crate::reloc::Relocs::default(),
            go: None,
            clr: None,
            parent: None,
            modes: crate::isa::a32::Modes::default(),
        }
    }

    /// Loads and parses the file at `path`.
    ///
    /// A path that names no file but ends in `@<offset>` after one that does
    /// (`dropper.exe@0x4400`) loads the PE, ELF or Mach-O image embedded at
    /// that file offset, as far as its headers state ([`crate::carve`]),
    /// with [`Program::parent`] saying where it came from. A Windows
    /// minidump (`MDMP`) loads as the memory it captured: every range a
    /// section, every module a symbol at its base ([`crate::minidump`]),
    /// purely on any platform.
    ///
    /// # Arguments
    ///
    /// * `path` - A PE, ELF, Mach-O or minidump file, or `<file>@<offset>`;
    ///   unknown formats load as [`BinaryFormat::Raw`].
    ///
    /// # Errors
    ///
    /// Returns the I/O error of reading the file, the refusal of a name that
    /// is a device, a directory or anything else that is not a regular
    /// file, the refusal of an `@<offset>` where no program starts, or the
    /// parse error from [`Program::from_bytes`].
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
        let (bytes, parent) = read_program_bytes(path, Take::Program, 0)?;
        let mut program = Self::from_bytes_with(path.to_path_buf(), bytes, apply_pdb, symsrv)?;
        program.parent = parent;
        Ok(program)
    }

    /// Loads the file at `path` as raw bytes mapped where a caller-stated
    /// layout says, its headers unread.
    ///
    /// The same file checks as [`Program::load`], then
    /// [`crate::layout::Layout::program`]; a `<file>@<offset>` path maps
    /// every byte from that offset on.
    ///
    /// # Arguments
    ///
    /// * `path` - The file to read.
    /// * `layout` - Where its bytes go.
    ///
    /// # Errors
    ///
    /// As [`Program::load`] for the file, and as
    /// [`crate::layout::Layout::program`] for a layout the file cannot
    /// hold.
    pub fn load_layout(path: &Path, layout: &crate::layout::Layout) -> anyhow::Result<Program> {
        let (bytes, parent) = read_program_bytes(path, Take::Rest, 0)?;
        let mut program = layout.program(path.to_path_buf(), bytes)?;
        program.parent = parent;
        Ok(program)
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
    /// unwind info is not chained, and ARM64 `.pdata` entries that are not
    /// fragments, become [`Program::function_ranges`] ([`arm64_pdata`]). The
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
    /// slots the indirect symbols name, and the starts the linker's function
    /// starts and compact unwind table list as the ranges ([`crate::macho`]);
    /// of a fat file, the x86-64 slice.
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
        if bytes.starts_with(b"MDMP") {
            let dump = crate::minidump::program(path, bytes).ok_or_else(|| {
                anyhow!("the minidump's header or stream directory does not sit in the file")
            })?;
            return Ok(dump);
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
        let file_len = from_usize(bytes.len());
        let mut fit = Fit::default();
        let mut pdb_record: Option<crate::pdb::Record> = None;
        let mut relocs = crate::reloc::Relocs::default();
        let mut clr_dir: Option<(u32, u32)> = None;
        let mut arm_marks: Vec<(u64, crate::isa::a32::Mode)> = Vec::new();
        let mut arm_default = crate::isa::a32::Mode::Arm;

        match &obj {
            goblin::Object::PE(pe) => {
                format = BinaryFormat::Pe;
                arch = match pe.header.coff_header.machine {
                    0x8664 => Arch::X86_64,
                    0x014c => Arch::X86,
                    0xaa64 => Arch::Arm64,
                    0x1c0 | 0x1c2 | 0x1c4 => Arch::Arm,
                    _ => Arch::Unknown,
                };
                if pe.header.coff_header.machine != 0x1c0 {
                    arm_default = crate::isa::a32::Mode::Thumb;
                }
                is_64 = pe.is_64;
                image_base = pe.image_base;
                clr_dir = pe
                    .header
                    .optional_header
                    .and_then(|o| o.data_directories.get_clr_runtime_header().copied())
                    .map(|d| (d.virtual_address, d.size));
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
                            name: s.name().map_or_else(
                                |_| {
                                    String::from_utf8_lossy(&s.name)
                                        .trim_end_matches('\0')
                                        .to_owned()
                                },
                                str::to_owned,
                            ),
                            va: Va(va),
                            vsize: u64::from(s.virtual_size),
                            file_off: FileOff(rawoff),
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
                        va: Va(pe.image_base),
                        vsize: file_len,
                        file_off: FileOff(0),
                        file_size: file_len,
                        readable: true,
                        writable: true,
                        executable: true,
                    });
                    flat_fallback = true;
                }

                let va_of_off = |off: u64| -> u64 { offset_to_va_in(&sections, off).unwrap_or(0) };
                for imp in &pe.imports {
                    let name = if imp.name.is_empty() {
                        "(unnamed)".to_owned()
                    } else {
                        imp.name.to_string()
                    };
                    let dll = imp.dll.trim_end_matches('\0');
                    let rva = if imp.offset != 0 { imp.offset } else { imp.rva };
                    let addr = pe.image_base.wrapping_add(from_usize(rva));
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
                        addr: pe.image_base.wrapping_add(from_usize(exp.rva)),
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
                                    data: va_of_off(from_usize(off)),
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
                if arch == Arch::Arm64
                    && let Some(ex) = &pe.exception_data
                {
                    let (found, fragments) =
                        caught(|| arm64_pdata(ex, &pe.sections, image_base)).unwrap_or_default();
                    function_ranges.extend(found);
                    chained_chunks = fragments;
                }
                headers = caught(|| {
                    crate::headers::from_pe(pe, &bytes, file_len, &sections, function_ranges.len())
                })
                .unwrap_or_default();
                headers.exception_handlers = exception_handlers;
                headers.chained_chunks = chained_chunks;
                headers.delay_imports = delay_slots;
                headers.ordinal_imports = name_ordinal_imports(&mut symbols);
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
                    40 => Arch::Arm,
                    _ => Arch::Unknown,
                };
                entry = (elf.entry != 0).then_some(elf.entry);
                if arch == Arch::Arm {
                    arm_marks = arm::mapping_symbols(elf);
                    if elf.entry & 1 == 1 {
                        arm_default = crate::isa::a32::Mode::Thumb;
                    }
                }

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
                                va: Va(0),
                                vsize: 0,
                                file_off: FileOff(sh.sh_offset),
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
                        va: Va(sh.sh_addr),
                        vsize: sh.sh_size,
                        file_off: FileOff(sh.sh_offset),
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
                            va: Va(ph.p_vaddr),
                            vsize: ph.p_memsz,
                            file_off: FileOff(ph.p_offset),
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

                /// Most slots one import is named at: a GOT slot and a PLT
                /// slot are two, a table of thousands is hostile.
                const SLOTS_PER_IMPORT: usize = 16;
                let applied = crate::reloc::read_elf(elf, &bytes, &sections);
                let mut slots_of: BTreeMap<usize, Vec<u64>> = BTreeMap::new();
                for r in elf
                    .pltrelocs
                    .iter()
                    .chain(elf.dynrelas.iter())
                    .chain(elf.dynrels.iter())
                {
                    if r.r_sym != 0 {
                        slots_of.entry(r.r_sym).or_insert_with(|| vec![r.r_offset]);
                    }
                }
                for (sym, slot) in applied.bound {
                    let slots = slots_of.entry(sym).or_default();
                    if !slots.contains(&slot) && slots.len() < SLOTS_PER_IMPORT {
                        slots.push(slot);
                    }
                }
                relocs = applied.relocs;
                let strs = &elf.dynstrtab;
                for (i, sym) in elf.dynsyms.iter().enumerate() {
                    let Some(name) = strs.get_at(sym.st_name) else {
                        continue;
                    };
                    if name.is_empty() {
                        continue;
                    }
                    if sym.st_shndx == 0 {
                        let slots = slots_of.get(&i).map_or(&[0][..], Vec::as_slice);
                        for &addr in slots {
                            symbols.push(Symbol {
                                name: name.to_owned(),
                                addr,
                                kind: SymbolKind::Import,
                            });
                        }
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
                    let is_data = kind == goblin::elf::sym::STT_OBJECT && sym.st_size != 0;
                    if !(is_code || is_data) || sym.st_value == 0 {
                        continue;
                    }
                    let Some(name) = elf.strtab.get_at(sym.st_name) else {
                        continue;
                    };
                    if name.is_empty() {
                        continue;
                    }
                    if is_data {
                        if !exported.contains(&(sym.st_value, name)) {
                            locals.push(Symbol {
                                name: name.to_owned(),
                                addr: sym.st_value,
                                kind: SymbolKind::Data,
                            });
                        }
                        continue;
                    }
                    if sym.st_size != 0
                        && let Some(end) = sym.st_value.checked_add(sym.st_size)
                    {
                        function_ranges.push((sym.st_value, end));
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
                        usize::try_from(sec.file_off.0),
                        usize::try_from(sec.file_size),
                    )
                    && let Some(slice) = off.checked_add(size).and_then(|end| bytes.get(off..end))
                {
                    let code = Spans::of(
                        sections
                            .iter()
                            .filter(|s| s.executable && !s.name.starts_with(".plt"))
                            .map(|s| (s.va.0, s.va.0.saturating_add(s.vsize))),
                    );
                    for (start, end) in crate::eh_frame::function_ranges(slice, sec.va.0, is_64) {
                        if code.holds(start) {
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
                arm_default = crate::isa::a32::Mode::Thumb;
                is_64 = loaded.is_64;
                entry = loaded.entry;
                image_base = loaded.image_base;
                sections = loaded.sections;
                symbols = loaded.symbols;
                function_ranges = loaded.function_ranges;
                headers = loaded.headers;
                relocs = loaded.relocs;
                fit.add(loaded.fit);
                if let Some(why) = loaded.lenient {
                    lenient.push(why);
                }
            }
            goblin::Object::Archive(_) => format = BinaryFormat::Archive,
            _ => {}
        }
        drop(obj);
        let modes = if arch == Arch::Arm {
            let mut code = arm::Code {
                entry: &mut entry,
                symbols: &mut symbols,
                ranges: &mut function_ranges,
                sections: &sections,
            };
            arm::settle(&mut code, &arm_marks, arm_default)
        } else {
            crate::isa::a32::Modes::default()
        };
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
        let debug = crate::dwarf::read(&sections, &unmapped, &bytes);
        let mut named = debug.subprograms;
        phases.mark("load dwarf");
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
        let pdb_source = match (&pdb, &pdb_record) {
            (Some(crate::pdb::Outcome::Applied { .. }), Some(rec)) => {
                crate::pdb::resolved(&path, rec, symsrv).map(|p| (p, rec.clone()))
            }
            _ => None,
        };
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

        let section_index = Program::index_sections(&sections);
        let mut program = Program {
            path,
            bytes,
            format,
            arch,
            is_64,
            entry,
            image_base,
            sections,
            section_index,
            symbols,
            function_ranges,
            headers,
            debug_functions: named,
            debug_types: debug.types,
            debug_typedefs: debug.typedefs,
            debug_globals: debug.globals,
            pdb,
            pdb_record,
            pdb_source,
            flat_fallback,
            relocs,
            go: None,
            clr: None,
            parent: None,
            modes,
        };
        program.read_go();
        phases.mark("load go");
        program.read_clr(clr_dir);
        phases.mark("load clr");
        Ok(program)
    }

    /// Reads the Go function table and names the functions it lists where
    /// nothing else in the file does ([`crate::go`]).
    ///
    /// It runs on the image as loaded, its relocations applied, since a
    /// PIE's table states its text start through one.
    fn read_go(&mut self) {
        let Some(word) = self
            .arch
            .bitness()
            .map(|b| saturating_usize(u64::from(b / 8)))
        else {
            return;
        };
        let Some((table, funcs)) = crate::go::find(&self.sections, |s| self.section_bytes(s), word)
        else {
            return;
        };
        let named = crate::go::symbols(&funcs, &self.symbols);
        self.symbols.extend(named);
        self.go = Some(table);
    }

    /// Reads the .NET metadata a CLR runtime header points at and names
    /// each method's body with its method ([`crate::clr`]).
    ///
    /// # Arguments
    ///
    /// * `dir` - The CLR runtime header's data directory, `(rva, size)`;
    ///   `None` for a file without one.
    fn read_clr(&mut self, dir: Option<(u32, u32)>) {
        let Some(dir) = dir else {
            return;
        };
        let read = crate::clr::read(self, dir);
        if let Ok(clr) = &read {
            let named = clr.symbols(self.image_base, &self.symbols);
            self.symbols.extend(named);
        }
        self.clr = Some(read);
    }

    /// The .NET metadata, when the program has a CLR runtime header whose
    /// metadata reads ([`Program::clr`]).
    ///
    /// # Returns
    ///
    /// The metadata, or `None` for a file without one or with one refused.
    #[must_use]
    pub fn clr(&self) -> Option<&crate::clr::Clr> {
        self.clr.as_ref().and_then(|c| c.as_ref().ok())
    }

    /// The addresses of the pointer-sized words a PE's base relocation
    /// table, a position-independent ELF's dynamic relocations or a
    /// Mach-O's rebases fix up: every absolute address the image holds, as
    /// an instruction's operand or as data.
    ///
    /// A 32-bit image names its function pointers nowhere else: a table of
    /// callbacks kept in `.text` (a linker without `.rdata` puts it there)
    /// is a run of relocated words, where a scan of the data sections never
    /// looks. Only `HIGHLOW` entries count in a 32-bit image and `DIR64` in
    /// a 64-bit one. An ELF's are its `RELATIVE`, absolute and `DT_RELR`
    /// words ([`crate::reloc`]), and only an `ET_DYN` image's, the one kind
    /// that relocates every pointer it holds; a Mach-O's are its rebases
    /// ([`crate::dyld`]), and only a PIE's, a dylib's or a bundle's.
    ///
    /// # Returns
    ///
    /// The fixed-up words' addresses, in table order for a PE and address
    /// order for an ELF or a Mach-O, at most a million; empty for any other
    /// file or one with no relocations.
    #[must_use]
    pub fn relocated_words(&self) -> Vec<u64> {
        /// Most relocated words read, whatever the table claims.
        const WORDS_MAX: usize = 1 << 20;
        /// `IMAGE_REL_BASED_HIGHLOW`, a 32-bit address.
        const HIGHLOW: u16 = 3;
        /// `IMAGE_REL_BASED_DIR64`, a 64-bit address.
        const DIR64: u16 = 10;
        let mut out = Vec::new();
        if matches!(self.format, BinaryFormat::Elf | BinaryFormat::MachO) {
            return self.relocs.sites.clone();
        }
        if self.format != BinaryFormat::Pe {
            return out;
        }
        let bytes = &self.bytes;
        let Some((entry, _)) = directory_entry(bytes, 5) else {
            return out;
        };
        let (Some(rva), Some(size)) = (u32_le(bytes, entry), u32_le(bytes, entry + 4)) else {
            return out;
        };
        let Some(table) = self.read_va(
            self.image_base + u64::from(rva),
            saturating_usize(u64::from(size)),
        ) else {
            return out;
        };
        let wanted = if self.is_64 { DIR64 } else { HIGHLOW };
        let mut at = 0usize;
        while at + 8 <= table.len() && out.len() < WORDS_MAX {
            let (Some(page), Some(block)) = (u32_le(table, at), u32_le(table, at + 4)) else {
                break;
            };
            let block = saturating_usize(u64::from(block));
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

    /// Builds the address-ordered lookup rows of a section table.
    ///
    /// The file-backed sections' spans ([`Program::section_at`]'s answers)
    /// are cut at every span's start and end into stretches that do not
    /// overlap, each naming the first-declared section holding it: the
    /// same section a linear scan of the table in file order returns,
    /// however the sections nest or overlap, found by one binary search
    /// ([`section_in`]) even when every section overlaps every other.
    ///
    /// # Arguments
    ///
    /// * `sections` - The final section table.
    ///
    /// # Returns
    ///
    /// The rows, sorted by virtual address.
    pub(crate) fn index_sections(sections: &[Section]) -> Vec<SectionRow> {
        let mut spans: Vec<(u64, u64, usize)> = sections
            .iter()
            .enumerate()
            .filter(|&(_, s)| s.file_size > 0)
            .map(|(index, s)| {
                (
                    s.va.0,
                    s.va.0.saturating_add(s.vsize.max(s.file_size)),
                    index,
                )
            })
            .filter(|&(va, end, _)| end > va)
            .collect();
        spans.sort_unstable();
        let mut ends: Vec<(u64, usize)> =
            spans.iter().map(|&(_, end, index)| (end, index)).collect();
        ends.sort_unstable();
        let mut bounds: Vec<u64> = spans.iter().flat_map(|&(va, end, _)| [va, end]).collect();
        bounds.sort_unstable();
        bounds.dedup();
        let (mut opened, mut closed) = (0, 0);
        let mut live: BTreeSet<usize> = BTreeSet::new();
        let mut rows: Vec<SectionRow> = Vec::new();
        for pair in bounds.windows(2) {
            let &[lo, hi] = pair else {
                continue;
            };
            while let Some(&(_, index)) = ends.get(closed).filter(|&&(end, _)| end <= lo) {
                live.remove(&index);
                closed += 1;
            }
            while let Some(&(_, _, index)) = spans.get(opened).filter(|&&(va, ..)| va <= lo) {
                live.insert(index);
                opened += 1;
            }
            let Some(&index) = live.first() else {
                continue;
            };
            match rows.last_mut() {
                Some(row) if row.end == lo && row.index == index => row.end = hi,
                Some(_) | None => rows.push(SectionRow {
                    va: lo,
                    end: hi,
                    index,
                }),
            }
        }
        rows
    }

    /// Finds the file-backed section containing `va`.
    ///
    /// # Arguments
    ///
    /// * `va` - A virtual address.
    ///
    /// # Returns
    ///
    /// The first-declared section whose span (the larger of its memory and
    /// file sizes) holds `va`, or `None` when the address is unmapped or only
    /// in `.bss`-style memory.
    pub fn section_at(&self, va: u64) -> Option<&Section> {
        if let Some(first) = self.sections.first()
            && first.file_size > 0
            && first.va.0 <= va
            && va < first.va.0.saturating_add(first.vsize.max(first.file_size))
        {
            return Some(first);
        }
        section_in(&self.sections, &self.section_index, va)
    }

    /// Finds the zero-filled section containing `va`: one the loader maps
    /// but the file holds no bytes for (`.bss`, a PE section with no raw
    /// data), where a program keeps its uninitialized globals.
    ///
    /// # Arguments
    ///
    /// * `va` - A virtual address.
    ///
    /// # Returns
    ///
    /// The first-declared such section holding `va`, or `None`.
    pub fn zero_fill_at(&self, va: u64) -> Option<&Section> {
        self.sections
            .iter()
            .find(|s| s.file_size == 0 && s.va.0 <= va && va < s.va.0.saturating_add(s.vsize))
    }

    /// Converts a virtual address to its file offset.
    ///
    /// # Arguments
    ///
    /// * `va` - A virtual address inside a file-backed section.
    ///
    /// # Returns
    ///
    /// The offset, or `None` when [`Program::section_at`] finds no section
    /// or the offset the address maps to does not fit one.
    pub fn va_to_offset(&self, va: u64) -> Option<u64> {
        let s = self.section_at(va)?;
        s.file_off.0.checked_add(va - s.va.0)
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
        offset_to_va_in(&self.sections, off)
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
            .map(|s| (s.file_off.0, s.file_off.0.saturating_add(s.file_size)))
            .collect();
        covered.sort_unstable();
        let len = from_usize(self.bytes.len());
        let mut runs = Vec::new();
        let mut next = 0u64;
        for (start, end) in covered.into_iter().chain([(len, len)]) {
            if start > next
                && let Some(bytes) = self
                    .bytes
                    .get(saturating_usize(next)..saturating_usize(start))
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

    /// Returns the bytes of a section's file extent as the image holds them.
    ///
    /// They are the file's, with the words an ELF's dynamic relocations
    /// write in place ([`Program::relocs`]).
    ///
    /// # Arguments
    ///
    /// * `s` - A section of this program.
    ///
    /// # Returns
    ///
    /// The bytes, or `None` when the extent runs past the end of the file.
    pub fn section_bytes(&self, s: &Section) -> Option<&[u8]> {
        self.image_bytes(s.file_off.0, s.file_off.0.checked_add(s.file_size)?)
    }

    /// Reads file offsets `start..end` as the loaded image holds them: the
    /// relocated copy where the dynamic relocations wrote into the range,
    /// else the file.
    ///
    /// # Arguments
    ///
    /// * `start` - File offset of the first byte.
    /// * `end` - File offset one past the last byte.
    ///
    /// # Returns
    ///
    /// The bytes, or `None` when the range runs past the end of the file.
    fn image_bytes(&self, start: u64, end: u64) -> Option<&[u8]> {
        if let Some(relocated) = self.relocs.slice(start, end) {
            return Some(relocated);
        }
        self.bytes
            .get(usize::try_from(start).ok()?..usize::try_from(end).ok()?)
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
    /// A non-empty slice, or `None` when `va` is unmapped, at the very end
    /// of its section's file bytes, or maps past any file offset.
    pub fn read_va_upto(&self, va: u64, max: usize) -> Option<&[u8]> {
        let Some(s) = self.section_at(va) else {
            let first = self.sections.first()?;
            let cap = first
                .va
                .0
                .checked_sub(self.image_base)?
                .min(first.file_off.0);
            let off = va.checked_sub(self.image_base)?;
            let room = usize::try_from(cap.checked_sub(off)?).ok()?;
            return self.header_slice(va, max.min(room));
        };
        let off = s.file_off.0.checked_add(va - s.va.0)?;
        let limit = (s.file_off.0 + s.file_size).min(from_usize(self.bytes.len()));
        let end = (off + from_usize(max)).min(limit);
        self.image_bytes(off, end).filter(|b| !b.is_empty())
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
    /// The bytes, or `None` when the range is not entirely file-backed or
    /// the offset it maps to does not fit one.
    pub fn read_va(&self, va: u64, len: usize) -> Option<&[u8]> {
        let Some(s) = self.section_at(va) else {
            return self.header_slice(va, len);
        };
        let off = s.file_off.0.checked_add(va - s.va.0)?;
        let end = off.checked_add(from_usize(len))?;
        if end > s.file_off.0 + s.file_size {
            return None;
        }
        self.image_bytes(off, end)
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
        let cap = first
            .va
            .0
            .checked_sub(self.image_base)?
            .min(first.file_off.0);
        let off = va - self.image_base;
        let end = off.checked_add(from_usize(len))?;
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

    /// Returns the instruction set to read this program's code in for
    /// `feature`.
    ///
    /// An unrecognized file loads as raw bytes of no architecture, and a
    /// program for another instruction set loads with its sections and
    /// symbols; neither has code borer can read. An arm64 program is
    /// disassembled, its functions discovered and its code emulated, and
    /// nothing more yet. The
    /// refusal names the format so the reader knows which case it has, says
    /// what does apply, and points at the tools that read any file.
    ///
    /// # Arguments
    ///
    /// * `feature` - What the tool asks of the code.
    ///
    /// # Errors
    ///
    /// The sentence a code tool answers with when the engine does not do
    /// `feature` with this architecture ([`Arch::supports`]).
    pub fn isa_for(&self, feature: Feature) -> Result<Isa, String> {
        let (format, arch) = (self.format.name(), self.arch.name());
        match self.arch.isa() {
            Some(isa) if self.arch.supports(feature) => Ok(isa),
            Some(_) if self.arch.supports(Feature::Disasm) => {
                let stage = match feature {
                    Feature::Disasm => "disassemble it",
                    Feature::Discover => "discover its functions",
                    Feature::Emulate => "emulate it",
                    Feature::Decompile => "decompile it",
                };
                let (runs, beyond) = if self.arch.supports(Feature::Emulate) {
                    (
                        " and runs it in the emulator (borer://emulate, borer://run),",
                        "its functions, blocks, calls and runs",
                    )
                } else {
                    ("", "its functions, blocks and calls")
                };
                Err(format!(
                    "{format} file, arch '{arch}': borer disassembles {arch} code and discovers its functions (functions, function, disassemble_function, cfg, callgraph, xrefs){runs} but does not yet {stage}, so no code analysis beyond {beyond} applies; triage, entropy and strings read any file"
                ))
            }
            Some(_) | None => Err(format!(
                "{format} file, arch '{arch}': borer decodes only x86, x86-64, arm64 and 32-bit arm code, so no code analysis applies; triage, entropy and strings read any file{}",
                if self.format == BinaryFormat::Raw {
                    "; if this is raw code or a memory dump, load it again with arch=x86|x64|arm64 (CLI: --arch)"
                } else {
                    ""
                }
            )),
        }
    }

    /// Says why the engine cannot do `feature` with this program's code,
    /// when it cannot.
    ///
    /// # Arguments
    ///
    /// * `feature` - What the tool asks of the code.
    ///
    /// # Returns
    ///
    /// `None` when [`Arch::supports`] the feature; otherwise the sentence
    /// a code tool answers with ([`Program::isa_for`]).
    pub fn refuses(&self, feature: Feature) -> Option<String> {
        self.isa_for(feature).err()
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
                    s.va.0,
                    s.va.0.saturating_add(s.vsize.max(s.file_size))
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
    /// architecture is known), what code analysis does not apply (the
    /// decompiler's refusal) and the container magic when there are, base
    /// and entry, a flat-mapping
    /// warning when it applies, the section table with permissions and
    /// entropy (at most [`SECTIONS_SHOWN`] rows, under a `# showing N of M
    /// sections` line when there are more), and import/export counts with
    /// up to ten sample names each.
    pub fn summary(&self) -> String {
        let mut out = String::new();
        out.push_str(&format!("path:    {}\n", self.path.display()));
        if let Some(parent) = &self.parent {
            out.push_str(&format!(
                "parent:  {} at file offset {:#x}, {:#x} bytes\n",
                parent.path.display(),
                parent.off,
                parent.len
            ));
        }
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
        if let Some(why) = self.refuses(Feature::Decompile) {
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
                format!("{:#x}", s.va.0),
                format!("{:#x}", s.vsize),
                format!("{:#x}", s.file_off.0),
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
        out.push_str(&self.relocs.render());
        if let Some(go) = &self.go {
            out.push_str(&go.render());
        }
        match &self.clr {
            Some(Ok(clr)) => out.push_str(&clr.render(self.image_base)),
            Some(Err(why)) => out.push_str(&format!(
                ".net:    a CLR runtime header, its metadata refused: {why}
"
            )),
            None => {}
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
        let text = Section::mapped(".text", 0x1000, 0, from_usize(PAGE), false, true);
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
            for share in [
                r"\\?\UNC\host\share\a.exe",
                r"\\host\share\a.exe",
                "//host/share/a.exe",
                r"\\?\unc\host\share\a.pdb",
            ] {
                let why = unusable_path(std::path::Path::new(share));
                assert!(
                    why.as_deref()
                        .is_some_and(|w| w.contains("names a network share")),
                    "{share}: {why:?}"
                );
                let refused = Program::load(std::path::Path::new(share))
                    .expect_err("a share is never opened");
                assert!(refused.to_string().contains("network share"), "{refused}");
            }
            assert!(
                !is_device(r"\\.\C:\tmp\a.exe"),
                "a drive path in the device space"
            );
            let dir = std::env::temp_dir();
            let refused = Program::load(&dir).expect_err("a directory is no program");
            assert!(refused.to_string().contains("is a directory"), "{refused}");
        }
        assert!(!is_device("control.dll"), "a real name starting with con");
        assert!(!is_device("com0"), "there is no COM0");
        assert!(!is_device("com10"), "nor a two-digit port");
        assert!(!is_device("borer.exe"));
        assert!(unusable_path(std::path::Path::new("")).is_some());
    }

    /// The section index answers what a scan of the table in file order does.
    ///
    /// However the sections nest or overlap, its rows do not overlap: a
    /// table of sections that all overlap one another costs a look-up one
    /// binary search, where a walk back over the rows visited every one of
    /// them.
    ///
    /// # Panics
    ///
    /// When a look-up differs from the scan, or the rows overlap.
    #[test]
    fn the_section_index_answers_as_a_scan_does() {
        use super::{Section, section_in};
        let mut sections: Vec<Section> = (0..2000u64)
            .map(|k| {
                let va = 0x1000 + (k % 37) * 0x100;
                let size = 0x10_0000 - k * 0x80;
                Section::mapped(&format!("s{k}"), va, 0, size, false, k % 3 == 0)
            })
            .collect();
        sections.push(Section::mapped("bss", 0x9000_0000, 0, 0, false, false));
        sections.push(Section::mapped("far", 0x8000_0000, 0, 0x100, false, false));
        let index = Program::index_sections(&sections);
        assert!(index.len() <= 2 * sections.len(), "{} rows", index.len());
        assert!(
            index.windows(2).all(|w| w[0].end <= w[1].va),
            "rows overlap"
        );
        let scan = |va: u64| {
            sections
                .iter()
                .find(|s| s.file_size > 0 && va >= s.va.0 && va - s.va.0 < s.vsize.max(s.file_size))
        };
        for va in (0..0x11_0000u64).step_by(0x3f).chain([
            0x8000_0000,
            0x8000_00ff,
            0x8000_0100,
            0x9000_0000,
            u64::MAX,
        ]) {
            assert_eq!(
                section_in(&sections, &index, va).map(|s| s.name.as_str()),
                scan(va).map(|s| s.name.as_str()),
                "{va:#x}"
            );
        }
    }

    /// A read by path takes only a regular file within its cap, judged
    /// before it is opened, so a pipe or a device never blocks or reads
    /// forever.
    ///
    /// # Panics
    ///
    /// When a directory, a device, a pipe or an oversized file is read.
    #[test]
    fn a_read_takes_only_a_regular_file_within_its_cap() {
        use super::read_regular;
        let dir = std::env::temp_dir().join(format!("borer-regular-{}", std::process::id()));
        std::fs::create_dir_all(&dir).expect("a temp dir");
        let file = dir.join("ten.txt");
        std::fs::write(&file, b"0123456789").expect("written");
        assert_eq!(
            read_regular(&file, 10).expect("within the cap"),
            b"0123456789"
        );
        let over = read_regular(&file, 9).expect_err("past the cap");
        assert!(over.to_string().contains("past the 9"), "{over}");
        let isdir = read_regular(&dir, u64::MAX).expect_err("a directory");
        assert!(isdir.to_string().contains("is a directory"), "{isdir}");
        #[cfg(unix)]
        {
            let device =
                read_regular(std::path::Path::new("/dev/zero"), u64::MAX).expect_err("a device");
            assert!(
                device.to_string().contains("not a regular file"),
                "{device}"
            );
            let fifo = dir.join("pipe");
            if std::process::Command::new("mkfifo")
                .arg(&fifo)
                .status()
                .is_ok_and(|s| s.success())
            {
                let pipe = read_regular(&fifo, u64::MAX).expect_err("a pipe");
                assert!(pipe.to_string().contains("not a regular file"), "{pipe}");
                assert!(Program::load(&fifo).is_err(), "a pipe is no program");
            }
        }
        std::fs::remove_dir_all(&dir).expect("cleans up");
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
