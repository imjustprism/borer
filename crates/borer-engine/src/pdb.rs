//! PDB debug symbols: the names a PE's companion PDB holds.
//!
//! A PE built with debug information carries a `CodeView` record naming the
//! PDB it was linked with: the path the linker wrote, the build's GUID and
//! an age. Reading that PDB names every function the compiler saw, the way
//! [`crate::dwarf`] does for a binary that carries its DWARF inside, and
//! for the same reason it is a fact rather than a guess: the linker wrote
//! the name down.
//!
//! This reads the subset that answers "what is this function called",
//! "where does it end", "what does it take" and "what lives at this
//! address": the PDB information stream (checked against the record, so a
//! PDB from another build is never applied to this one), the symbols with
//! an address - module procedures and thunks, then the publics marked
//! function or code - the procedure extents, which join the program's
//! function ranges where an executable section holds them whole, the
//! signatures the type stream states, which join the debug functions the
//! way the DWARF ones do, and the data records - module data and the
//! publics marked neither function nor code - which join the symbol list
//! as data symbols where a non-executable section maps them, naming the
//! globals the decompiler would otherwise synthesize `gN_` names for.
//! The line programs are read one row deep and only on ask: the file and
//! line each procedure starts at ([`sources`]), paid by the first header
//! that states one. A procedure's frame-relative locals - the records
//! between its own and the scope's end - name the decompiler's stack
//! slots, so `alpha` renders where `local_8` otherwise would.

use crate::dwarf::{frame_slot, local_name_ok};
use crate::program::{Section, Symbol, SymbolKind};
use std::collections::BTreeMap;
use std::io::Cursor;
use std::path::{Path, PathBuf};

/// Most PDB symbols applied, whatever the file holds.
///
/// A Windows component's full PDB names a few hundred thousand functions;
/// past half a million the gather stops taking and counts the rest, told
/// as `+N more` the way every capped listing says what it cut. The import
/// and export caps are sixteen bits, too small for a debug build's
/// statics; this sits a grain under the relocation cap's million words.
const SYMBOLS_MAX: usize = 1 << 19;

/// `S_FRAMEPROC`: the frame facts that follow a procedure record, whose
/// first word is the frame's size in bytes.
const S_FRAMEPROC: u16 = 0x1012;
/// `S_BPREL32`: a local at an offset from the frame pointer register.
const S_BPREL32: u16 = 0x110b;
/// `S_DEFRANGE_FRAMEPOINTER_REL`: the live range of an `S_LOCAL` at an
/// offset from the frame's base.
const S_DEFRANGE_FRAMEPOINTER_REL: u16 = 0x1142;
/// `S_DEFRANGE_REGISTER_REL`: the live range of an `S_LOCAL` at an offset
/// from a named register.
const S_DEFRANGE_REGISTER_REL: u16 = 0x1145;

/// The frame pointer register of an Intel frame, either width: `CV_REG_EBP`
/// and `CV_AMD64_RBP` as the crate hands them back, plain numbers.
const FRAME_PTR: [u16; 2] = [22, 334];
/// The stack pointer register of an Intel frame, either width:
/// `CV_REG_ESP` and `CV_AMD64_RSP`.
const STACK_PTR: [u16; 2] = [21, 335];

/// The `CodeView` PDB70 record a PE's debug directory states, owned.
#[derive(Debug, Clone)]
pub struct Record {
    /// The PDB path as recorded, one line: the linker usually writes the
    /// absolute path of the machine that built the image.
    pub path: String,
    /// The build's GUID as the sixteen bytes the record holds: a
    /// little-endian `u32`, two little-endian `u16`s, then eight raw bytes.
    pub guid: [u8; 16],
    /// How many times the PDB was written when the image was linked.
    pub age: u32,
}

impl Record {
    /// Reads the record out of a parsed PE's debug data.
    ///
    /// # Arguments
    ///
    /// * `cv` - The debug directory's `CodeView` PDB70 entry.
    ///
    /// # Returns
    ///
    /// The record with its path made one line, the same defense every name
    /// out of a file gets, so a path holding a newline cannot forge a row.
    pub fn from_debug_info(cv: &goblin::pe::debug::CodeviewPDB70DebugInfo<'_>) -> Self {
        Self {
            path: crate::text::one_line(
                String::from_utf8_lossy(cv.filename).trim_end_matches('\0'),
            ),
            guid: cv.signature,
            age: cv.age,
        }
    }

    /// The string a symbol server files this PDB under.
    ///
    /// The GUID as its 32 uppercase hex digits with no dashes, then the age
    /// in uppercase hex: the same pair the information-stream check
    /// ([`matches_record`]) accepts, spelled the way the public symbol
    /// store's paths spell it. A cache that holds `{name}/{key}/{name}`
    /// under its root and a download URL that asks for the same are both
    /// built from this one string.
    ///
    /// # Returns
    ///
    /// The key: 33 or more characters, from the record's own pair whatever
    /// the recorded path says.
    #[must_use]
    pub fn symsrv_key(&self) -> String {
        let g = &self.guid;
        let tail: String = g[8..].iter().map(|b| format!("{b:02X}")).collect();
        format!(
            "{:08X}{:04X}{:04X}{tail}{:X}",
            u32::from_le_bytes([g[0], g[1], g[2], g[3]]),
            u16::from_le_bytes([g[4], g[5]]),
            u16::from_le_bytes([g[6], g[7]]),
            self.age
        )
    }
}

/// What applying the PDB a record named did.
///
/// Held as [`crate::program::Program::pdb`] and rendered by the summary and
/// the triage, so a load that found a PDB says what it took from it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Outcome {
    /// The PDB matched the record and its symbols were applied.
    Applied {
        /// Symbols inserted into the program's symbol list: the functions
        /// as locals, the data as data symbols.
        named: usize,
        /// Symbols past [`SYMBOLS_MAX`] the gather dropped, said as
        /// `+N more`.
        dropped: usize,
    },
    /// The PDB was found but not applied, and why; nothing changed.
    Skipped(Skip),
}

/// Why a found PDB was not applied.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Skip {
    /// The file is no PDB a parser can read: empty, damaged or locked.
    Unreadable,
    /// The PDB's information stream states another build's GUID or age, so
    /// its names describe a different image than the one under analysis.
    Mismatch,
}

impl Outcome {
    /// Renders the outcome as one line without its prefix.
    ///
    /// # Returns
    ///
    /// `1234 symbols applied (+56 more)` for an applied PDB, or
    /// `skipped: ...` naming why one that was found was left alone.
    pub fn render(&self) -> String {
        match *self {
            Self::Applied { named, dropped } => {
                let more = if dropped == 0 {
                    String::new()
                } else {
                    format!(" (+{dropped} more)")
                };
                format!("{named} symbols applied{more}")
            }
            Self::Skipped(Skip::Unreadable) => "skipped: unreadable".to_owned(),
            Self::Skipped(Skip::Mismatch) => {
                "skipped: guid/age mismatch, another build's pdb".to_owned()
            }
        }
    }
}

/// The paths a record's PDB may be at, in try order.
///
/// Three places: the recorded path when it is absolute (the linker's own
/// machine, so a build tree that still exists names its PDB wherever it
/// sits), the recorded file name beside the loaded binary (a PDB shipped
/// next to its image), and the `{name}/{guid+age}/{name}` entry a symbol
/// server client caches under a root the caller names, last, so a build
/// tree or a shipped file always wins over a download. Nothing relative to
/// the working directory is tried, which would make the answer depend on
/// where the engine was run from. The file name is what follows the last
/// `\` or `/`, since a record written on Windows names a Windows path that
/// another host's [`Path`] reads as one component.
///
/// # Arguments
///
/// * `record` - The image's debug record.
/// * `binary` - The path the image was loaded from.
/// * `symsrv` - The root of a symbol-server cache, `None` when the caller
///   keeps no cache.
///
/// # Returns
///
/// The candidates, in try order; the cache entry only when the record
/// states a file name.
fn candidates(record: &Record, binary: &Path, symsrv: Option<&Path>) -> Vec<PathBuf> {
    let recorded = Path::new(&record.path);
    let mut out = Vec::new();
    if recorded.is_absolute() {
        out.push(recorded.to_path_buf());
    }
    let name = record.path.rsplit(['/', '\\']).next().unwrap_or_default();
    if !matches!(name, "" | "." | "..") {
        if let Some(dir) = binary.parent() {
            out.push(dir.join(name));
        }
        if let Some(root) = symsrv {
            out.push(root.join(name).join(record.symsrv_key()).join(name));
        }
    }
    out
}

/// Whether a PDB's information stream names the build a record does.
///
/// # Arguments
///
/// * `guid` - The stream's GUID as its four fields, which is how the crate
///   hands it back; the crate reads each field little-endian off the
///   stream, so a field equals the same little-endian bytes of the record.
/// * `age` - The stream's age.
/// * `record` - The image's debug record.
///
/// # Returns
///
/// Whether both the GUID and the age are the record's: the same pair a
/// symbol server files a PDB under, so an equal pair is the one build.
fn matches_record(guid: (u32, u16, u16, &[u8; 8]), age: u32, record: &Record) -> bool {
    let (d1, d2, d3, d4) = guid;
    let g = &record.guid;
    age == record.age
        && d1.to_le_bytes() == g[0..4]
        && d2.to_le_bytes() == g[4..6]
        && d3.to_le_bytes() == g[6..8]
        && *d4 == g[8..16]
}

/// Whether a PDB's bytes name the build a record does, without applying it.
///
/// The gate a symbol-server download is held to: the file is worth caching
/// only when it is the build the image's record names, so a wrong or
/// hostile download is refused before anything reads its symbols. The
/// check is [`matches_record`], the one [`apply`] runs on a companion it
/// found on disk.
///
/// # Arguments
///
/// * `bytes` - The whole PDB file, as downloaded.
/// * `record` - The image's `CodeView` PDB70 debug record.
///
/// # Returns
///
/// `Some(true)` when the information stream states the record's GUID and
/// age, `Some(false)` when it states another build's, `None` when the file
/// is no PDB a parser can read.
pub fn identifies(bytes: &[u8], record: &Record) -> Option<bool> {
    let mut db = pdb::PDB::open(Cursor::new(bytes)).ok()?;
    let info = db.pdb_information().ok()?;
    Some(matches_record(info.guid.as_fields(), info.age, record))
}

/// Applies the PDB a debug record names, when one is on disk to apply.
///
/// The PDB is resolved through [`resolved`] and read whole; its
/// information stream must state the record's GUID and age
/// ([`matches_record`]), and one that does not is skipped with a note
/// rather than applied to an image it does not describe. A walk that runs
/// into a damaged stream keeps the symbols gathered so far: a corrupt PDB
/// answers with part of the truth, never a panic. The line programs are
/// left for [`sources`]: no load answers from them, and every one of them
/// costs a load seconds it would not otherwise spend.
///
/// # Arguments
///
/// * `binary` - The path the image was loaded from.
/// * `symsrv` - The root of a symbol-server cache, the third place a
///   companion is looked for ([`candidates`]); `None` keeps the two
///   on-disk places.
/// * `record` - The image's `CodeView` PDB70 debug record.
/// * `image_base` - The image's preferred load base, added to every RVA.
/// * `word` - The stack word in bytes, which the locals' frame-relative
///   offsets convert through.
/// * `sections` - The image's sections; an extent lands only inside one
///   executable section, whole ([`extent_va`]).
/// * `symbols` - The program's symbol list, appended to as
///   [`SymbolKind::Local`] the way the DWARF names are, and as
///   [`SymbolKind::Data`] for the data records a non-executable section
///   maps.
/// * `ranges` - The program's function ranges, appended to by the extents
///   the image holds whole.
/// * `subs` - The program's debug functions, appended to by the signatures
///   the type stream states, for the decompiler's headers, each with the
///   frame-relative locals its module states naming its stack slots.
///
/// # Returns
///
/// The outcome when a PDB file was found at a candidate path, `None` when
/// none was: nothing was read and nothing changed.
#[expect(
    clippy::too_many_arguments,
    reason = "the load hands apply every collection the PDB fills; a struct for one call site would hide which is which"
)]
pub(crate) fn apply(
    binary: &Path,
    symsrv: Option<&Path>,
    record: &Record,
    image_base: u64,
    word: i64,
    sections: &[Section],
    symbols: &mut Vec<Symbol>,
    ranges: &mut Vec<(u64, u64)>,
    subs: &mut Vec<crate::dwarf::Subprogram>,
) -> Option<Outcome> {
    let mut phases = crate::timing::Phases::new();
    let path = candidates(record, binary, symsrv)
        .into_iter()
        .find(|p| p.is_file())?;
    let unreadable = || Some(Outcome::Skipped(Skip::Unreadable));
    let Ok(bytes) = std::fs::read(&path) else {
        return unreadable();
    };
    phases.mark("pdb read");
    let Ok(mut db) = pdb::PDB::open(Cursor::new(bytes.as_slice())) else {
        return unreadable();
    };
    phases.mark("pdb open");
    let Ok(info) = db.pdb_information() else {
        return unreadable();
    };
    if !matches_record(info.guid.as_fields(), info.age, record) {
        return Some(Outcome::Skipped(Skip::Mismatch));
    }
    let Ok(map) = db.address_map() else {
        return unreadable();
    };
    let gathered = gather(&mut db, &map, word, false);
    phases.mark("pdb gather");
    let named = insert(image_base, &gathered.found, symbols);
    let data = insert_data(
        image_base,
        &gathered.found,
        &gathered.data,
        sections,
        symbols,
    );
    for (&rva, &end) in &gathered.extents {
        if let Some(va) = extent_va(image_base, rva, end, sections) {
            ranges.push(va);
        }
    }
    phases.mark("pdb insert");
    let sigs = signatures(&mut db, &gathered.types);
    phases.mark("pdb signatures");
    for (rva, name) in &gathered.found {
        let Some(sig) = sigs.get(rva) else {
            continue;
        };
        subs.push(crate::dwarf::Subprogram {
            low_pc: image_base + u64::from(*rva),
            name: name.clone(),
            parameters: sig
                .params
                .iter()
                .map(|t| crate::dwarf::Parameter {
                    name: String::new(),
                    type_name: Some(crate::text::one_line(t)),
                })
                .collect(),
            return_type: sig.ret.as_deref().map(crate::text::one_line),
            locals: gathered.locals.get(rva).cloned().unwrap_or_default(),
        });
    }
    Some(Outcome::Applied {
        named: named + data,
        dropped: gathered.dropped,
    })
}

/// The path a record's PDB resolved to, when one is on disk to apply.
///
/// # Arguments
///
/// * `binary` - The path the image was loaded from.
/// * `record` - The image's `CodeView` PDB70 debug record.
///
/// # Returns
///
/// The first candidate that names a file, or `None` when none does.
pub(crate) fn resolved(binary: &Path, record: &Record, symsrv: Option<&Path>) -> Option<PathBuf> {
    candidates(record, binary, symsrv)
        .into_iter()
        .find(|p| p.is_file())
}

/// Reads the source file and line each named procedure starts at, the
/// walk a load defers until a `// source:` line is asked for.
///
/// A full PDB's line programs cost seconds to parse and no load answers
/// from them, so [`apply`] leaves them out and this re-opens the same
/// resolved file, checks it against the same record, and walks the same
/// gather with its line programs on: the caller memoizes the result, so
/// the seconds are paid once, at the first function whose header states a
/// source. A PDB that no longer matches its record - replaced on disk
/// since the load - states nothing, and a caller that keeps the empty
/// answer answers the same bytes for the analysis's life either way.
///
/// # Arguments
///
/// * `binary` - The path the image was loaded from.
/// * `record` - The image's `CodeView` PDB70 debug record.
/// * `symsrv` - The symbol-server cache root, the third place a resolved
///   companion can live.
/// * `image_base` - The image's preferred load base, added to every RVA.
/// * `word` - The stack word in bytes, for the gather this re-runs.
///
/// # Returns
///
/// Function entry to the `(file, line)` its first row states, or `None`
/// when no PDB is on disk or the one there no longer matches the record.
pub(crate) fn sources(
    binary: &Path,
    record: &Record,
    symsrv: Option<&Path>,
    image_base: u64,
    word: i64,
) -> Option<BTreeMap<u64, (String, u32)>> {
    let path = resolved(binary, record, symsrv)?;
    let unreadable = || None;
    let Ok(bytes) = std::fs::read(&path) else {
        return unreadable();
    };
    let Ok(mut db) = pdb::PDB::open(Cursor::new(bytes.as_slice())) else {
        return unreadable();
    };
    let Ok(info) = db.pdb_information() else {
        return unreadable();
    };
    if !matches_record(info.guid.as_fields(), info.age, record) {
        return unreadable();
    }
    let Ok(map) = db.address_map() else {
        return unreadable();
    };
    let gathered = gather(&mut db, &map, word, true);
    let rows = resolve_lines(&mut db, &gathered.lines);
    Some(
        rows.into_iter()
            .map(|(rva, fl)| (image_base + u64::from(rva), fl))
            .collect(),
    )
}

/// Maps a data record's RVA to the virtual address a non-executable
/// section holds.
///
/// The linker lays a static, a global or a string constant in a data
/// section, so a record that lands in an executable one - or in no section
/// at all - describes nothing this image's data lives at, a shifted or
/// hostile PDB, and is refused rather than named onto code, the same
/// discipline the procedure extents get. Refusing executable sections is
/// also what keeps a data record from ever shadowing a function's name:
/// every function the analysis finds sits in executable memory.
///
/// # Arguments
///
/// * `image_base` - The image's preferred load base, added to the RVA.
/// * `rva` - Where the data sits, image-relative.
/// * `sections` - The image's sections.
///
/// # Returns
///
/// The virtual address, or `None` when no non-executable section's span
/// holds it.
fn data_va(image_base: u64, rva: u32, sections: &[Section]) -> Option<u64> {
    let va = image_base.checked_add(u64::from(rva))?;
    sections.iter().find_map(|s| {
        let limit = s.va.checked_add(s.vsize.max(s.file_size))?;
        (!s.executable && va >= s.va && va < limit).then_some(va)
    })
}

/// Maps a procedure's extent to virtual addresses an executable section
/// holds whole.
///
/// The DBI states extents as an RVA and a length, and the linker that wrote
/// them laid each procedure inside one section; an extent that crosses a
/// section boundary, lands in data, or runs past a section's end describes
/// no code this image holds - a shifted or hostile PDB - and is refused
/// rather than trimmed to what fits, the same discipline the exception
/// table's entries get.
///
/// # Arguments
///
/// * `image_base` - The image's preferred load base, added to the RVA.
/// * `rva` - Where the procedure starts, image-relative; its caller has
///   already refused one that is unmapped.
/// * `end` - Where the procedure ends, image-relative and exclusive, past
///   `rva`.
/// * `sections` - The image's sections.
///
/// # Returns
///
/// The `(start, end)` virtual addresses, or `None` when no executable
/// section's span holds the extent whole.
fn extent_va(image_base: u64, rva: u32, end: u32, sections: &[Section]) -> Option<(u64, u64)> {
    let start = image_base.checked_add(u64::from(rva))?;
    let end = image_base.checked_add(u64::from(end))?;
    sections.iter().find_map(|s| {
        let limit = s.va.checked_add(s.vsize.max(s.file_size))?;
        (s.executable && start >= s.va && start < limit && end <= limit).then_some((start, end))
    })
}

/// The symbols gathered from a PDB, with the cap told as a count.
#[derive(Debug, Default)]
struct Gathered {
    /// RVA to name; a `BTreeMap` so what is taken is fixed by the
    /// addresses, not by the order the streams happen to list them in.
    found: BTreeMap<u32, String>,
    /// RVA to name, for the records that mark data; the same fixed
    /// address order, kept apart from [`Gathered::found`] so a data name
    /// never occupies an address a function name wants.
    data: BTreeMap<u32, String>,
    /// RVA to exclusive end RVA, for the procedures that state a length;
    /// taken under the same cap and the same fixed address order.
    extents: BTreeMap<u32, u32>,
    /// RVA to the type index a named procedure names, for the signature
    /// walk; only a named procedure has a header to render one in.
    types: BTreeMap<u32, pdb::TypeIndex>,
    /// RVA to the winning line row so far, as its offset in the image, the
    /// file's reference into the string table and its line; the names
    /// resolve once the modules are walked. Only a procedure the gather
    /// sized has an entry.
    lines: BTreeMap<u32, (u32, pdb::StringRef, u32)>,
    /// Procedure RVA to its locals, as slot offset to name: the
    /// frame-relative records its module states, converted into the
    /// decompiler's frame. Only a procedure the gather named has an entry,
    /// and a local whose offset converts past [`crate::dwarf::FRAME_SPAN`]
    /// is refused.
    locals: BTreeMap<u32, BTreeMap<i64, String>>,
    /// Real candidates past the cap, counted so the cut can be said.
    dropped: usize,
    /// How many symbols to take, [`SYMBOLS_MAX`] on a real gather.
    max: usize,
}

impl Gathered {
    /// Takes one symbol, or counts it when the gather is full.
    ///
    /// The extent is taken with the name, so a procedure past the cap loses
    /// both and one under it keeps both: the two facts describe the same
    /// function, and neither outlives the other.
    ///
    /// # Arguments
    ///
    /// * `rva` - Where the symbol sits, image-relative; `None` or `0` when
    ///   the PDB maps it to no address the image holds.
    /// * `name` - The symbol's decorated name.
    /// * `len` - The symbol's length in bytes when it states one, as the
    ///   procedure and thunk records do; `None` or `0` when it does not.
    /// * `ty` - The type index a procedure record names, for the signature
    ///   walk; `None` when the record states no type.
    fn take(
        &mut self,
        rva: Option<u32>,
        name: pdb::RawString<'_>,
        len: Option<u32>,
        ty: Option<pdb::TypeIndex>,
    ) {
        let Some(rva) = rva.filter(|r| *r != 0) else {
            return;
        };
        if self.found.contains_key(&rva) {
            return;
        }
        if self.found.len() >= self.max {
            self.dropped += 1;
            return;
        }
        if let Some(end) = len.filter(|l| *l != 0).and_then(|l| rva.checked_add(l))
            && end > rva
        {
            self.extents.insert(rva, end);
        }
        let name = name.to_string();
        if name.is_empty() {
            return;
        }
        // INVARIANT: an index under `0x1000` names a primitive, and no
        // procedure's signature is one.
        if let Some(t) = ty.filter(|t| t.0 >= 0x1000) {
            self.types.insert(rva, t);
        }
        self.found.insert(rva, name.into_owned());
    }

    /// Takes one data record, or counts it when the gather is full.
    ///
    /// Data shares the cap with the functions - both are symbols the PDB
    /// applies - and an address a function already took is left to it: a
    /// record pair that disagrees about one address is settled for the
    /// code, which the module stream stated with a size the data record
    /// has no counterpart of.
    ///
    /// # Arguments
    ///
    /// * `rva` - Where the data sits, image-relative; `None` or `0` when
    ///   the PDB maps it to no address the image holds.
    /// * `name` - The record's decorated name.
    fn take_data(&mut self, rva: Option<u32>, name: pdb::RawString<'_>) {
        let Some(rva) = rva.filter(|r| *r != 0) else {
            return;
        };
        if self.found.contains_key(&rva) || self.data.contains_key(&rva) {
            return;
        }
        if self.found.len() + self.data.len() >= self.max {
            self.dropped += 1;
            return;
        }
        let name = name.to_string();
        if !name.is_empty() {
            self.data.insert(rva, name.into_owned());
        }
    }

    /// Takes one frame-relative local for the procedure being walked,
    /// through the contract both debug readers insert by
    /// ([`crate::dwarf::take_local`]).
    ///
    /// # Arguments
    ///
    /// * `rva` - The procedure the local belongs to, image-relative.
    /// * `slot` - The converted slot offset; `None` refuses the record.
    /// * `name` - The local's name, already checked by
    ///   [`crate::dwarf::local_name_ok`].
    fn take_local(&mut self, rva: u32, slot: Option<i64>, name: &str) {
        if let Some(map) = self.locals.get_mut(&rva) {
            crate::dwarf::take_local(map, slot, name);
        }
    }

    /// Takes the first line row each stated procedure starts at.
    ///
    /// Rows are asked of the module's own program by the offset its
    /// records state, and are not promised to be in offset order, so the
    /// winner is the row with the least offset inside the procedure's
    /// extent, ties by the lesser line. Only a procedure the gather sized
    /// has an extent to place rows in; a row outside it, a zero line, or a
    /// file the program does not name contributes nothing.
    ///
    /// # Arguments
    ///
    /// * `program` - The module's line program.
    /// * `map` - The address map, translating the internal offsets the
    ///   rows state into image RVAs.
    /// * `procs` - The procedures this module states, RVA and record
    ///   offset.
    fn take_lines(
        &mut self,
        program: &pdb::LineProgram<'_>,
        map: &pdb::AddressMap<'_>,
        procs: &[(u32, pdb::PdbInternalSectionOffset)],
    ) {
        use pdb::FallibleIterator as _;
        for &(rva, offset) in procs {
            let Some(&end) = self.extents.get(&rva) else {
                continue;
            };
            let mut rows = program.lines_for_symbol(offset);
            while let Ok(Some(row)) = rows.next() {
                let Some(at) = row.offset.to_rva(map).map(|rva| rva.0) else {
                    continue;
                };
                if at < rva || at >= end || row.line_start == 0 {
                    continue;
                }
                if self.lines.get(&rva).is_some_and(|&(best, _, line)| {
                    best < at || (best == at && line <= row.line_start)
                }) {
                    continue;
                }
                if let Ok(file) = program.get_file_info(row.file_index) {
                    self.lines.insert(rva, (at, file.name, row.line_start));
                }
            }
        }
    }
}

/// Reads how far a procedure's frame reaches below the entry stack
/// pointer, from its frame record.
///
/// The record states the frame's size in bytes and, a field later, the
/// bytes its prologue pushed to save callee registers: the writer of both
/// counts the pushes in the frame's size only to leave them out of the
/// field, so the distance the frame reaches is the two added. A local a
/// stack-pointer-relative record names sits that far below entry.
///
/// # Arguments
///
/// * `raw` - The `S_FRAMEPROC` record's raw bytes, kind included.
///
/// # Returns
///
/// The frame's reach in bytes, or `None` when the record is too short to
/// state it.
fn frame_size(raw: &[u8]) -> Option<i64> {
    let word = |at: usize| -> Option<i64> {
        Some(i64::from(u32::from_le_bytes(
            raw.get(at..at.checked_add(4)?)?.try_into().ok()?,
        )))
    };
    word(2)?.checked_add(word(14)?)
}

/// Reads the offset a frame-pointer-relative live range states.
///
/// # Arguments
///
/// * `raw` - The `S_DEFRANGE_FRAMEPOINTER_REL` record's raw bytes, kind
///   included.
///
/// # Returns
///
/// The offset from the frame's base, or `None` when the record is too
/// short to state one.
fn defrange_offset(raw: &[u8]) -> Option<i32> {
    let four = raw.get(2..6)?;
    Some(i32::from_le_bytes(four.try_into().ok()?))
}

/// Reads the register and offset a register-relative live range states.
///
/// # Arguments
///
/// * `raw` - The `S_DEFRANGE_REGISTER_REL` record's raw bytes, kind
///   included.
///
/// # Returns
///
/// The register and the offset from it, or `None` when the record is too
/// short to state them.
fn defrange_register(raw: &[u8]) -> Option<(u16, i32)> {
    let reg = u16::from_le_bytes(raw.get(2..4)?.try_into().ok()?);
    let off = i32::from_le_bytes(raw.get(6..10)?.try_into().ok()?);
    Some((reg, off))
}

/// Reads the offset and name a frame-pointer-relative local states.
///
/// # Arguments
///
/// * `raw` - The `S_BPREL32` record's raw bytes, kind included.
///
/// # Returns
///
/// The offset from the frame pointer register and the name, or `None`
/// when the record is too short to state them or names nothing.
fn bprel32(raw: &[u8]) -> Option<(i32, &str)> {
    let off = i32::from_le_bytes(raw.get(2..6)?.try_into().ok()?);
    let name = raw.get(10..)?;
    let end = name.iter().position(|&b| b == 0).unwrap_or(name.len());
    let name = std::str::from_utf8(&name[..end]).ok()?;
    (!name.is_empty()).then_some((off, name))
}

/// A scope the module's symbol stream is inside, for the locals walk.
#[derive(Debug)]
enum Scope {
    /// The procedure being walked, at its RVA, whose locals are gathered.
    Proc(u32),
    /// A nested scope of the procedure's own - a block or a thunk - whose
    /// locals still live in its frame.
    Nested,
    /// An inline site: the locals inside belong to the inlinee's frame,
    /// not the procedure's.
    Inline,
}

/// Reads the named symbols a PDB states, by RVA.
///
/// Module procedures and thunks go in first: they carry the sizes and name
/// the statics, so where a public overlaps one the module's name wins. The
/// publics marked function or code fill the addresses still open. The data
/// records - the module's own, then the publics marked neither function
/// nor code - go into a map of their own, so a data name and a function
/// name never contend for one address inside the PDB. When `want_lines`
/// asks, each module's line program is parsed and asked for the first row
/// of every procedure it states - the one part of the walk a load does
/// not pay, deferred to [`sources`] - and the records between a procedure
/// and its scope's end name its locals,
/// an inline site's own records excepted: they belong to the inlinee's
/// frame, not the procedure's. An error from a damaged stream ends that
/// walk and keeps what was gathered.
///
/// # Arguments
///
/// * `db` - The opened PDB.
/// * `map` - Its address map, translating the internal offsets the symbols
///   state into image RVAs.
/// * `word` - The stack word in bytes, which the locals' frame-relative
///   offsets convert through.
/// * `want_lines` - Whether to parse the modules' line programs, the walk
///   [`sources`] pays and a load does not.
///
/// # Returns
///
/// The gathered symbols, extents and how many candidates the cap dropped.
fn gather<'s>(
    db: &mut pdb::PDB<'s, Cursor<&'s [u8]>>,
    map: &pdb::AddressMap<'s>,
    word: i64,
    want_lines: bool,
) -> Gathered {
    use pdb::FallibleIterator as _;
    let mut out = Gathered {
        max: SYMBOLS_MAX,
        ..Gathered::default()
    };
    if let Ok(dbi) = db.debug_information()
        && let Ok(mut modules) = dbi.modules()
    {
        while let Ok(Some(m)) = modules.next() {
            let Ok(Some(info)) = db.module_info(&m) else {
                continue;
            };
            let Ok(mut syms) = info.symbols() else {
                continue;
            };
            // The procedures this module states, for the line lookups: a
            // module's line program answers by the internal offsets its own
            // records state, which leave with the module.
            let mut procs: Vec<(u32, pdb::PdbInternalSectionOffset)> = Vec::new();
            // The scope stack the locals belong to: a procedure's records
            // end at its scope's end, a block inside it keeps its frame, and
            // an inline site's own locals belong to the frame it inlined,
            // not this procedure's.
            let mut scopes: Vec<Scope> = Vec::new();
            let mut frame = 0i64;
            let mut pending: Option<String> = None;
            let mut taken = 0usize;
            let current_proc = |scopes: &[Scope]| {
                scopes.iter().rev().find_map(|s| match s {
                    Scope::Proc(rva) => Some(*rva),
                    Scope::Nested | Scope::Inline => None,
                })
            };
            let take =
                |out: &mut Gathered, rva: u32, slot: Option<i64>, name: &str, taken: &mut usize| {
                    if *taken >= SYMBOLS_MAX {
                        return;
                    }
                    let before = out.locals.get(&rva).map_or(0, BTreeMap::len);
                    out.take_local(rva, slot, name);
                    *taken += out.locals.get(&rva).map_or(0, BTreeMap::len) - before;
                };
            while let Ok(Some(s)) = syms.next() {
                let kind = s.raw_kind();
                let inlined = scopes.iter().any(|s| matches!(s, Scope::Inline));
                if s.starts_scope() {
                    match s.parse() {
                        Ok(pdb::SymbolData::Procedure(p)) => {
                            let rva = p.offset.to_rva(map).map(|rva| rva.0);
                            if let Some(rva) = rva {
                                procs.push((rva, p.offset));
                            }
                            out.take(rva, p.name, Some(p.len), Some(p.type_index));
                            frame = 0;
                            match rva.filter(|r| *r != 0 && out.found.contains_key(r)) {
                                Some(rva) => {
                                    out.locals.entry(rva).or_default();
                                    scopes.push(Scope::Proc(rva));
                                }
                                None => scopes.push(Scope::Nested),
                            }
                        }
                        Ok(pdb::SymbolData::Thunk(t)) => {
                            out.take(
                                t.offset.to_rva(map).map(|rva| rva.0),
                                t.name,
                                Some(u32::from(t.len)),
                                None,
                            );
                            scopes.push(Scope::Nested);
                        }
                        Ok(pdb::SymbolData::InlineSite(_)) => scopes.push(Scope::Inline),
                        _ => scopes.push(Scope::Nested),
                    }
                    pending = None;
                } else if s.ends_scope() {
                    scopes.pop();
                    pending = None;
                } else if !inlined && kind == S_FRAMEPROC {
                    frame = frame_size(s.raw_bytes()).unwrap_or(frame);
                    pending = None;
                } else if !inlined && kind == S_BPREL32 {
                    if let Some((off, name)) = bprel32(s.raw_bytes())
                        && local_name_ok(name)
                        && let Some(rva) = current_proc(&scopes)
                    {
                        take(
                            &mut out,
                            rva,
                            frame_slot(off, true, word, frame),
                            name,
                            &mut taken,
                        );
                    }
                    pending = None;
                } else if !inlined && let Some(name) = &pending {
                    let range = match kind {
                        // The record names no register: a negative offset
                        // sits below the frame pointer a frame that has
                        // one, a non-negative one above the stack pointer
                        // a frame-pointer-less frame's prologue left.
                        S_DEFRANGE_FRAMEPOINTER_REL => {
                            defrange_offset(s.raw_bytes()).map(|off| (off < 0, off))
                        }
                        S_DEFRANGE_REGISTER_REL => defrange_register(s.raw_bytes())
                            .and_then(|(reg, off)| base_kind(reg).map(|b| (b, off))),
                        _ => None,
                    };
                    if let (Some(rva), Some((base_bp, off))) = (current_proc(&scopes), range) {
                        take(
                            &mut out,
                            rva,
                            frame_slot(off, base_bp, word, frame),
                            name,
                            &mut taken,
                        );
                    }
                    if !matches!(kind, S_DEFRANGE_FRAMEPOINTER_REL | S_DEFRANGE_REGISTER_REL) {
                        pending = None;
                    }
                } else if !inlined {
                    let relative = s.parse().ok().and_then(|d| match d {
                        pdb::SymbolData::Data(d) => {
                            out.take_data(d.offset.to_rva(map).map(|rva| rva.0), d.name);
                            None
                        }
                        pdb::SymbolData::RegisterRelative(r) => base_kind(r.register.0)
                            .filter(|_| local_name_ok(r.name.to_string().as_ref()))
                            .map(|base_bp| (base_bp, r.offset, r.name.to_string().into_owned())),
                        pdb::SymbolData::Local(l) => {
                            pending = (!l.flags.isparam
                                && local_name_ok(l.name.to_string().as_ref()))
                            .then(|| l.name.to_string().into_owned());
                            None
                        }
                        _ => None,
                    });
                    if let Some((base_bp, off, name)) = relative
                        && let Some(rva) = current_proc(&scopes)
                    {
                        take(
                            &mut out,
                            rva,
                            frame_slot(off, base_bp, word, frame),
                            &name,
                            &mut taken,
                        );
                    }
                }
            }
            if want_lines
                && !procs.is_empty()
                && let Ok(program) = info.line_program()
            {
                out.take_lines(&program, map, &procs);
            }
        }
    }
    if let Ok(globals) = db.global_symbols() {
        let mut it = globals.iter();
        while let Ok(Some(s)) = it.next() {
            if let Ok(pdb::SymbolData::Public(p)) = s.parse() {
                let rva = p.offset.to_rva(map).map(|rva| rva.0);
                if p.function || p.code {
                    out.take(rva, p.name, None, None);
                } else {
                    out.take_data(rva, p.name);
                }
            }
        }
    }
    out
}

/// Which frame base a register names, when it names one the locals read.
///
/// # Arguments
///
/// * `reg` - The register number the record states, as the crate hands it
///   back.
///
/// # Returns
///
/// `Some(true)` for the frame pointer register, `Some(false)` for the
/// stack pointer one, `None` for every other: a local held anywhere else
/// states no slot the decompiler's frame knows.
fn base_kind(reg: u16) -> Option<bool> {
    if FRAME_PTR.contains(&reg) {
        Some(true)
    } else if STACK_PTR.contains(&reg) {
        Some(false)
    } else {
        None
    }
}

/// Most parameters one signature lists, whatever the type stream claims.
///
/// A hostile arglist record can name tens of thousands of type indices, and
/// the signature feeds the decompiler's arity floor and its header text
/// verbatim, so the list is cut where a real one ends: no Windows or Rust
/// function declares more than a dozen.
const PARAMS_MAX: usize = 16;

/// How far a type chain is resolved before it is called circular, the same
/// depth the DWARF chains get.
const TYPE_DEPTH: u32 = 16;

/// The signature one procedure's type states.
#[derive(Debug, Default, PartialEq, Eq)]
struct Signature {
    /// The return type as C source; `None` for `void` or unresolved.
    ret: Option<String>,
    /// Each parameter's type as C source, in order; `this` leads the list
    /// for a member function, the way a DWARF method's `self` is a formal
    /// parameter of its own.
    params: Vec<String>,
}

/// Reads the signatures the type stream states for the gathered procedures.
///
/// The type stream is walked once, end to end, so every index is findable
/// however the stream orders what a procedure references; a walk a damaged
/// stream ends keeps the types it passed, and each procedure's index is
/// resolved through what was kept. An index that does not resolve to a
/// signature the stream backs contributes nothing, never a guess.
///
/// # Arguments
///
/// * `db` - The opened PDB.
/// * `types` - RVA to the type index each gathered procedure names.
///
/// # Returns
///
/// RVA to signature, for the procedures whose types resolved.
fn signatures<'s>(
    db: &mut pdb::PDB<'s, Cursor<&'s [u8]>>,
    types: &BTreeMap<u32, pdb::TypeIndex>,
) -> BTreeMap<u32, Signature> {
    use pdb::FallibleIterator as _;
    let mut out = BTreeMap::new();
    if types.is_empty() {
        return out;
    }
    let Ok(info) = db.type_information() else {
        return out;
    };
    let mut finder = info.finder();
    let mut iter = info.iter();
    while let Ok(Some(_)) = iter.next() {
        finder.update(&iter);
    }
    for (&rva, &index) in types {
        let sig = resolve(&finder, index);
        if sig.ret.is_some() || !sig.params.is_empty() {
            out.insert(rva, sig);
        }
    }
    out
}

/// Reads the source file and line each gathered procedure starts at, from
/// the modules' line programs.
///
/// One row per procedure: the first line row the module's program maps
/// inside the procedure's extent, which is the line its first instruction
/// was written on. A name the string table does not hold contributes
/// nothing, never a guess; the winners stay bounded by the procedures
/// gathered, whatever the rows number.
///
/// # Arguments
///
/// * `db` - The opened PDB.
/// * `lines` - The winning rows, as [`Gathered::lines`] left them: their
///   offset in the image, the file's reference into the string table and
///   their line.
///
/// # Returns
///
/// Procedure RVA to the `(file, line)` its first row names.
fn resolve_lines<'s>(
    db: &mut pdb::PDB<'s, Cursor<&'s [u8]>>,
    lines: &BTreeMap<u32, (u32, pdb::StringRef, u32)>,
) -> BTreeMap<u32, (String, u32)> {
    let mut out = BTreeMap::new();
    if lines.is_empty() {
        return out;
    }
    let Ok(table) = db.string_table() else {
        return out;
    };
    for (start, (_, file, line)) in lines {
        let name = table.get(*file).map(|n| n.to_string()).unwrap_or_default();
        if !name.is_empty() {
            out.insert(*start, (crate::text::one_line(&name), *line));
        }
    }
    out
}

/// Resolves the signature a procedure's type index states.
///
/// # Arguments
///
/// * `finder` - The type stream, walked to its end.
/// * `index` - The type index the procedure record names.
///
/// # Returns
///
/// The signature, empty when the index names no procedure or member type
/// the stream holds: a record that is missing, damaged or of another kind
/// states no signature.
fn resolve(finder: &pdb::TypeFinder<'_>, index: pdb::TypeIndex) -> Signature {
    let Ok(data) = finder.find(index).and_then(|t| t.parse()) else {
        return Signature::default();
    };
    match data {
        pdb::TypeData::Procedure(p) => Signature {
            ret: p.return_type.and_then(|i| type_text(finder, i, TYPE_DEPTH)),
            params: arguments(finder, p.argument_list),
        },
        pdb::TypeData::MemberFunction(m) => {
            let this = m
                .this_pointer_type
                .and_then(|i| type_text(finder, i, TYPE_DEPTH))
                .or_else(|| type_text(finder, m.class_type, TYPE_DEPTH).map(|c| pointer(&c)));
            let mut params = arguments(finder, m.argument_list);
            if let Some(this) = this {
                params.insert(0, this);
            }
            Signature {
                ret: (!matches!(m.return_type.0, 0 | 0xffff))
                    .then(|| type_text(finder, m.return_type, TYPE_DEPTH))
                    .flatten(),
                params,
            }
        }
        _ => Signature::default(),
    }
}

/// Resolves an argument list's types, in order.
///
/// # Arguments
///
/// * `finder` - The type stream, walked to its end.
/// * `list` - The argument-list type index a procedure record states.
///
/// # Returns
///
/// The parameter types as C source, cut at [`PARAMS_MAX`]; a single `void`
/// is `CodeView`'s spelling of an empty list, a damaged list is none, and a
/// parameter that does not resolve is dropped where it stands.
fn arguments(finder: &pdb::TypeFinder<'_>, list: pdb::TypeIndex) -> Vec<String> {
    let Ok(pdb::TypeData::ArgumentList(args)) = finder.find(list).and_then(|t| t.parse()) else {
        return Vec::new();
    };
    if let [only] = args.arguments.as_slice()
        && is_void(finder, *only)
    {
        return Vec::new();
    }
    args.arguments
        .iter()
        .take(PARAMS_MAX)
        .filter_map(|&i| type_text(finder, i, TYPE_DEPTH))
        .collect()
}

/// Tells whether a type index is the `void` primitive.
///
/// # Arguments
///
/// * `finder` - The type stream, walked to its end.
/// * `index` - The type index to ask about.
fn is_void(finder: &pdb::TypeFinder<'_>, index: pdb::TypeIndex) -> bool {
    matches!(
        finder.find(index).and_then(|t| t.parse()),
        Ok(pdb::TypeData::Primitive(p)) if p.kind == pdb::PrimitiveKind::Void
    )
}

/// Resolves a type index to C source, the way the DWARF chains render.
///
/// # Arguments
///
/// * `finder` - The type stream, walked to its end.
/// * `index` - The type index to resolve.
/// * `depth` - Remaining links to follow, against a circular chain.
///
/// # Returns
///
/// The type as C source, or `None` when the chain does not resolve within
/// its depth or is of a kind no parameter or return renders as.
fn type_text(finder: &pdb::TypeFinder<'_>, index: pdb::TypeIndex, depth: u32) -> Option<String> {
    if depth == 0 {
        return None;
    }
    let data = finder.find(index).ok()?.parse().ok()?;
    let inner = |i| type_text(finder, i, depth - 1);
    Some(match data {
        pdb::TypeData::Primitive(p) => {
            let base = primitive_text(p.kind)?;
            match p.indirection {
                None => base,
                Some(_) => pointer(&base),
            }
        }
        pdb::TypeData::Pointer(p) => {
            inner(p.underlying_type).map_or_else(|| "void *".to_owned(), |to| pointer(&to))
        }
        pdb::TypeData::Modifier(m) => {
            let to = inner(m.underlying_type)?;
            // `const` binds to the pointer, not the pointee, when it
            // follows one: `char * const`, not `const char *`.
            if m.constant {
                if to.ends_with('*') {
                    format!("{to} const")
                } else {
                    format!("const {to}")
                }
            } else if m.volatile {
                format!("volatile {to}")
            } else {
                to
            }
        }
        pdb::TypeData::Class(c) => {
            let tag = match c.kind {
                pdb::ClassKind::Class => "class",
                pdb::ClassKind::Struct | pdb::ClassKind::Interface => "struct",
            };
            let name = c.name.to_string();
            if name.is_empty() {
                tag.to_owned()
            } else {
                format!("{tag} {name}")
            }
        }
        pdb::TypeData::Union(u) => {
            let name = u.name.to_string();
            if name.is_empty() {
                "union".to_owned()
            } else {
                format!("union {name}")
            }
        }
        pdb::TypeData::Enumeration(e) => {
            let name = e.name.to_string();
            if name.is_empty() {
                "enum".to_owned()
            } else {
                format!("enum {name}")
            }
        }
        pdb::TypeData::Array(a) => format!("{}[]", inner(a.element_type)?),
        pdb::TypeData::Procedure(p) => format!(
            "{} ()",
            p.return_type
                .and_then(inner)
                .unwrap_or_else(|| "void".into())
        ),
        pdb::TypeData::Bitfield(b) => inner(b.underlying_type)?,
        // A field, a method list, a nested list: members of a type, not
        // types a parameter or a return renders as.
        _ => return None,
    })
}

/// Appends a pointer level, the way the DWARF chains render one.
///
/// # Arguments
///
/// * `to` - The type the pointer points at, as C source.
///
/// # Returns
///
/// `to` with a `*`, glued to a pointer that already ends in one.
fn pointer(to: &str) -> String {
    if to.ends_with('*') {
        format!("{to}*")
    } else {
        format!("{to} *")
    }
}

/// Renders a primitive kind as the C source the decompiler's text uses.
///
/// The sized integers take the `stdint` spellings the decompiler's own
/// inferred types print, so a recorded type and an inferred one read the
/// same for the same width.
///
/// # Arguments
///
/// * `kind` - The primitive kind the stream states.
///
/// # Returns
///
/// The C source, or `None` for the kinds no C parameter renders as.
fn primitive_text(kind: pdb::PrimitiveKind) -> Option<String> {
    use pdb::PrimitiveKind as P;
    Some(
        match kind {
            P::Void => "void",
            P::Char | P::RChar => "char",
            P::UChar => "unsigned char",
            P::WChar => "wchar_t",
            P::RChar16 => "char16_t",
            P::RChar32 => "char32_t",
            P::I8 => "int8_t",
            P::U8 => "uint8_t",
            P::Short | P::I16 => "int16_t",
            P::UShort | P::U16 => "uint16_t",
            P::Long | P::I32 => "int32_t",
            P::ULong | P::U32 => "uint32_t",
            P::Quad | P::I64 => "int64_t",
            P::UQuad | P::U64 => "uint64_t",
            P::Octa | P::I128 => "__int128",
            P::UOcta | P::U128 => "unsigned __int128",
            P::F16 => "_Float16",
            P::F32 | P::F32PP => "float",
            P::F64 => "double",
            P::F80 => "long double",
            P::F128 => "__float128",
            P::Bool8 | P::Bool16 | P::Bool32 | P::Bool64 => "bool",
            P::HRESULT => "long",
            // `NoType` states nothing, the exotic floats and complex kinds
            // have no spelling in the text's vocabulary, and the crate
            // leaves the enum open for kinds it has not met.
            P::NoType | P::F48 | P::Complex32 | P::Complex64 | P::Complex80 | P::Complex128 => {
                return None;
            }
            _ => return None,
        }
        .to_owned(),
    )
}

/// Inserts gathered symbols as local symbols, keeping what the image states.
///
/// An address that already holds a symbol (an import's slot, an export's
/// entry) keeps the image's own name, the same precedence the DWARF names
/// are applied with.
///
/// # Arguments
///
/// * `image_base` - The image's preferred load base, added to every RVA.
/// * `found` - The gathered symbols, in address order.
/// * `symbols` - The program's symbol list, appended to.
///
/// # Returns
///
/// How many symbols were inserted.
fn insert(image_base: u64, found: &BTreeMap<u32, String>, symbols: &mut Vec<Symbol>) -> usize {
    let taken: std::collections::BTreeSet<u64> = symbols.iter().map(|s| s.addr).collect();
    let mut named = 0usize;
    for (rva, name) in found {
        let addr = image_base + u64::from(*rva);
        if !taken.contains(&addr) {
            symbols.push(Symbol {
                name: name.clone(),
                addr,
                kind: SymbolKind::Local,
            });
            named += 1;
        }
    }
    named
}

/// Appends gathered data records as data symbols, keeping the image's and
/// the functions' names.
///
/// An address that already holds a symbol keeps the name it has, and an
/// address a gathered function names keeps that: the functions were
/// inserted first, so what survives here is the addresses only data
/// claims. [`data_va`] refuses every address outside a non-executable
/// section, which is also what keeps a data name off any function the
/// analysis discovers.
///
/// # Arguments
///
/// * `image_base` - The image's preferred load base, added to every RVA.
/// * `found` - The gathered functions, in address order.
/// * `data` - The gathered data records, in address order.
/// * `sections` - The image's sections; a record lands only inside one
///   non-executable section ([`data_va`]).
/// * `symbols` - The program's symbol list, appended to.
///
/// # Returns
///
/// How many data symbols were inserted.
fn insert_data(
    image_base: u64,
    found: &BTreeMap<u32, String>,
    data: &BTreeMap<u32, String>,
    sections: &[Section],
    symbols: &mut Vec<Symbol>,
) -> usize {
    let taken: std::collections::BTreeSet<u64> = symbols.iter().map(|s| s.addr).collect();
    let mut named = 0usize;
    for (rva, name) in data {
        if found.contains_key(rva) {
            continue;
        }
        if let Some(addr) = data_va(image_base, *rva, sections)
            && !taken.contains(&addr)
        {
            symbols.push(Symbol {
                name: name.clone(),
                addr,
                kind: SymbolKind::Data,
            });
            named += 1;
        }
    }
    named
}

#[cfg(test)]
#[expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]
mod tests {
    use super::{
        Gathered, Record, candidates, data_va, extent_va, identifies, insert, insert_data,
        matches_record, pointer, primitive_text,
    };
    use crate::dwarf::{frame_slot, local_name_ok};
    use crate::program::{Program, Section, Symbol, SymbolKind};
    use std::collections::BTreeMap;
    use std::path::Path;

    /// Makes the [`pdb::RawString`] the gather tests feed, from a name.
    fn raw(name: &str) -> pdb::RawString<'_> {
        pdb::RawString::from(name)
    }

    /// The type index of a defined type record, as a procedure names one.
    fn ty(index: u32) -> Option<pdb::TypeIndex> {
        Some(pdb::TypeIndex(index))
    }

    /// The recorded path, the binary's directory and the cache are the
    /// candidates, in that order.
    ///
    /// A recorded Windows path is absolute only where Windows reads it, and
    /// the sibling takes its file name from it on every host.
    ///
    /// # Panics
    ///
    /// When the order differs or a working-directory-relative path sneaks
    /// in.
    #[test]
    fn the_record_names_three_places_and_no_others() {
        let dir = Path::new("bin");
        let binary = dir.join("app.exe");
        let record = Record {
            path: r"C:\build\app.pdb".to_owned(),
            guid: [0; 16],
            age: 1,
        };
        let mut expected = Vec::new();
        if cfg!(windows) {
            expected.push(Path::new(r"C:\build\app.pdb").to_path_buf());
        }
        expected.push(dir.join("app.pdb"));
        assert_eq!(candidates(&record, &binary, None), expected);
        // A relative record names only the sibling and the cache, never a
        // working directory, which would make the answer depend on where
        // the engine ran from.
        let mut relative = record;
        relative.path = r"build\app.pdb".to_owned();
        let cache = Path::new("cache");
        assert_eq!(
            candidates(&relative, &binary, Some(cache)),
            vec![
                dir.join("app.pdb"),
                cache
                    .join("app.pdb")
                    .join("000000000000000000000000000000001")
                    .join("app.pdb"),
            ]
        );
    }

    /// The key spells the GUID and age the way the store's paths do.
    ///
    /// # Panics
    ///
    /// When the spelling differs in case, width or order.
    #[test]
    fn the_key_spells_the_pair_the_store_expects() {
        let record = Record {
            path: String::new(),
            guid: [
                0x78, 0x56, 0x34, 0x12, 0x22, 0x22, 0x33, 0x33, 1, 2, 3, 4, 5, 6, 7, 8,
            ],
            age: 7,
        };
        assert_eq!(record.symsrv_key(), "123456782222333301020304050607087");
    }

    /// A PDB matches only the record of its own build.
    #[test]
    fn a_pdb_matches_only_its_own_record() {
        let record = Record {
            path: String::new(),
            guid: [
                0x78, 0x56, 0x34, 0x12, 0x22, 0x22, 0x33, 0x33, 1, 2, 3, 4, 5, 6, 7, 8,
            ],
            age: 7,
        };
        let guid = (
            0x1234_5678u32,
            0x2222u16,
            0x3333u16,
            &[1u8, 2, 3, 4, 5, 6, 7, 8],
        );
        assert!(matches_record(guid, 7, &record));
        assert!(!matches_record(guid, 8, &record));
        let wrong_guid = (0x1234_5679u32, 0x2222, 0x3333, &[1, 2, 3, 4, 5, 6, 7, 8]);
        assert!(!matches_record(wrong_guid, 7, &record));
        let wrong_tail = (0x1234_5678, 0x2222, 0x3333, &[1, 2, 3, 4, 5, 6, 7, 9]);
        assert!(!matches_record(wrong_tail, 7, &record));
    }

    /// The gather stops at its cap and counts the rest, skipping nothing
    /// that is no candidate at all.
    #[test]
    fn a_full_gather_counts_what_the_cap_cut() {
        let mut g = Gathered {
            max: 2,
            ..Gathered::default()
        };
        for (rva, name, len) in [
            (1, "a", Some(0x10u32)),
            (1, "dup", Some(0x20)),
            (2, "", Some(0)),
            (2, "b", Some(0)),
            (3, "c", None),
            (4, "d", None),
        ] {
            g.take(Some(rva), raw(name), len, ty(0x1004));
        }
        g.take(None, raw("unmapped"), Some(8), ty(0x1004));
        g.take(Some(0), raw("the image base"), Some(8), ty(0x1004));
        let names: Vec<&str> = g.found.values().map(String::as_str).collect();
        assert_eq!(names, vec!["a", "b"], "{g:?}");
        assert_eq!(g.extents.get(&1), Some(&0x11), "{g:?}");
        assert!(!g.extents.contains_key(&2), "a zero length states none");
        assert_eq!(
            g.types.get(&1),
            Some(&pdb::TypeIndex(0x1004)),
            "a named procedure keeps its type"
        );
        assert_eq!(
            g.types.get(&2),
            Some(&pdb::TypeIndex(0x1004)),
            "the name that took an unnamed address takes its type too: {g:?}"
        );
        assert_eq!(g.dropped, 2);
    }

    /// A primitive kind takes the spelling the decompiler's own inferred
    /// types use, glued pointers included; what C cannot say stays `None`.
    #[test]
    fn primitives_render_as_the_decompilers_own_types_do() {
        use pdb::PrimitiveKind as P;
        let text = |k| primitive_text(k);
        assert_eq!(text(P::Void).as_deref(), Some("void"));
        assert_eq!(text(P::UChar).as_deref(), Some("unsigned char"));
        assert_eq!(text(P::WChar).as_deref(), Some("wchar_t"));
        assert_eq!(text(P::Long).as_deref(), Some("int32_t"));
        assert_eq!(text(P::U32).as_deref(), Some("uint32_t"));
        assert_eq!(text(P::Quad).as_deref(), Some("int64_t"));
        assert_eq!(text(P::UQuad).as_deref(), Some("uint64_t"));
        assert_eq!(text(P::F32).as_deref(), Some("float"));
        assert_eq!(text(P::F64).as_deref(), Some("double"));
        assert_eq!(text(P::Bool8).as_deref(), Some("bool"));
        assert_eq!(text(P::NoType), None);
        assert_eq!(text(P::Complex64), None);
        assert_eq!(pointer("uint8_t"), "uint8_t *");
        assert_eq!(pointer("char **"), "char ***");
    }

    /// An extent lands only where an executable section holds it whole.
    ///
    /// One that crosses into the next section, sits in data, or runs past
    /// the section's end describes no code this image holds, and is refused
    /// rather than trimmed to what fits.
    #[test]
    fn an_extent_lands_only_inside_one_executable_section() {
        let base = 0x1400_0000u64;
        let sections = vec![
            Section::mapped(".text", base + 0x1000, 0x1000, 0x2000, false, true),
            Section::mapped(".rdata", base + 0x3000, 0x3000, 0x1000, false, false),
        ];
        let va = |rva: u32, end: u32| extent_va(base, rva, end, &sections);
        assert_eq!(va(0x1000, 0x1040), Some((base + 0x1000, base + 0x1040)));
        assert_eq!(
            va(0x2ff0, 0x3000),
            Some((base + 0x2ff0, base + 0x3000)),
            "an end at the section's edge is inside it"
        );
        assert_eq!(va(0x2ff0, 0x3010), None, "it crosses into the next section");
        assert_eq!(va(0x3000, 0x3040), None, "it sits in data");
        assert_eq!(va(0x8000, 0x8040), None, "it sits in no section at all");
        assert_eq!(va(0xf000, 0x1000), None, "a wrapped end holds no code");
    }

    /// An applied PDB names only the addresses the image left open.
    #[test]
    fn applied_symbols_keep_the_names_the_image_states() {
        let mut symbols = vec![Symbol {
            name: "DllMain".to_owned(),
            addr: 0x1400_1000,
            kind: SymbolKind::Export,
        }];
        let mut found = BTreeMap::new();
        found.insert(0x1000u32, "public_DllMain".to_owned());
        found.insert(0x2000u32, "static_helper".to_owned());
        let named = insert(0x1400_0000, &found, &mut symbols);
        assert_eq!(named, 1);
        assert_eq!(symbols[0].name, "DllMain", "the export keeps its name");
        assert_eq!(symbols[1].addr, 0x1400_2000);
        assert_eq!(symbols[1].kind, SymbolKind::Local);
    }

    /// A data record yields to a function at the same address and shares
    /// the cap with the function names.
    #[test]
    fn a_data_record_yields_to_functions_and_shares_the_cap() {
        let mut g = Gathered {
            max: 2,
            ..Gathered::default()
        };
        g.take(Some(1), raw("fn"), Some(0x10), ty(0x1004));
        g.take_data(Some(1), raw("the functions rva"));
        g.take_data(Some(2), raw("first_data"));
        g.take_data(Some(2), raw("dup_data"));
        g.take_data(Some(3), raw("capped_data"));
        g.take_data(None, raw("unmapped"));
        g.take_data(Some(0), raw("the image base"));
        let names: Vec<(u32, &str)> = g.data.iter().map(|(k, v)| (*k, v.as_str())).collect();
        assert_eq!(names, vec![(2, "first_data")], "{g:?}");
        assert_eq!(g.dropped, 1, "{g:?}");
    }

    /// A data record lands only where a non-executable section maps it.
    ///
    /// One that lands in code, or in no section at all, describes nothing
    /// this image's data lives at, and is refused rather than named onto
    /// a function's address.
    #[test]
    fn a_data_record_lands_only_in_non_executable_sections() {
        let base = 0x1400_0000u64;
        let sections = vec![
            Section::mapped(".text", base + 0x1000, 0x1000, 0x2000, false, true),
            Section::mapped(".rdata", base + 0x3000, 0x3000, 0x1000, false, false),
        ];
        let va = |rva: u32| data_va(base, rva, &sections);
        assert_eq!(va(0x3000), Some(base + 0x3000));
        assert_eq!(va(0x3ff8), Some(base + 0x3ff8));
        assert_eq!(va(0x1000), None, "an executable section holds code");
        assert_eq!(va(0x8000), None, "no section maps it");
    }

    /// Applied data symbols take only the addresses no function, no image
    /// symbol and no data section refuses.
    #[test]
    fn applied_data_symbols_stay_off_functions_and_code() {
        let base = 0x1400_0000u64;
        let sections = vec![
            Section::mapped(".text", base + 0x1000, 0x1000, 0x2000, false, true),
            Section::mapped(".data", base + 0x4000, 0x4000, 0x1000, true, false),
        ];
        let mut symbols = vec![Symbol {
            name: "Imported".to_owned(),
            addr: base + 0x4008,
            kind: SymbolKind::Import,
        }];
        let mut found = BTreeMap::new();
        found.insert(0x1000u32, "fn".to_owned());
        let mut data = BTreeMap::new();
        data.insert(0x1000u32, "the functions address".to_owned());
        data.insert(0x4008u32, "the imports slot".to_owned());
        data.insert(0x4000u32, "gap022_static".to_owned());
        data.insert(0x9000u32, "unmapped".to_owned());
        let named = insert_data(base, &found, &data, &sections, &mut symbols);
        assert_eq!(named, 1, "{symbols:?}");
        let applied = &symbols[1];
        assert_eq!(applied.addr, base + 0x4000);
        assert_eq!(applied.name, "gap022_static");
        assert_eq!(applied.kind, SymbolKind::Data);
    }

    /// The running test binary's own PDB names its functions end to end.
    ///
    /// Record, resolution, match and apply all run against the real
    /// artifacts of a build. A build without debug information (a release
    /// profile) has no PDB to find, and then nothing is applied. Where the
    /// PDB applies, its procedure extents only ever add function ranges:
    /// the exception table's are all still there.
    #[test]
    fn the_test_binaries_own_pdb_names_its_functions() {
        let exe = std::env::current_exe().expect("the test binary has a path");
        let bytes = std::fs::read(&exe).expect("the test binary is readable");
        if bytes.first_chunk::<2>() != Some(b"MZ") {
            return;
        }
        let pe = goblin::pe::PE::parse(&bytes).expect("the test binary is a parseable PE");
        let Some(cv) = pe
            .debug_data
            .as_ref()
            .and_then(|d| d.codeview_pdb70_debug_info.as_ref())
        else {
            return;
        };
        let record = Record::from_debug_info(cv);
        let resolved = candidates(&record, &exe, None)
            .into_iter()
            .find(|p| p.is_file());
        let program = Program::load(&exe).expect("the test binary loads");
        let kept = program
            .pdb_record
            .as_ref()
            .expect("a load keeps the record it read");
        assert_eq!(kept.guid, record.guid);
        assert_eq!(kept.age, record.age);
        match resolved {
            Some(_) => match program.pdb {
                Some(super::Outcome::Applied { named, .. }) => {
                    assert!(named > 0, "the PDB names at least one function");
                    assert!(
                        program
                            .symbols
                            .iter()
                            .any(|s| s.kind == SymbolKind::Local && s.addr != 0),
                        "an applied PDB leaves local symbols"
                    );
                    let bare = Program::load_with(&exe, false).expect("it loads again");
                    assert!(
                        program.function_ranges.len() >= bare.function_ranges.len(),
                        "the PDB removed ranges: {} without it, {} with it",
                        bare.function_ranges.len(),
                        program.function_ranges.len()
                    );
                }
                other => panic!("a matching PDB was not applied: {other:?}"),
            },
            None => assert!(
                program.pdb.is_none(),
                "no PDB on disk changes nothing: {:?}",
                program.pdb
            ),
        }
    }

    /// Downloaded bytes identify their build only when the record is theirs.
    ///
    /// The running binary's own PDB is the one file guaranteed to both
    /// parse and match, so the gate's yes is exercised on real bytes; one
    /// GUID byte flipped in the record turns it into a no, and bytes that
    /// are no PDB at all read as unreadable. A build without a PDB on disk
    /// (a release profile) has nothing to ask about, and nothing is
    /// asserted.
    #[test]
    fn downloaded_bytes_identify_only_their_own_build() {
        let exe = std::env::current_exe().expect("the test binary has a path");
        let bytes = std::fs::read(&exe).expect("the test binary is readable");
        if bytes.first_chunk::<2>() != Some(b"MZ") {
            return;
        }
        let pe = goblin::pe::PE::parse(&bytes).expect("the test binary is a parseable PE");
        let Some(cv) = pe
            .debug_data
            .as_ref()
            .and_then(|d| d.codeview_pdb70_debug_info.as_ref())
        else {
            return;
        };
        let mut record = Record::from_debug_info(cv);
        let Some(own) = candidates(&record, &exe, None)
            .into_iter()
            .find(|p| p.is_file())
            .and_then(|p| std::fs::read(p).ok())
        else {
            return;
        };
        assert_eq!(identifies(&own, &record), Some(true));
        record.guid[0] ^= 1;
        assert_eq!(identifies(&own, &record), Some(false));
        assert_eq!(identifies(b"not a pdb", &record), None);
    }

    /// A signature the running binary states, for the end-to-end test.
    ///
    /// The compiler records the function and its type in the PDB the test
    /// binary builds with, and its mangled name embeds the path, so the
    /// test finds it by the part that cannot change. Never inlined, or the
    /// one call there is folds into the caller and no procedure exists.
    #[inline(never)]
    fn gap022_probe(x: u32, y: f64) -> u64 {
        u64::from(x).wrapping_add(y.to_bits())
    }

    /// The running test binary's own PDB states a known signature.
    ///
    /// The probe is compiled into the binary, so its PDB holds the
    /// procedure record and the type that record names; where the PDB
    /// applies, the signature reads back as the decompiler's header will
    /// print it. A build without a PDB on disk has nothing to read, and
    /// then nothing is asserted.
    #[test]
    fn the_test_binaries_own_pdb_states_a_known_signature() {
        // The arguments pass through a black box, or the pure call folds
        // away before the linker ever sees a procedure to record.
        let probe = gap022_probe(std::hint::black_box(7), std::hint::black_box(0.5));
        assert!(probe >= 7, "the probe ran: {probe}");
        let exe = std::env::current_exe().expect("the test binary has a path");
        let bytes = std::fs::read(&exe).expect("the test binary is readable");
        if bytes.first_chunk::<2>() != Some(b"MZ") {
            return;
        }
        let pe = goblin::pe::PE::parse(&bytes).expect("the test binary is a parseable PE");
        let Some(cv) = pe
            .debug_data
            .as_ref()
            .and_then(|d| d.codeview_pdb70_debug_info.as_ref())
        else {
            return;
        };
        let record = Record::from_debug_info(cv);
        let resolved = candidates(&record, &exe, None)
            .into_iter()
            .find(|p| p.is_file());
        if resolved.is_none() {
            return;
        }
        let program = Program::load(&exe).expect("the test binary loads");
        let Some(super::Outcome::Applied { .. }) = program.pdb else {
            panic!("a matching PDB was not applied: {:?}", program.pdb)
        };
        let sub = program
            .debug_functions
            .iter()
            .find(|d| d.name.contains("gap022_probe"))
            .unwrap_or_else(|| {
                panic!(
                    "the probe's signature was not read: {} debug functions",
                    program.debug_functions.len()
                )
            });
        let params: Vec<&str> = sub
            .parameters
            .iter()
            .map(|p| p.type_name.as_deref().unwrap_or(""))
            .collect();
        assert_eq!(params, vec!["uint32_t", "double"], "{}", sub.name);
        assert!(
            sub.parameters.iter().all(|p| p.name.is_empty()),
            "a PDB names no parameter, only its type"
        );
        assert_eq!(sub.return_type.as_deref(), Some("uint64_t"));
    }

    /// The running test binary's own PDB states a known source line.
    ///
    /// The probe is compiled into the binary, so its PDB holds the module
    /// line program mapping the probe's first instruction back to this
    /// file; where the PDB applies, the lazy walk states the file and
    /// line, the decompile's header says them as a `// source:` line, and
    /// a second ask answers the same rows the first did. A build without
    /// a PDB on disk has nothing to read, and then nothing is asserted.
    #[test]
    fn the_test_binaries_own_pdb_states_a_known_source() {
        let read = gap022_data_probe(std::hint::black_box(5));
        assert!(read >= 5, "the probe ran: {read}");
        let exe = std::env::current_exe().expect("the test binary has a path");
        let bytes = std::fs::read(&exe).expect("the test binary is readable");
        if bytes.first_chunk::<2>() != Some(b"MZ") {
            return;
        }
        let pe = goblin::pe::PE::parse(&bytes).expect("the test binary is a parseable PE");
        let Some(cv) = pe
            .debug_data
            .as_ref()
            .and_then(|d| d.codeview_pdb70_debug_info.as_ref())
        else {
            return;
        };
        let record = Record::from_debug_info(cv);
        let resolved = candidates(&record, &exe, None)
            .into_iter()
            .find(|p| p.is_file());
        if resolved.is_none() {
            return;
        }
        let program = Program::load(&exe).expect("the test binary loads");
        let Some(super::Outcome::Applied { .. }) = program.pdb else {
            panic!("a matching PDB was not applied: {:?}", program.pdb)
        };
        let sub = program
            .debug_functions
            .iter()
            .find(|d| d.name.contains("gap022_data_probe"))
            .unwrap_or_else(|| {
                panic!(
                    "the probe's debug function was not read: {} debug functions",
                    program.debug_functions.len()
                )
            });
        let word = i64::from(program.arch.bitness().unwrap_or(64) / 8);
        let rows = super::sources(&exe, &record, None, program.image_base, word);
        let (file, line) = rows
            .as_ref()
            .and_then(|rows| rows.get(&sub.low_pc))
            .cloned()
            .unwrap_or_else(|| panic!("the probe's source row was not stated"));
        assert!(
            file.ends_with("pdb.rs"),
            "the source file is not this one: {file:?}"
        );
        assert!(line > 0, "the source line is not stated: {line:?}");
        let a = crate::analysis::Analysis::compute(&program);
        let overlay = crate::analysis::Overlay::default();
        let text = crate::analysis::decompile::decompile(&program, &a, &overlay, sub.low_pc)
            .unwrap_or_default();
        let stated = format!("// source: {file}:{line}");
        assert!(
            text.contains(&stated),
            "the header does not state the source:
{text}"
        );
        // The same binary answers the same rows twice: the walk the first
        // ask paid is not paid differently by the second.
        let again = super::sources(&exe, &record, None, program.image_base, word);
        assert_eq!(again, rows, "the second walk answered differently");
        let twice = crate::analysis::decompile::decompile(&program, &a, &overlay, sub.low_pc)
            .unwrap_or_default();
        assert_eq!(twice, text, "the second decompile answered differently");
    }

    /// An opaque call, never inlined, that a local must outlive.
    ///
    /// The call lands between the stores of the probe's locals and their
    /// reads, so the optimizer cannot keep them in registers: their
    /// addresses have escaped before a call, and they reload after it.
    #[inline(never)]
    fn gap022_sides(x: u32) -> u32 {
        x.wrapping_add(x)
    }

    /// Locals the running binary's own PDB states, for the end-to-end test.
    ///
    /// Each local is read through a black-boxed pointer across a call,
    /// which forces its address out of the register allocator and onto the
    /// frame the PDB then states as a frame-pointer-relative record. Never
    /// inlined, or the one call there is folds into the caller and no
    /// procedure exists.
    #[inline(never)]
    fn gap022_locals_probe(x: u32) -> u64 {
        let alpha: u64 = u64::from(x).wrapping_mul(3);
        let beta: u32 = x.wrapping_add(7);
        let gamma: u16 = (x & 0xff) as u16;
        let (a, b, g) = std::hint::black_box((&alpha, &beta, &gamma));
        let keep = gap022_sides(std::hint::black_box(x));
        a.wrapping_add(u64::from(*b))
            .wrapping_add(u64::from(*g))
            .wrapping_add(u64::from(keep))
    }

    /// The running test binary's own PDB names its frame's locals.
    ///
    /// The probe's locals are compiled into the binary, so its PDB holds a
    /// frame-relative record for each; where the PDB applies, the record
    /// names the decompiler's slot at that offset, so the local renders by
    /// its own name where the synthesized `local_N` otherwise would. The
    /// widths stay the lifting's own: `gamma` reads and writes as the byte
    /// pair the code moves, whatever the PDB's type for it says. A build
    /// without a PDB on disk has nothing to read, and then nothing is
    /// asserted.
    #[test]
    fn the_test_binaries_own_pdb_names_its_locals() {
        let read = gap022_locals_probe(std::hint::black_box(5));
        assert!(read >= 5, "the probe ran: {read}");
        let exe = std::env::current_exe().expect("the test binary has a path");
        let bytes = std::fs::read(&exe).expect("the test binary is readable");
        if bytes.first_chunk::<2>() != Some(b"MZ") {
            return;
        }
        let pe = goblin::pe::PE::parse(&bytes).expect("the test binary is a parseable PE");
        let Some(cv) = pe
            .debug_data
            .as_ref()
            .and_then(|d| d.codeview_pdb70_debug_info.as_ref())
        else {
            return;
        };
        let record = Record::from_debug_info(cv);
        let resolved = candidates(&record, &exe, None)
            .into_iter()
            .find(|p| p.is_file());
        if resolved.is_none() {
            return;
        }
        let program = Program::load(&exe).expect("the test binary loads");
        let Some(super::Outcome::Applied { .. }) = program.pdb else {
            panic!("a matching PDB was not applied: {:?}", program.pdb)
        };
        let sub = program
            .debug_functions
            .iter()
            .find(|d| d.name.contains("gap022_locals_probe"))
            .unwrap_or_else(|| {
                panic!(
                    "the probe's debug function was not read: {} debug functions",
                    program.debug_functions.len()
                )
            });
        for name in ["alpha", "beta", "gamma"] {
            assert!(
                sub.locals.values().any(|n| n == name),
                "the local {name} was not stated: {:?}",
                sub.locals
            );
        }
        assert!(
            sub.locals.keys().all(|off| *off < 0),
            "a local sat above the return address: {:?}",
            sub.locals
        );
        let a = crate::analysis::Analysis::compute(&program);
        let overlay = crate::analysis::Overlay::default();
        let text = crate::analysis::decompile::decompile(&program, &a, &overlay, sub.low_pc)
            .unwrap_or_default();
        for name in ["alpha", "beta", "gamma"] {
            let off = sub
                .locals
                .iter()
                .find(|(_, n)| n.as_str() == name)
                .map(|(off, _)| *off)
                .unwrap_or_default();
            let synthesized = format!("local_{:x}", -off);
            assert!(
                text.contains(name) && !text.contains(&synthesized),
                "the local {name} at {off:#x} does not render as itself:
{text}"
            );
        }
    }

    /// Frame-relative offsets convert into the slots the decompiler states:
    /// a word under the frame pointer, a whole frame under the stack
    /// pointer, and never the return address or outside a sane span.
    #[test]
    fn frame_offsets_convert_into_slots() {
        // The frame pointer sits on the pushed register itself, a word
        // under the return address.
        assert_eq!(frame_slot(-0x18, true, 8, 0x38), Some(-0x20));
        assert_eq!(frame_slot(-0x10, true, 4, 0x20), Some(-0x14));
        // A frame-pointer-less frame's base sits at the bottom of the
        // frame its record states.
        assert_eq!(frame_slot(0x20, false, 8, 0x28), Some(-8));
        assert_eq!(frame_slot(2, false, 8, 0x28), Some(-0x26));
        // The return address's own slot, and offsets no frame holds.
        assert_eq!(frame_slot(8, true, 8, 0), None);
        assert_eq!(frame_slot(0, false, 8, 0), None);
        assert_eq!(frame_slot(-0x20000, true, 8, 0x28), None);
        assert_eq!(frame_slot(0x20000, false, 8, 0x28), None);
    }

    /// A local's name stands in the text only where it cannot make the
    /// text say or mean something else.
    #[test]
    fn only_names_the_text_can_hold_name_a_slot() {
        for name in ["alpha", "beta2", "_pad", "a_1"] {
            assert!(local_name_ok(name), "{name}");
        }
        // Not identifiers, or empty.
        for name in ["", "2fast", "x; y", "a-b", "x y"] {
            assert!(!local_name_ok(name), "{name}");
        }
        // Words the text's own grammar reads.
        for name in ["retaddr", "if", "while", "return", "sizeof"] {
            assert!(!local_name_ok(name), "{name}");
        }
        // Names the text synthesizes for slots, temporaries, parameters
        // and globals.
        for name in [
            "local_8",
            "home_10",
            "arg_18",
            "tmp_1",
            "a3",
            "g64_140010000",
        ] {
            assert!(!local_name_ok(name), "{name}");
        }
    }

    /// A local's map keeps one name per slot and one slot per name, and
    /// stops at its cap.
    #[test]
    fn a_local_never_shares_a_slot_or_a_name() {
        let mut g = Gathered::default();
        g.locals.insert(0x1000, BTreeMap::new());
        g.take_local(0x1000, Some(-8), "alpha");
        g.take_local(0x1000, Some(-0x10), "alpha");
        g.take_local(0x1000, Some(-8), "shadowed");
        g.take_local(0x1000, None, "refused");
        g.take_local(0x2000, Some(-8), "another frame");
        let map = g.locals.get(&0x1000).unwrap();
        assert_eq!(
            map.iter().collect::<Vec<_>>(),
            vec![(&-8i64, &"alpha".to_owned())],
            "{g:?}"
        );
        assert!(!g.locals.contains_key(&0x2000), "{g:?}");
    }

    /// A static the running binary's own PDB states as data, for the
    /// end-to-end tests.
    ///
    /// The compiler records the static in the PDB the test binary builds
    /// with. Read through a black-boxed pointer, or the dev profile's
    /// optimizer folds the value away and the linker drops both the static
    /// and its record.
    static GAP022_DATA: u64 = 0x5eed_c0de_1234_5678;

    /// Reads the static the PDB names, never inlined, so a procedure
    /// record for the probe and a load of the static both exist.
    #[inline(never)]
    fn gap022_data_probe(x: u32) -> u64 {
        let s = std::hint::black_box(&GAP022_DATA);
        s.wrapping_add(u64::from(x))
    }

    /// The running test binary's own PDB names its data as data symbols.
    ///
    /// The static is compiled into the binary, so its PDB holds a data
    /// record for it; where the PDB applies, the record becomes a data
    /// symbol at the static's address, which a non-executable section
    /// maps. A build without a PDB on disk has nothing to read, and then
    /// nothing is asserted.
    #[test]
    fn the_test_binaries_own_pdb_names_its_data() {
        let read = gap022_data_probe(std::hint::black_box(3));
        assert!(read >= 3, "the probe ran: {read}");
        let exe = std::env::current_exe().expect("the test binary has a path");
        let bytes = std::fs::read(&exe).expect("the test binary is readable");
        if bytes.first_chunk::<2>() != Some(b"MZ") {
            return;
        }
        let pe = goblin::pe::PE::parse(&bytes).expect("the test binary is a parseable PE");
        let Some(cv) = pe
            .debug_data
            .as_ref()
            .and_then(|d| d.codeview_pdb70_debug_info.as_ref())
        else {
            return;
        };
        let record = Record::from_debug_info(cv);
        let resolved = candidates(&record, &exe, None)
            .into_iter()
            .find(|p| p.is_file());
        if resolved.is_none() {
            return;
        }
        let program = Program::load(&exe).expect("the test binary loads");
        let Some(super::Outcome::Applied { .. }) = program.pdb else {
            panic!("a matching PDB was not applied: {:?}", program.pdb)
        };
        let data = program
            .symbols
            .iter()
            .filter(|s| s.kind == SymbolKind::Data)
            .count();
        let sym = program
            .symbols
            .iter()
            .find(|s| s.kind == SymbolKind::Data && s.name.contains("GAP022_DATA"))
            .unwrap_or_else(|| {
                panic!(
                    "the static was not named as data: {} symbols, {data} data",
                    program.symbols.len()
                )
            });
        assert!(
            program.section_at(sym.addr).is_some_and(|s| !s.executable),
            "the static sits in executable memory: {sym:?}"
        );
        // The naming surface the decompiler reads: a global the PDB named
        // renders as that name, not the `gN_` synthesis an unnamed one
        // gets.
        let a = crate::analysis::Analysis::compute(&program);
        let entry = program
            .debug_functions
            .iter()
            .find(|d| d.name.contains("gap022_data_probe"))
            .map_or(0, |d| d.low_pc);
        let overlay = crate::analysis::Overlay::default();
        let text = (entry != 0)
            .then(|| crate::analysis::decompile::decompile(&program, &a, &overlay, entry))
            .flatten()
            .unwrap_or_default();
        assert!(
            text.contains("GAP022_DATA"),
            "the probe decompiled without the static's name:
{text}"
        );
    }

    /// A gather over arbitrary bytes ends without a panic.
    ///
    /// The engine is handed whatever file sits at the recorded path, so a
    /// truncated or hostile PDB has to answer with nothing, not a crash.
    #[test]
    fn a_damaged_pdb_gathers_nothing() {
        let noise: Vec<u8> = (0..4096u32).map(|k| (k * 31 % 253) as u8).collect();
        let Ok(mut db) = pdb::PDB::open(std::io::Cursor::new(noise.as_slice())) else {
            return;
        };
        // Whatever the damaged file answered for its streams is what
        // `apply` would skip it for; the gather itself must not panic on
        // either side of that.
        if let Ok(map) = db.address_map() {
            let gathered = super::gather(&mut db, &map, 8, false);
            assert!(gathered.found.is_empty(), "{gathered:?}");
        }
        if let Ok(globals) = db.global_symbols() {
            use pdb::FallibleIterator as _;
            let mut it = globals.iter();
            while let Ok(Some(s)) = it.next() {
                let _ = s.parse();
            }
        }
    }
}
