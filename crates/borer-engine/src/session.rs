//! Opening a binary the way a front end does: the file within a size cap,
//! its companion PDB from beside it or a symbol cache, and the packs in
//! the pack directories that fit it.
//!
//! The engine reads every file here through the checked reader
//! ([`read_regular`]) and writes none; it reads no environment variable and
//! fetches nothing. Which pack directories to read, where the symbol cache
//! is and how large a file may be are the front end's to say ([`Open`]).

use std::path::{Path, PathBuf};
use std::sync::Arc;

use crate::layout::Layout;
use crate::pack::{Fit, Pack, Packs};
use crate::program::{Program, read_regular, unusable_path};

/// The extension of a pack file.
pub const EXTENSION: &str = "borer";
/// Largest pack file read, in bytes: 64 MiB.
pub const PACK_MAX: u64 = 1 << 26;
/// Most scripts one pack runs.
pub const SCRIPTS_MAX: usize = 64;
/// Most bytes the scripts one pack runs hold together: 4 MiB.
pub const SCRIPT_BYTES_MAX: u64 = 1 << 22;

/// Where a binary's companion PDB is looked for. The engine only reads a
/// PDB already on disk; fetching one is the front end's.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Pdb {
    /// No PDB applies.
    Off,
    /// A PDB beside the binary or at the path it records applies.
    Beside,
    /// As [`Pdb::Beside`], and one in the symbol-server cache at this root.
    Cache(PathBuf),
}

/// How to open a binary ([`open`]).
#[derive(Debug, Clone)]
pub struct Open {
    /// Most bytes the file may hold.
    pub max_file: u64,
    /// Where its companion PDB is looked for; a raw layout reads none.
    pub pdb: Pdb,
    /// The packs the user named, which load for every program.
    pub named: Arc<Packs>,
    /// The pack directories, in search order ([`read_dirs`]); a pack
    /// there loads only for a program its `[match]` lines fit.
    pub dirs: Vec<PathBuf>,
    /// Where a raw file's bytes go; `None` reads its headers.
    pub layout: Option<Layout>,
}

/// A binary opened ([`open`]): the program and the packs its analysis runs
/// with ([`crate::analysis::Analysis::compute_with`]).
#[derive(Debug)]
pub struct Opened {
    /// The loaded file.
    pub program: Program,
    /// The found packs that fit it, then the named ones.
    pub packs: Arc<Packs>,
    /// One line per pack directory or file skipped and per pack that
    /// loaded by itself,
    /// saying why.
    pub notes: Vec<String>,
}

/// Opens a binary and fits its packs to it.
///
/// # Arguments
///
/// * `path` - The file, or `<file>@<offset>`.
/// * `how` - How to open it.
///
/// # Returns
///
/// The program, its packs and the notes on them ([`Opened`]).
///
/// # Errors
///
/// As [`Program::load_with_symsrv_max`], or [`Program::load_layout_max`]
/// with a layout: a file past [`Open::max_file`] bytes is a
/// [`crate::program::TooLarge`]. A pack file that does not read is a note,
/// not an error.
pub fn open(path: &Path, how: &Open) -> anyhow::Result<Opened> {
    let program = match &how.layout {
        Some(layout) => Program::load_layout_max(path, layout, how.max_file)?,
        None => {
            let cache = match &how.pdb {
                Pdb::Cache(root) => Some(root.as_path()),
                Pdb::Off | Pdb::Beside => None,
            };
            Program::load_with_symsrv_max(path, how.pdb != Pdb::Off, cache, how.max_file)?
        }
    };
    let mut notes = Vec::new();
    let found = read_dirs(&how.dirs, &mut notes);
    let packs = Arc::new(fitting(&program, &how.named, found, &mut notes));
    Ok(Opened {
        program,
        packs,
        notes,
    })
}

/// Reads the scripts a pack's `[scripts] run` lines name, relative to the
/// pack's own file, into the pack.
///
/// A line's words are joined to the pack's directory, so its `..` climbs
/// from there, and each script is read by [`read_regular`], which refuses a
/// share, a device and anything else that is not a regular file before it
/// is opened. A pack runs at most [`SCRIPTS_MAX`] scripts holding
/// [`SCRIPT_BYTES_MAX`] bytes together: one that ran itself 100,000 times
/// read its own file as often.
///
/// # Arguments
///
/// * `pack` - The pack, its scripts filled in place.
/// * `file` - The pack's file.
///
/// # Errors
///
/// When the pack names more than [`SCRIPTS_MAX`] scripts, a script's path
/// is refused or the file does not read as text, or the scripts hold more
/// than [`SCRIPT_BYTES_MAX`] bytes.
pub fn load_scripts(pack: &mut Pack, file: &Path) -> Result<(), String> {
    let dir = file.parent().unwrap_or_else(|| Path::new("."));
    let files = pack.script_files();
    if files.len() > SCRIPTS_MAX {
        return Err(format!(
            "{}: {} scripts, past the {SCRIPTS_MAX} a pack may run",
            pack.source,
            files.len()
        ));
    }
    let mut total = 0u64;
    let mut scripts = Vec::with_capacity(files.len());
    for rel in files {
        let path = rel
            .split(['/', '\\'])
            .filter(|part| !part.is_empty())
            .fold(dir.to_path_buf(), |p, part| p.join(part));
        let shown = crate::text::short_path(&path.to_string_lossy());
        let bytes = read_regular(&path, SCRIPT_BYTES_MAX)
            .map_err(|e| format!("{}: script {e:#}", pack.source))?;
        total = total.saturating_add(crate::num::from_usize(bytes.len()));
        if total > SCRIPT_BYTES_MAX {
            return Err(format!(
                "{}: scripts hold {total} bytes, past the {SCRIPT_BYTES_MAX} a pack's scripts may hold",
                pack.source
            ));
        }
        let code = String::from_utf8(bytes)
            .map_err(|_| format!("{}: script {shown} is not text", pack.source))?;
        scripts.push((shown, code));
    }
    pack.scripts = scripts;
    Ok(())
}

/// Reads the packs in the pack directories, a directory at a time and
/// its `.borer` files in name order, each with the file it came from as
/// its `source` and its scripts read ([`load_scripts`]).
///
/// A directory that names a share or a device is skipped with a note,
/// unread, and one that cannot be listed is passed over; a file that does
/// not read as a pack is skipped with a note. The notes come in the order
/// the directories and files are read.
///
/// # Arguments
///
/// * `dirs` - The pack directories, in search order.
/// * `notes` - Takes a line for each directory or file skipped, saying why.
///
/// # Returns
///
/// The packs that read, in the order they were read.
#[must_use]
pub fn read_dirs(dirs: &[PathBuf], notes: &mut Vec<String>) -> Vec<Pack> {
    let mut out = Vec::new();
    for dir in dirs {
        if let Some(why) = unusable_path(dir) {
            notes.push(format!("skipped a pack directory: {why}"));
            continue;
        }
        #[expect(clippy::disallowed_methods, reason = "unusable_path just cleared dir")]
        let Ok(entries) = std::fs::read_dir(dir) else {
            continue;
        };
        let mut files: Vec<PathBuf> = entries
            .flatten()
            .map(|e| e.path())
            .filter(|p| p.extension().is_some_and(|e| e == EXTENSION))
            .collect();
        files.sort();
        for path in &files {
            match read_pack(path) {
                Ok(pack) => out.push(pack),
                Err(e) => notes.push(format!(
                    "skipped {}: {e}",
                    crate::text::short_path(&path.to_string_lossy())
                )),
            }
        }
    }
    out
}

/// Reads one pack file found in a pack directory, its scripts with it.
///
/// # Arguments
///
/// * `path` - The pack file.
///
/// # Errors
///
/// When the file does not read, is not text or not a pack, or its scripts
/// are refused ([`load_scripts`]).
fn read_pack(path: &Path) -> Result<Pack, String> {
    let shown = crate::text::short_path(&path.to_string_lossy());
    let bytes = read_regular(path, PACK_MAX).map_err(|e| format!("{e:#}"))?;
    let text = String::from_utf8(bytes).map_err(|_| "not text".to_owned())?;
    let (mut pack, _) = Pack::parse(&text, &shown)?;
    load_scripts(&mut pack, path)?;
    Ok(pack)
}

/// The packs an analysis of a program runs with: the found packs that fit
/// it, then the packs the user named, so a named pack's single values win.
///
/// A found pack is left out when the user named a pack of the same name,
/// or an earlier found pack has it.
///
/// # Arguments
///
/// * `program` - The program.
/// * `named` - The packs the user named.
/// * `found` - The packs found in the pack directories ([`read_dirs`]).
/// * `notes` - Takes a line for each found pack that fits, naming its
///   `[match]` lines.
#[must_use]
pub fn fitting(
    program: &Program,
    named: &Packs,
    found: Vec<Pack>,
    notes: &mut Vec<String>,
) -> Packs {
    let mut packs: Vec<Pack> = Vec::new();
    for pack in found {
        if named.packs.iter().any(|p| p.name == pack.name)
            || packs.iter().any(|p| p.name == pack.name)
        {
            continue;
        }
        if pack.fit(program) == Fit::Holds {
            notes.push(format!(
                "pack {} {} from {} fits: {}",
                pack.name,
                pack.version,
                pack.source,
                pack.match_lines().join(", ")
            ));
            packs.push(pack);
        }
    }
    packs.extend(named.packs.iter().cloned());
    Packs { packs }
}
