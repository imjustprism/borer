//! Writing the whole-binary exports, for `export` and `decompile_batch(out=)`.
//!
//! [`borer_engine::analysis::decompile::export`] goes to a C file, the mod
//! SDK ([`borer_engine::analysis::modsdk`]) to a C++ header, a Cheat
//! Engine table and a ReClass.NET project. The function definitions stream to a sibling `.part` file while they
//! are rendered, and the file is then written as the hoisted declarations
//! followed by that part, so memory never holds the file.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;
use std::io::Write as _;
use std::path::{Path, PathBuf};

use anyhow::Context as _;
use borer_engine::analysis::decompile::export::{BUDGET_BLOCKS, Hoisted, Library, export};
use borer_engine::analysis::{Analysis, Overlay};
use borer_engine::program::Program;
use borer_engine::text::short_path;

use crate::output::{Existing, append, create};

/// What an export wrote.
#[derive(Debug)]
pub struct Written {
    /// The hoisted declarations and the function counts.
    pub hoisted: Hoisted,
    /// Bytes in the file.
    pub bytes: u64,
    /// Requested entries no function starts at, even after gap recovery.
    pub unmatched: Vec<u64>,
}

impl Written {
    /// Says what was written, on one line.
    ///
    /// # Arguments
    ///
    /// * `out` - The file's path.
    #[must_use]
    pub fn line(&self, out: &str) -> String {
        let h = &self.hoisted;
        let cut = if h.cut == 0 {
            String::new()
        } else {
            format!(
                ", {} cut over the budget of {BUDGET_BLOCKS} blocks a function",
                h.cut
            )
        };
        let missed = if self.unmatched.is_empty() {
            String::new()
        } else {
            let list: Vec<String> = self.unmatched.iter().map(|va| format!("{va:#x}")).collect();
            format!("; no function starts at {}", list.join(", "))
        };
        format!(
            "wrote {} functions to {} ({} bytes); {} did not decompile{cut}, {} library functions and stubs left out, {} declarations stated two ways kept the first",
            h.written,
            short_path(out),
            self.bytes,
            h.failed,
            h.left_out,
            h.conflicts
        ) + missed.as_str()
    }
}

/// Exports every function of a binary as one C file at `out`.
///
/// # Arguments
///
/// * `program` - The loaded binary.
/// * `analysis` - Its analysis.
/// * `overlay` - Names, types and comments to apply.
/// * `library` - Whether library code is written.
/// * `out` - The C file to write.
/// * `existing` - Whether a regular file already at `out` is replaced;
///   a link there is never written through.
///
/// # Returns
///
/// What was written.
///
/// # Errors
///
/// When the file or its `.part` beside it cannot be written, a file is
/// at `out` and `existing` keeps it, or the request's deadline passed while
/// the functions were decompiled ([`borer_engine::cancel::Cancel`]): then
/// the `.part` is removed and whatever is at `out` stays untouched.
pub fn write_c(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    library: Library,
    out: &str,
    existing: Existing,
) -> anyhow::Result<Written> {
    write_with_set(program, analysis, overlay, library, None, out, existing)
}

/// Exports the entries in `only`, or every function when `only` is `None`.
///
/// The file is the same shape as [`write_c`]: declarations those functions
/// hoist, then their bodies. An entry that is not a written function is
/// skipped.
///
/// # Arguments
///
/// * `program` - The loaded binary.
/// * `analysis` - Its analysis.
/// * `overlay` - Names, types and comments to apply.
/// * `library` - Whether library code is written.
/// * `only` - Entries to write, or every function when `None`.
/// * `out` - The C file to write.
/// * `existing` - Whether a regular file already at `out` is replaced;
///   a link there is never written through.
///
/// # Returns
///
/// What was written.
///
/// # Errors
///
/// When the file or its `.part` beside it cannot be written, or a file
/// is at `out` and `existing` keeps it.
pub fn write_entries(
    program: &Program,
    analysis: &mut Analysis,
    overlay: &Overlay,
    library: Library,
    only: Option<&[u64]>,
    out: &str,
    existing: Existing,
) -> anyhow::Result<Written> {
    let mut unmatched = Vec::new();
    if let Some(entries) = only {
        let sorted: BTreeSet<u64> = entries.iter().copied().collect();
        for va in sorted {
            let thumb = (program.arch == borer_engine::program::Arch::Arm)
                .then(|| analysis.function(va & !1))
                .flatten();
            let known = analysis.function(va).or(thumb);
            if known.is_none() && analysis.start_gap_function(program, va).is_none() {
                unmatched.push(va);
            }
        }
    }
    let set = only.map(|entries| entries.iter().copied().collect::<BTreeSet<_>>());
    let mut written = write_with_set(
        program,
        analysis,
        overlay,
        library,
        set.as_ref(),
        out,
        existing,
    )?;
    written.unmatched = unmatched;
    Ok(written)
}

/// Writes the exported C file for `set` (or every function when `None`).
///
/// # Errors
///
/// Fails when `out` cannot be created or written, or already exists under [`Existing::Keep`].
fn write_with_set(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    library: Library,
    set: Option<&BTreeSet<u64>>,
    out: &str,
    existing: Existing,
) -> anyhow::Result<Written> {
    let path = Path::new(out);
    if let Some(why) = borer_engine::program::unusable_path(path) {
        anyhow::bail!("{why}; nothing was written");
    }
    let part_name = format!("{out}.part");
    let part = Path::new(&part_name);
    let shown = short_path(out);
    #[expect(clippy::disallowed_methods, reason = "unusable_path cleared path")]
    let occupied = existing == Existing::Keep && std::fs::symlink_metadata(path).is_ok();
    if occupied {
        anyhow::bail!("{shown} exists; nothing was written");
    }
    let mut bodies = std::io::BufWriter::new(
        create(part, Existing::Replace).with_context(|| format!("creating {shown}.part"))?,
    );
    let hoisted = export(program, analysis, overlay, library, set, &mut |text| {
        bodies
            .write_all(text.as_bytes())
            .with_context(|| format!("writing {shown}.part"))
    })?;
    bodies
        .flush()
        .with_context(|| format!("writing {shown}.part"))?;
    drop(bodies);
    if borer_engine::cancel::Cancel::raised() {
        std::fs::remove_file(part).with_context(|| format!("removing {shown}.part"))?;
        anyhow::bail!(
            "the request's deadline passed before every function was decompiled, so {shown} was left as it was; export fewer functions (a filter or a list) or raise BORER_DEADLINE_SECS"
        );
    }
    let binary = short_path(&program.path.display().to_string());
    let mut file = std::io::BufWriter::new(
        create(path, existing).with_context(|| format!("creating {shown}"))?,
    );
    file.write_all(hoisted.head(&binary).as_bytes())
        .with_context(|| format!("writing {shown}"))?;
    #[expect(
        clippy::disallowed_methods,
        reason = "the part file this export just wrote"
    )]
    let mut from = std::fs::File::open(part).with_context(|| format!("reading {shown}.part"))?;
    std::io::copy(&mut from, &mut file).with_context(|| format!("writing {shown}"))?;
    file.flush().with_context(|| format!("writing {shown}"))?;
    drop(from);
    std::fs::remove_file(part).with_context(|| format!("removing {shown}.part"))?;
    #[expect(clippy::disallowed_methods, reason = "the file this export just wrote")]
    let bytes = std::fs::metadata(path)
        .with_context(|| format!("reading {shown}"))?
        .len();
    Ok(Written {
        hoisted,
        bytes,
        unmatched: Vec::new(),
    })
}

/// A file a mod author loads, written from the program's mod SDK
/// ([`borer_engine::analysis::modsdk`]).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ModFile {
    /// A C++ header: classes, offsets, vtables and addresses (`.h`).
    Header,
    /// A Cheat Engine table of the globals and their fields (`.ct`).
    CheatTable,
    /// A ReClass.NET project of the class layouts (`.rcnet`).
    ReClass,
}

impl ModFile {
    /// Every mod file, with the extension that names it.
    pub const ALL: [(ModFile, &'static str); 3] = [
        (ModFile::Header, "h"),
        (ModFile::CheatTable, "ct"),
        (ModFile::ReClass, "rcnet"),
    ];

    /// Returns the mod file a path's extension names.
    ///
    /// # Arguments
    ///
    /// * `path` - The file to write; its extension in any case.
    ///
    /// # Returns
    ///
    /// The kind, or `None` for another extension (a `.c` export).
    #[must_use]
    pub fn of_path(path: &str) -> Option<Self> {
        let ext = Path::new(path).extension()?.to_str()?.to_ascii_lowercase();
        Self::ALL
            .iter()
            .find(|(_, e)| *e == ext)
            .map(|(kind, _)| *kind)
    }

    /// Returns what the file holds, for the line saying it was written.
    fn what(self) -> &'static str {
        match self {
            ModFile::Header => "mod SDK header",
            ModFile::CheatTable => "Cheat Engine table",
            ModFile::ReClass => "ReClass.NET project",
        }
    }
}

/// Writes the program's mod SDK as each file asked for.
///
/// The SDK is gathered once and every file rendered before any is
/// written, so a request whose deadline passes, or a file past the bytes
/// a mod file holds ([`borer_engine::analysis::modsdk::fits`]), writes
/// nothing.
///
/// # Arguments
///
/// * `program` - The loaded binary.
/// * `analysis` - Its analysis.
/// * `overlay` - Names and types, which win over what is recovered.
/// * `files` - Each file to write and its kind.
/// * `existing` - Whether a regular file already at a path is replaced;
///   a link there is never written through.
///
/// # Returns
///
/// One line per file written, and one saying what the SDK holds.
///
/// # Errors
///
/// When a path is unusable, a file is there and `existing` keeps it, a
/// file passes the bytes a mod file holds, a write fails, or the request's
/// deadline passed while the classes were read or rendered
/// ([`borer_engine::cancel::Cancel`]); the files written before a failed
/// write stay.
pub fn write_mod_files(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    files: &[(ModFile, &str)],
    existing: Existing,
) -> anyhow::Result<String> {
    use borer_engine::analysis::modsdk::{self, Evidence};
    for (_, out) in files {
        if let Some(why) = borer_engine::program::unusable_path(Path::new(out)) {
            anyhow::bail!("{why}; nothing was written");
        }
        #[expect(clippy::disallowed_methods, reason = "unusable_path cleared out")]
        let occupied = existing == Existing::Keep && std::fs::symlink_metadata(out).is_ok();
        if occupied {
            anyhow::bail!("{} exists; nothing was written", short_path(out));
        }
    }
    let cut = || {
        borer_engine::cancel::Cancel::raised().then(|| {
            anyhow::anyhow!(
                "the request's deadline passed before the mod files were ready, so nothing was written; raise BORER_DEADLINE_SECS"
            )
        })
    };
    let sdk = modsdk::build(program, analysis, overlay);
    if let Some(why) = cut() {
        return Err(why);
    }
    let mut rendered = Vec::with_capacity(files.len());
    for &(kind, out) in files {
        let bytes = match kind {
            ModFile::Header => modsdk::header::header(&sdk).into_bytes(),
            ModFile::CheatTable => modsdk::cheat::cheat_table(&sdk).into_bytes(),
            ModFile::ReClass => modsdk::reclass::reclass(&sdk)?,
        };
        if let Some(why) = cut() {
            return Err(why);
        }
        rendered.push((kind, out, modsdk::fits(&sdk, kind.what(), bytes)?));
    }
    if let Some(why) = cut() {
        return Err(why);
    }
    let mut lines = String::new();
    for (kind, out, bytes) in rendered {
        let shown = short_path(out);
        let mut file =
            create(Path::new(out), existing).with_context(|| format!("creating {shown}"))?;
        file.write_all(&bytes)
            .with_context(|| format!("writing {shown}"))?;
        let _ = writeln!(
            lines,
            "wrote the {} to {shown} ({} bytes)",
            kind.what(),
            bytes.len()
        );
    }
    let fields = sdk.classes.iter().flat_map(|c| &c.fields);
    let unsure = fields
        .clone()
        .filter(|f| matches!(f.evidence, Evidence::Unsure(_)))
        .count();
    let _ = write!(
        lines,
        "{} classes, {} fields ({unsure} unsure), {} globals, {} thread-local singletons, {} named functions",
        sdk.classes.len(),
        fields.count(),
        sdk.globals.len(),
        sdk.tls.len(),
        sdk.functions.len()
    );
    Ok(lines)
}

/// Bytes a split holds before it appends what it holds to its files.
const SPLIT_BUFFER: usize = 32 << 20;

/// The C files of a split being written: the text each holds that is not
/// on disk yet.
struct Units<'a> {
    /// The `src` directory the files go under.
    dir: &'a Path,
    /// Text by file, relative to `dir`.
    held: BTreeMap<String, String>,
    /// The files created so far.
    made: BTreeSet<String>,
    /// Bytes held.
    bytes: usize,
}

impl Units<'_> {
    /// Adds a function's text to a file, writing every file out once
    /// [`SPLIT_BUFFER`] bytes are held.
    ///
    /// # Arguments
    ///
    /// * `file` - The file, relative to the `src` directory.
    /// * `text` - The text.
    ///
    /// # Errors
    ///
    /// When a write fails.
    fn add(&mut self, file: &str, text: &str) -> anyhow::Result<()> {
        self.bytes = self.bytes.saturating_add(text.len());
        self.held.entry(file.to_owned()).or_default().push_str(text);
        if self.bytes > SPLIT_BUFFER {
            self.flush()?;
        }
        Ok(())
    }

    /// Writes out every file's held text: a file's first write creates it
    /// with its prologue, failing when a file or link is already there, and
    /// a later one appends to a regular file only. The directories on the
    /// way are checked for links first ([`no_link_under`]); one swapped in
    /// between that check and the write is not caught.
    ///
    /// # Errors
    ///
    /// When a directory or file cannot be created, or a write fails.
    fn flush(&mut self) -> anyhow::Result<()> {
        use borer_engine::analysis::split::unit_prologue;
        for (file, text) in std::mem::take(&mut self.held) {
            let path = self.dir.join(&file);
            let shown = short_path(&path.display().to_string());
            no_link_under(self.dir, &file)?;
            let mut out = if self.made.insert(file.clone()) {
                if let Some(parent) = path.parent() {
                    std::fs::create_dir_all(parent)
                        .with_context(|| format!("creating the directory of {shown}"))?;
                }
                let mut f =
                    create(&path, Existing::Keep).with_context(|| format!("creating {shown}"))?;
                f.write_all(unit_prologue(&file).as_bytes())
                    .with_context(|| format!("writing {shown}"))?;
                f
            } else {
                append(&path).with_context(|| format!("appending to {shown}"))?
            };
            out.write_all(text.as_bytes())
                .with_context(|| format!("writing {shown}"))?;
        }
        self.bytes = 0;
        Ok(())
    }
}

/// Refuses a link at `dir` or at any directory between it and the file
/// `file` names under it, as they are when it looks.
///
/// # Arguments
///
/// * `dir` - The directory the file is under.
/// * `file` - The file, relative to `dir`, `/`-separated.
///
/// # Errors
///
/// When `dir` or a directory on the way is a link, or something that is
/// not a directory.
fn no_link_under(dir: &Path, file: &str) -> anyhow::Result<()> {
    let mut at = dir.to_path_buf();
    let parts: Vec<&str> = file.split('/').collect();
    let dirs = parts.split_last().map_or(&[][..], |(_, d)| d);
    for part in std::iter::once("").chain(dirs.iter().copied()) {
        if !part.is_empty() {
            at.push(part);
        }
        #[expect(
            clippy::disallowed_methods,
            reason = "a sanitized path under the split's directory"
        )]
        let meta = std::fs::symlink_metadata(&at);
        match meta {
            Ok(m) if m.file_type().is_symlink() || !m.is_dir() => anyhow::bail!(
                "{} is a link or not a directory; nothing more was written",
                short_path(&at.display().to_string())
            ),
            _ => {}
        }
    }
    Ok(())
}

/// Writes one file of a split whole, as a new file.
///
/// # Arguments
///
/// * `path` - The file.
/// * `text` - Its bytes.
///
/// # Errors
///
/// When a file or link is already there, or the file cannot be created or
/// written.
fn write_whole(path: &Path, text: &[u8]) -> anyhow::Result<()> {
    let shown = short_path(&path.display().to_string());
    create(path, Existing::Keep)
        .with_context(|| format!("creating {shown}"))?
        .write_all(text)
        .with_context(|| format!("writing {shown}"))
}

/// Refuses a split directory that holds anything, before any work.
///
/// # Arguments
///
/// * `root` - The split's directory, cleared by
///   [`borer_engine::program::unusable_path`].
/// * `shown` - The directory as messages spell it.
///
/// # Errors
///
/// When the directory holds anything or cannot be read.
fn refuse_occupied(root: &Path, shown: &str) -> anyhow::Result<()> {
    #[expect(clippy::disallowed_methods, reason = "unusable_path cleared the root")]
    let listed = std::fs::read_dir(root);
    let occupied = match listed {
        Ok(mut d) => d.next().is_some(),
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => false,
        Err(e) => {
            return Err(e).with_context(|| format!("reading {shown}; nothing was written"));
        }
    };
    if occupied {
        anyhow::bail!(
            "{shown} is not empty; name a new or empty directory for --split; nothing was written"
        );
    }
    Ok(())
}

/// Refuses a split directory that is unusable or holds anything, so a
/// caller can ask before the analysis the split needs.
///
/// # Arguments
///
/// * `dir` - The directory as the caller named it.
///
/// # Errors
///
/// When the path is unusable ([`borer_engine::program::unusable_path`]),
/// or the directory holds anything or cannot be read.
pub fn refuse_split_dir(dir: &str) -> anyhow::Result<()> {
    let root = Path::new(dir);
    if let Some(why) = borer_engine::program::unusable_path(root) {
        anyhow::bail!("{why}; nothing was written");
    }
    refuse_occupied(root, &short_path(dir))
}

/// Creates the `src` and `include` directories of a split under its
/// directory, which [`refuse_occupied`] found new or empty.
///
/// # Arguments
///
/// * `root` - The split's directory.
///
/// # Returns
///
/// The `src` and the `include` directory.
///
/// # Errors
///
/// When one of the two cannot be created or is a link.
fn split_dirs(root: &Path) -> anyhow::Result<(PathBuf, PathBuf)> {
    let (src, include) = (root.join("src"), root.join("include"));
    for d in [&src, &include] {
        std::fs::create_dir_all(d)
            .with_context(|| format!("creating {}", short_path(&d.display().to_string())))?;
        no_link_under(d, "")?;
    }
    Ok((src, include))
}

/// Writes the export split per source file and per class into `dir`.
///
/// The C goes to `src/`: one file per source path the functions cite,
/// each function under the one it came from
/// ([`borer_engine::analysis::split::Sources::filed`]) or, a method citing
/// none, the one its class's methods cite, the functions
/// filed under none to `src/_unattributed.c`, and the hoisted
/// declarations every file includes to `src/_decls.h`. The mod SDK goes
/// to `include/`: one header per class and `include/_sdk.h` they include
/// ([`borer_engine::analysis::modsdk::header::class_headers`]). `MAP.tsv`
/// lists each class's header, its source file and the evidence
/// ([`borer_engine::analysis::split::split_map`]). Text is held in memory
/// up to [`SPLIT_BUFFER`] bytes, then appended, so memory never holds the
/// export.
///
/// # Arguments
///
/// * `program` - The loaded binary.
/// * `analysis` - Its analysis.
/// * `overlay` - Names, types and comments to apply.
/// * `library` - Whether library code is written.
/// * `only` - Entries to write, or every function when `None`.
/// * `dir` - The directory, created when missing; one holding anything is
///   refused.
///
/// # Returns
///
/// One line saying what was written.
///
/// # Errors
///
/// When the path is unusable, `include/_sdk.h` would pass the bytes a mod
/// file holds ([`borer_engine::analysis::modsdk::fits`], before anything is
/// written), the directory is not empty, a directory on the way to a file
/// is a link, a directory or file cannot be created or
/// written, or the request's deadline passed while the functions were
/// decompiled; the files written before stay, partial, and the error says
/// so.
pub fn write_split(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    library: Library,
    only: Option<&[u64]>,
    dir: &str,
) -> anyhow::Result<String> {
    use borer_engine::analysis::decompile::export::export_units;
    use borer_engine::analysis::{modsdk, split};
    refuse_split_dir(dir)?;
    let root = Path::new(dir);
    let shown = short_path(dir);
    let sdk = modsdk::build(program, analysis, overlay);
    if borer_engine::cancel::Cancel::raised() {
        anyhow::bail!(
            "the request's deadline passed while the classes were read, so nothing was written; raise BORER_DEADLINE_SECS"
        );
    }
    let mut split_headers = modsdk::header::class_headers(&sdk);
    let shared = modsdk::fits(
        &sdk,
        ModFile::Header.what(),
        std::mem::take(&mut split_headers.shared).into_bytes(),
    )?;
    let (src, include) = split_dirs(root)?;
    let mut sources = split::sources(program, analysis);
    sources.file_by_class(program, analysis, overlay, &sdk);
    let set = only.map(|e| e.iter().copied().collect::<BTreeSet<u64>>());
    let mut units = Units {
        dir: &src,
        held: BTreeMap::new(),
        made: BTreeSet::new(),
        bytes: 0,
    };
    let mut exported: BTreeMap<u64, split::Filed<'_>> = BTreeMap::new();
    let mut tally = Tally::default();
    let hoisted = export_units(
        program,
        analysis,
        overlay,
        library,
        set.as_ref(),
        &mut |entry, text, written| {
            let filed = sources.filed(entry, text);
            let path = tally.count(filed, written);
            exported.insert(entry, filed);
            let file = path
                .and_then(|p| sources.files.get(p))
                .map_or(split::REMAINDER, String::as_str);
            if let Some(note) = filed.note() {
                units.add(file, &note)?;
            }
            units.add(file, text)
        },
    )?;
    units.flush()?;
    if borer_engine::cancel::Cancel::raised() {
        anyhow::bail!(
            "the request's deadline passed before every function was decompiled, so the files under {shown} are partial; export fewer functions (--only) or raise BORER_DEADLINE_SECS"
        );
    }
    let binary = short_path(&program.path.display().to_string());
    write_whole(&src.join(split::DECLS), hoisted.head(&binary).as_bytes())?;
    let headers = &split_headers.classes;
    no_link_under(&include, split::SDK_HEADER)?;
    write_whole(&include.join(split::SDK_HEADER), &shared)?;
    for (_, file, text) in headers {
        no_link_under(&include, file)?;
        write_whole(&include.join(file), text.as_bytes())?;
    }
    let named: Vec<(&str, &str)> = headers
        .iter()
        .map(|(class, file, _)| (class.as_str(), file.as_str()))
        .collect();
    write_whole(
        &root.join("MAP.tsv"),
        split::split_map(analysis, overlay, &sdk, &named, &exported).as_bytes(),
    )?;
    let files = units.made.len() - usize::from(units.made.contains(split::REMAINDER));
    Ok(tally.said(&shown, files, &split_headers))
}

/// How many functions a split wrote, and why each it filed under no source
/// file went to [`borer_engine::analysis::split::REMAINDER`].
#[derive(Debug, Default)]
struct Tally {
    /// Functions written.
    total: usize,
    /// Functions filed under a source file by the paths they reference that
    /// did not decompile or were cut for size.
    rough: usize,
    /// Functions filed under a source file by their class, referencing none.
    by_class: usize,
    /// Of [`Tally::by_class`], those that did not decompile or were cut for
    /// size.
    class_rough: usize,
    /// The fewest methods citing the file in their own asserts of any class
    /// that filed a function, `None` when none did.
    witnesses: Option<usize>,
    /// Functions filed under none, by why.
    why: BTreeMap<String, usize>,
}

impl Tally {
    /// Counts one function.
    ///
    /// # Arguments
    ///
    /// * `filed` - Where the split files it.
    /// * `written` - How the export wrote it.
    ///
    /// # Returns
    ///
    /// The source path it is filed under, `None` for none.
    fn count<'a>(
        &mut self,
        filed: borer_engine::analysis::split::Filed<'a>,
        written: borer_engine::analysis::decompile::export::Written,
    ) -> Option<&'a str> {
        use borer_engine::analysis::decompile::export::Written;
        use borer_engine::analysis::split::Filed;
        self.total += 1;
        let (path, rough) = match filed {
            Filed::Source(path) => (Some(path), &mut self.rough),
            Filed::Class(by) => {
                self.by_class += 1;
                self.witnesses = Some(self.witnesses.map_or(by.cite, |w| w.min(by.cite)));
                (Some(by.path), &mut self.class_rough)
            }
            Filed::Nothing | Filed::Tie | Filed::Ambiguous | Filed::Unmatched | Filed::PastCap => {
                (None, &mut self.rough)
            }
        };
        let reason = match (path, written) {
            (Some(_), Written::Body) => None,
            (Some(_), Written::Failed | Written::Cut) => {
                *rough += 1;
                None
            }
            (None, Written::Body) => filed.why(),
            (None, Written::Failed) => Some("did not decompile".to_owned()),
            (None, Written::Cut) => Some("were cut for size".to_owned()),
        };
        if let Some(reason) = reason {
            *self.why.entry(reason).or_default() += 1;
        }
        path
    }

    /// Returns the line a split answers with.
    ///
    /// # Arguments
    ///
    /// * `shown` - The split's directory as messages spell it.
    /// * `files` - The source files written.
    /// * `headers` - The class headers.
    fn said(
        &self,
        shown: &str,
        files: usize,
        headers: &borer_engine::analysis::modsdk::header::ClassHeaders,
    ) -> String {
        use borer_engine::analysis::{modsdk, split};
        let left: usize = self.why.values().sum();
        let reasons = if self.why.is_empty() {
            "none".to_owned()
        } else {
            self.why
                .iter()
                .map(|(reason, n)| format!("{n} {reason}"))
                .collect::<Vec<_>>()
                .join(", ")
        };
        let rough = if self.rough > 0 {
            format!(
                "; {} of the filed did not decompile or were cut for size, filed by the one source path each references",
                self.rough
            )
        } else {
            String::new()
        };
        let past = if headers.left_out > 0 {
            format!(
                " ({} classes left out past the {} MiB or {} files the headers hold)",
                headers.left_out,
                modsdk::FILE_MAX >> 20,
                modsdk::header::HEADERS_MAX
            )
        } else {
            String::new()
        };
        let filed = self.total.saturating_sub(left);
        let how = match (self.by_class, self.witnesses, self.class_rough) {
            (0, _, _) | (_, None, _) => String::new(),
            (k, Some(least), cut) => format!(
                " ({} by the paths they reference, {k} by their class, citing none: at least {least} methods of each such class cite its file in their own asserts and none cites another, each class's count in MAP.tsv{})",
                filed.saturating_sub(k),
                if cut > 0 {
                    format!("; {cut} of those did not decompile or were cut for size")
                } else {
                    String::new()
                }
            ),
        };
        format!(
            "wrote {} functions under {shown}/src: {filed} to {files} source files{how} and {left} to {} ({reasons}){rough}; {} class headers under {shown}/include{past} and {shown}/MAP.tsv",
            self.total,
            split::REMAINDER,
            headers.classes.len(),
        )
    }
}

#[cfg(test)]
#[expect(clippy::disallowed_methods, reason = "the tests read their own files")]
mod tests {
    use super::{Existing, Library, write_c, write_entries};
    use borer_engine::analysis::{Analysis, Overlay};
    use borer_engine::program::{Arch, Program, Section};

    /// A caller and its leaf export as one file, the leaf first.
    ///
    /// The file has the prelude, the leaf's prototype once above both
    /// definitions, the name the overlay gives in force, and no `.part`
    /// file is left behind.
    ///
    /// # Panics
    ///
    /// When the file is not that.
    #[test]
    fn a_caller_and_its_leaf_export_leaves_first() {
        let mut code = vec![0xccu8; 0x20];
        code[..6].copy_from_slice(&[0xb8, 0x01, 0x00, 0x00, 0x00, 0xc3]); // ASM: mov eax, 1; ret
        code[0x10..0x1e].copy_from_slice(&[
            0x48, 0x83, 0xec, 0x28, // ASM: sub rsp, 0x28
            0xe8, 0xe7, 0xff, 0xff, 0xff, // ASM: call 0x1000
            0x48, 0x83, 0xc4, 0x28, 0xc3, // ASM: add rsp, 0x28; ret
        ]);
        let text = Section::mapped(".text", 0x1000, 0, 0x20, false, true);
        let p = Program::raw(code, Arch::X86_64, 0, Some(0x1010), vec![text]);
        let a = Analysis::compute(&p);
        let mut o = Overlay::default();
        o.names.insert(0x1000, "leaf_one".to_owned());
        let dir = std::env::temp_dir().join(format!("borer-export-{}", std::process::id()));
        std::fs::create_dir_all(&dir).expect("a temp dir");
        let out = dir.join("t.c").display().to_string();
        let written = write_c(&p, &a, &o, Library::Skip, &out, Existing::Keep).expect("writes");
        assert!(
            write_c(&p, &a, &o, Library::Skip, &out, Existing::Keep).is_err(),
            "a second write keeps the first file"
        );
        let c = std::fs::read_to_string(&out).expect("reads");
        let part_left = std::path::Path::new(&format!("{out}.part")).exists();
        std::fs::remove_dir_all(&dir).expect("cleans up");
        assert!(!part_left);
        assert_eq!(written.hoisted.written, 2, "{c}");
        assert!(c.contains("#include <stdint.h>"), "{c}");
        let leaf = c
            .find("\nuint32_t leaf_one();")
            .unwrap_or_else(|| panic!("{c}"));
        let leaf_def = c
            .find(" leaf_one()\n{\n  return 1;\n}")
            .unwrap_or_else(|| panic!("{c}"));
        let caller = c.find(" sub_1010()\n{").unwrap_or_else(|| panic!("{c}"));
        assert!(leaf < leaf_def && leaf_def < caller, "{c}");
        assert_eq!(c.matches("\nuint32_t leaf_one();").count(), 1, "{c}");
    }

    /// An `--only` entry no function starts at, even after gap recovery, is
    /// named in the summary rather than dropped without a word.
    ///
    /// # Panics
    ///
    /// When the summary does not name it.
    #[test]
    fn an_only_entry_no_function_starts_at_is_named() {
        let mut code = vec![0xccu8; 0x10];
        code[..6].copy_from_slice(&[0xb8, 0x01, 0x00, 0x00, 0x00, 0xc3]); // ASM: mov eax, 1; ret
        let text = Section::mapped(".text", 0x1000, 0, 0x10, false, true);
        let p = Program::raw(code, Arch::X86_64, 0, Some(0x1000), vec![text]);
        let mut a = Analysis::compute(&p);
        let dir = std::env::temp_dir().join(format!("borer-only-{}", std::process::id()));
        std::fs::create_dir_all(&dir).expect("a temp dir");
        let out = dir.join("o.c").display().to_string();
        let only = [0x1000, 0x1008];
        let w = write_entries(
            &p,
            &mut a,
            &Overlay::default(),
            Library::Skip,
            Some(&only),
            &out,
            Existing::Replace,
        )
        .expect("writes");
        std::fs::remove_dir_all(&dir).expect("cleans up");
        assert_eq!(w.unmatched, vec![0x1008]);
        assert!(
            w.line(&out).contains("no function starts at 0x1008"),
            "{}",
            w.line(&out)
        );
    }

    /// An export whose request's deadline has passed refuses to write.
    ///
    /// The file already at `out` stays as it was even when `existing` would
    /// replace it, no `.part` is left, and the error says how to narrow it.
    ///
    /// The flag is raised before the export runs, so every decompile in it
    /// answers that it stopped, whatever the machine's speed.
    ///
    /// # Panics
    ///
    /// When the export succeeds, touches the file or leaves the `.part`.
    #[test]
    fn an_export_past_the_deadline_leaves_the_file_as_it_was() {
        let mut code = vec![0xccu8; 0x10];
        code[..6].copy_from_slice(&[0xb8, 0x01, 0x00, 0x00, 0x00, 0xc3]); // ASM: mov eax, 1; ret
        let text = Section::mapped(".text", 0x1000, 0, 0x10, false, true);
        let p = Program::raw(code, Arch::X86_64, 0, Some(0x1000), vec![text]);
        let a = Analysis::compute(&p);
        let dir = std::env::temp_dir().join(format!("borer-cut-{}", std::process::id()));
        std::fs::create_dir_all(&dir).expect("a temp dir");
        let out = dir.join("c.c").display().to_string();
        std::fs::write(&out, "complete export").expect("writes");
        let flag = borer_engine::cancel::Cancel::new();
        flag.raise();
        let cut = flag.within(|| {
            write_c(
                &p,
                &a,
                &Overlay::default(),
                Library::Skip,
                &out,
                Existing::Replace,
            )
        });
        let kept = std::fs::read_to_string(&out).expect("reads");
        let part_left = std::path::Path::new(&format!("{out}.part")).exists();
        std::fs::remove_dir_all(&dir).expect("cleans up");
        let why = format!("{:#}", cut.expect_err("a cut export is refused"));
        assert!(why.contains("BORER_DEADLINE_SECS"), "{why}");
        assert_eq!(kept, "complete export");
        assert!(!part_left);
    }

    /// Mod files whose request's deadline has passed are refused, and none
    /// is written.
    ///
    /// # Panics
    ///
    /// When the files are written or the error does not say why.
    #[test]
    fn mod_files_past_the_deadline_are_not_written() {
        use super::{ModFile, write_mod_files};
        let text = Section::mapped(".text", 0x1000, 0, 0x10, false, true);
        let p = Program::raw(vec![0xc3; 0x10], Arch::X86_64, 0, Some(0x1000), vec![text]);
        let a = Analysis::compute(&p);
        let dir = std::env::temp_dir().join(format!("borer-mod-cut-{}", std::process::id()));
        std::fs::create_dir_all(&dir).expect("a temp dir");
        let h = dir.join("cut.h").display().to_string();
        let flag = borer_engine::cancel::Cancel::new();
        flag.raise();
        let files = [(ModFile::Header, h.as_str())];
        let cut =
            flag.within(|| write_mod_files(&p, &a, &Overlay::default(), &files, Existing::Replace));
        let written = std::path::Path::new(&h).exists();
        std::fs::remove_dir_all(&dir).expect("cleans up");
        let why = format!("{:#}", cut.expect_err("a cut export is refused"));
        assert!(why.contains("BORER_DEADLINE_SECS"), "{why}");
        assert!(!written);
    }

    /// A mod file past the bytes one holds is refused, naming the cap, and
    /// nothing is written.
    ///
    /// Two thousand globals typed by a struct of 256 fields made a Cheat
    /// Engine table of a hundred MiB, and 4096 such structs of 64 KiB arrays
    /// a ReClass.NET project of half a terabyte.
    ///
    /// # Panics
    ///
    /// When the table is written or the refusal does not name the cap.
    #[test]
    fn a_mod_file_past_its_cap_is_refused_and_not_written() {
        use super::{ModFile, write_mod_files};
        use borer_engine::analysis::utypes::{TypeExpr, build_struct};
        let text = Section::mapped(".text", 0x1000, 0, 0x10, false, true);
        let p = Program::raw(vec![0xc3; 0x10], Arch::X86_64, 0, Some(0x1000), vec![text]);
        let a = Analysis::compute(&p);
        let fields: Vec<(u64, String, TypeExpr)> = (0..256u64)
            .map(|k| (k * 4, format!("f{k}"), TypeExpr::U32))
            .collect();
        let mut o = Overlay::default();
        let big = build_struct("Big", None, &fields, &o.types, 8).expect("builds");
        o.types.insert("Big".to_owned(), big);
        for k in 0..2000u64 {
            o.applied
                .insert(0x10_0000 + k * 0x400, TypeExpr::Named("Big".to_owned()));
        }
        let dir = std::env::temp_dir().join(format!("borer-mod-cap-{}", std::process::id()));
        std::fs::create_dir_all(&dir).expect("a temp dir");
        let ct = dir.join("big.ct").display().to_string();
        let files = [(ModFile::CheatTable, ct.as_str())];
        let refused = write_mod_files(&p, &a, &o, &files, Existing::Replace);
        let written = std::path::Path::new(&ct).exists();
        std::fs::remove_dir_all(&dir).expect("cleans up");
        let why = format!("{:#}", refused.expect_err("a table past the cap"));
        assert!(
            why.contains("passes the 67108864 bytes a mod file holds"),
            "{why}"
        );
        assert!(!written);
    }

    /// Checks a C++17 file with a compiler, warnings as errors.
    ///
    /// # Arguments
    ///
    /// * `cxx` - The compiler.
    /// * `file` - The file.
    ///
    /// # Returns
    ///
    /// What the compiler said, or `None` when it does not run.
    fn syntax_check(cxx: &std::path::Path, file: &std::path::Path) -> Option<std::process::Output> {
        std::process::Command::new(cxx)
            .args(["-std=c++17", "-fsyntax-only", "-Wall", "-Werror"])
            .arg(file)
            .output()
            .ok()
    }

    /// The C++ compiler this machine has with its standard library.
    ///
    /// The first of `$CXX`, `c++`, `clang++` or `g++` on the path, and
    /// LLVM's clang++ where Windows installs it, that compiles the two
    /// headers the mod SDK includes.
    ///
    /// # Arguments
    ///
    /// * `dir` - A scratch directory for the probe.
    ///
    /// # Returns
    ///
    /// The compiler, or `None` when none does.
    fn cxx(dir: &std::path::Path) -> Option<std::path::PathBuf> {
        let probe = dir.join("probe.cpp");
        std::fs::write(&probe, "#include <cstddef>\n#include <cstdint>\n").ok()?;
        let named = std::env::var_os("CXX").map(std::path::PathBuf::from);
        let llvm = std::path::PathBuf::from(r"C:\Program Files\LLVM\bin\clang++.exe");
        named
            .into_iter()
            .chain(["c++", "clang++", "g++"].map(std::path::PathBuf::from))
            .chain([llvm])
            .find(|c| syntax_check(c, &probe).is_some_and(|o| o.status.success()))
    }

    /// The mod files of a class with a vtable, a stated struct and a
    /// global singleton are written, and the header compiles as C++17:
    /// its `static_assert`s on every offset and size hold.
    ///
    /// A member of the struct is spelled like the class a later member
    /// points at, which the header's qualified pointer types keep apart;
    /// two are spelled like the macros `<cstddef>` and `<cstdint>` define.
    ///
    /// Where no C++ compiler runs, the header is only checked for its
    /// asserts and the test says so on stderr.
    ///
    /// # Panics
    ///
    /// When a file is not written, the header lacks its asserts, or the
    /// compiler rejects it.
    #[test]
    fn the_mod_files_are_written_and_the_header_compiles() {
        use super::{ModFile, write_mod_files};
        use borer_engine::analysis::utypes::{TypeExpr, UserField, UserStruct, UserType};
        use borer_engine::analysis::vtables::ClassInfo;
        let text = Section::mapped(".text", 0x1000, 0, 0x10, false, true);
        let p = Program::raw(vec![0xc3; 0x10], Arch::X86_64, 0, Some(0x1000), vec![text]);
        let mut a = Analysis::compute(&p);
        a.classes.by_name.insert(
            "Game::Player".to_owned(),
            ClassInfo {
                name: "Game::Player".to_owned(),
                vtable: Some(0x5000),
                slots: vec![0x1000, 0],
                bases: borer_engine::analysis::vtables::Bases::default(),
                ctors: Vec::new(),
                creators: Vec::new(),
            },
        );
        a.classes
            .global_hints
            .insert(0x6000, "Game::Player".to_owned());
        let mut o = Overlay::default();
        let field = |name: &str, ty| UserField {
            name: name.to_owned(),
            ty,
        };
        let fields = [
            (0, field("hp", TypeExpr::I32)),
            (4, field("pos", TypeExpr::Array(Box::new(TypeExpr::F32), 3))),
            (0x10, field("Game_Player", TypeExpr::U8)),
            (0x11, field("NULL", TypeExpr::U8)),
            (0x12, field("INT16_MAX", TypeExpr::U16)),
            (
                0x18,
                field(
                    "owner",
                    TypeExpr::Ptr(Box::new(TypeExpr::Named("Game::Player".to_owned()))),
                ),
            ),
        ];
        o.types.insert(
            "Stats".to_owned(),
            UserType::Struct(UserStruct {
                size: 0x28,
                fields: fields.into_iter().collect(),
            }),
        );
        let dir = std::env::temp_dir().join(format!("borer-mod-{}", std::process::id()));
        std::fs::create_dir_all(&dir).expect("a temp dir");
        let path = |name: &str| dir.join(name).display().to_string();
        let (h, ct, rc) = (path("sdk.h"), path("t.CT"), path("t.rcnet"));
        let files = [
            (ModFile::of_path(&h).expect("h"), h.as_str()),
            (ModFile::of_path(&ct).expect("ct"), ct.as_str()),
            (ModFile::of_path(&rc).expect("rcnet"), rc.as_str()),
        ];
        let said = write_mod_files(&p, &a, &o, &files, Existing::Keep).expect("writes");
        assert!(
            said.contains("2 classes, 7 fields (0 unsure), 1 globals"),
            "{said}"
        );
        assert!(
            write_mod_files(&p, &a, &o, &files, Existing::Keep).is_err(),
            "a second write keeps the files"
        );
        let header = std::fs::read_to_string(&h).expect("reads");
        let table = std::fs::read_to_string(&ct).expect("reads");
        let zip = std::fs::read(&rc).expect("reads");
        assert!(
            header.contains("static_assert(offsetof(Stats, owner) == 0x18"),
            "{header}"
        );
        assert!(
            table.contains("<Address>\"module\"+6000</Address>"),
            "{table}"
        );
        assert!(zip.starts_with(b"PK\x03\x04"));
        let cpp = dir.join("use.cpp");
        std::fs::write(&cpp, "#include \"sdk.h\"\nint main() { return 0; }\n").expect("writes");
        let compiled = cxx(&dir).map(|c| syntax_check(&c, &cpp).expect("runs"));
        std::fs::remove_dir_all(&dir).expect("cleans up");
        match compiled {
            Some(out) => assert!(
                out.status.success(),
                "{}\n{header}",
                String::from_utf8_lossy(&out.stderr)
            ),
            None => {
                eprintln!("no C++ compiler runs here; the header was checked for its asserts only");
            }
        }
    }

    /// The split files a function by the source file its assert cites, the
    /// rest apart, and writes the declarations, the SDK header and the map.
    ///
    /// `main` calls `check`, whose assert cites `src/a.cpp`, and `one`,
    /// which asserts nothing.
    ///
    /// # Panics
    ///
    /// When a file is missing or holds the wrong function.
    #[test]
    fn the_split_files_a_function_by_the_source_its_assert_cites() {
        let (p, mut o) = asserting(&[("check", &["src/a.cpp"]), ("one", &[])]);
        let a = Analysis::compute(&p);
        let typed =
            borer_engine::analysis::protos::Proto::parse("int one(int count)").expect("parses");
        o.prototypes.insert(0x1100, typed);
        let dir = std::env::temp_dir().join(format!("borer-split-{}", std::process::id()));
        let said = super::write_split(
            &p,
            &a,
            &o,
            Library::Include,
            None,
            &dir.display().to_string(),
        )
        .expect("writes");
        assert_eq!(
            said,
            format!(
                "wrote 3 functions under {0}/src: 1 to 1 source files and 2 to _unattributed.c (2 cite no source file); 0 class headers under {0}/include and {0}/MAP.tsv",
                borer_engine::text::short_path(&dir.display().to_string())
            )
        );
        let read = |rel: &str| std::fs::read_to_string(dir.join(rel)).unwrap_or_default();
        let unit = read("src/a.cpp.c");
        assert!(unit.contains("#include \"_decls.h\""), "{unit}");
        assert!(unit.contains("// check @ 0x1000"), "{unit}");
        assert!(!unit.contains("// one @"), "{unit}");
        let rest = read("src/_unattributed.c");
        assert!(
            rest.contains("// one @ 0x1100") && !rest.contains("// check @"),
            "{rest}"
        );
        assert!(
            rest.contains("one(int count)") || read("src/_decls.h").contains("one(int count)"),
            "the project's typed prototype is in the C: {rest}"
        );
        assert!(read("src/_decls.h").contains("functions decompiled by borer"));
        assert!(read("include/_sdk.h").contains("namespace sdk"));
        assert!(read("MAP.tsv").contains("# class\theader\tsource\tevidence"));
        let again = super::write_split(
            &p,
            &a,
            &o,
            Library::Include,
            None,
            &dir.display().to_string(),
        )
        .expect_err("a directory holding a split is refused");
        assert!(again.to_string().contains("is not empty"), "{again}");
        std::fs::remove_dir_all(&dir).expect("cleans up");
    }

    /// Builds an image whose functions each assert once per path given,
    /// citing it, and a `main` at `0x1800` calling each in turn, with the
    /// overlay naming them.
    ///
    /// # Arguments
    ///
    /// * `funcs` - Each function's name and the paths its asserts cite, at
    ///   `0x1000`, `0x1100` and on.
    ///
    /// # Panics
    ///
    /// When the functions or their asserts do not fit the image.
    fn asserting(funcs: &[(&str, &[&str])]) -> (Program, Overlay) {
        assembled(funcs, &[])
    }

    /// Builds the image [`asserting`] builds, the asserts of each function
    /// in `signed` also passing its own signature, `void __cdecl <name>(void)`,
    /// at `0x2800`, `0x2880` and on.
    ///
    /// # Arguments
    ///
    /// * `funcs` - As for [`asserting`].
    /// * `signed` - The functions whose asserts pass their signature.
    ///
    /// # Panics
    ///
    /// When the functions or their asserts do not fit the image.
    fn assembled(funcs: &[(&str, &[&str])], signed: &[&str]) -> (Program, Overlay) {
        use borer_engine::program::{Symbol, SymbolKind};
        let mut bytes = vec![0xccu8; 0x2000];
        let rel = |at: u64, to: u64| borer_engine::num::lo32(to.wrapping_sub(at)).to_le_bytes();
        bytes[0x1008..0x100e].copy_from_slice(b"x > 0\0");
        let mut paths: Vec<&str> = Vec::new();
        let mut o = Overlay::default();
        let mut main = Vec::new();
        for (i, (name, cites)) in funcs.iter().enumerate() {
            let entry = 0x1000 + 0x100 * u64::try_from(i).expect("few");
            let mut code = Vec::new();
            for (line, path) in cites.iter().enumerate() {
                let at = paths.iter().position(|p| p == path).unwrap_or_else(|| {
                    paths.push(path);
                    paths.len() - 1
                });
                let string = 0x2040 + 0x80 * u64::try_from(at).expect("few");
                let off = usize::try_from(string - 0x1000).expect("fits");
                bytes[off..off + path.len()].copy_from_slice(path.as_bytes());
                bytes[off + path.len()] = 0;
                let here = entry + u64::try_from(code.len()).expect("fits");
                code.extend([0x48, 0x8d, 0x0d]); // ASM: lea rcx, [rip+expr]
                code.extend(rel(here + 7, 0x2008));
                code.extend([0x48, 0x8d, 0x15]); // ASM: lea rdx, [rip+path]
                code.extend(rel(here + 14, string));
                code.extend([0x41, 0xb8, u8::try_from(line).expect("few"), 0, 0, 0]); // ASM: mov r8d, line
                let mut call = here + 20;
                if signed.contains(name) {
                    let sig = 0x2800 + 0x80 * u64::try_from(i).expect("few");
                    let off = usize::try_from(sig - 0x1000).expect("fits");
                    let text = format!("void __cdecl {name}(void) ");
                    bytes[off..off + text.len()].copy_from_slice(text.as_bytes());
                    code.extend([0x4c, 0x8d, 0x0d]); // ASM: lea r9, [rip+signature]
                    code.extend(rel(call + 7, sig));
                    call += 7;
                }
                code.extend([0xff, 0x15]); // ASM: call qword [rip+iat]
                code.extend(rel(call + 6, 0x2000));
            }
            code.push(0xc3); // ASM: ret
            let off = usize::try_from(entry - 0x1000).expect("fits");
            bytes[off..off + code.len()].copy_from_slice(&code);
            let at = 0x1800 + u64::try_from(main.len()).expect("fits");
            main.push(0xe8); // ASM: call the function
            main.extend(rel(at + 5, entry));
            o.names.insert(entry, (*name).to_owned());
        }
        main.push(0xc3); // ASM: ret
        bytes[0x800..0x800 + main.len()].copy_from_slice(&main);
        let mut p = Program::raw(
            bytes,
            Arch::X86_64,
            0,
            Some(0x1800),
            vec![
                Section::mapped(".text", 0x1000, 0, 0x1000, false, true),
                Section::mapped(".rdata", 0x2000, 0x1000, 0x1000, false, false),
            ],
        );
        p.symbols.push(Symbol {
            name: "KERNEL32.dll!ReportAssertFailure".to_owned(),
            addr: 0x2000,
            kind: SymbolKind::Import,
        });
        (p, o)
    }

    /// A function citing a source file files under it however many times
    /// it cites a header, whatever the source file's extension, and the map
    /// gives its class that source.
    ///
    /// `Foo::Run` cites `C:\ws\src\foo.cxx` three times and
    /// `C:\ws\inc\vec.h` once; `Level` cites `game/level.cpp` once and
    /// `core/array.h` twice.
    ///
    /// # Panics
    ///
    /// When a function is filed elsewhere or the map names another source.
    #[test]
    fn a_cited_source_file_wins_over_a_header_in_the_split() {
        use borer_engine::analysis::utypes::{UserStruct, UserType};
        let foo = r"C:\ws\src\foo.cxx";
        let (p, mut o) = asserting(&[
            ("Foo::Run", &[foo, r"C:\ws\inc\vec.h", foo, foo]),
            ("Level", &["core/array.h", "game/level.cpp", "core/array.h"]),
        ]);
        o.types.insert(
            "Foo".to_owned(),
            UserType::Struct(UserStruct {
                size: 8,
                fields: std::collections::BTreeMap::new(),
            }),
        );
        let a = Analysis::compute(&p);
        let dir = std::env::temp_dir().join(format!("borer-split-src-{}", std::process::id()));
        super::write_split(
            &p,
            &a,
            &o,
            Library::Include,
            None,
            &dir.display().to_string(),
        )
        .expect("writes");
        let read = |rel: &str| std::fs::read_to_string(dir.join(rel)).unwrap_or_default();
        let units: Vec<String> = walk(&dir.join("src"));
        let holding = |name: &str| {
            units
                .iter()
                .filter(|u| read(&format!("src/{u}")).contains(&format!("// {name} @ ")))
                .cloned()
                .collect::<Vec<_>>()
        };
        assert_eq!(holding("Foo::Run"), vec!["src/foo.cxx.c"], "{units:?}");
        assert_eq!(holding("Level"), vec!["game/level.cpp.c"], "{units:?}");
        let map = read("MAP.tsv");
        assert!(
            map.lines().any(
                |l| l.starts_with("Foo\t") && l.split('\t').nth(2) == Some("C:/ws/src/foo.cxx")
            ),
            "{map}"
        );
        std::fs::remove_dir_all(&dir).expect("cleans up");
    }

    /// What a test split wrote: its reply with the directory spelled
    /// `<dir>`, each file under `src` with its text, and `MAP.tsv`.
    type SplitOut = (String, std::collections::BTreeMap<String, String>, String);

    /// Returns what a split of `funcs` ([`assembled`]) writes with a struct
    /// stated for each of `classes`.
    ///
    /// # Arguments
    ///
    /// * `tag` - Names the split's directory apart from other tests'.
    /// * `funcs` - The functions and what their asserts cite.
    /// * `signed` - The functions whose asserts pass their own signature.
    /// * `classes` - The classes the SDK knows.
    ///
    /// # Panics
    ///
    /// When the split is not written.
    fn split_of(
        tag: &str,
        funcs: &[(&str, &[&str])],
        signed: &[&str],
        classes: &[&str],
    ) -> SplitOut {
        use borer_engine::analysis::utypes::{UserStruct, UserType};
        let (p, mut o) = assembled(funcs, signed);
        for c in classes {
            o.types.insert(
                (*c).to_owned(),
                UserType::Struct(UserStruct {
                    size: 8,
                    fields: std::collections::BTreeMap::new(),
                }),
            );
        }
        let a = Analysis::compute(&p);
        let dir = std::env::temp_dir().join(format!("borer-split-{tag}-{}", std::process::id()));
        let shown = borer_engine::text::short_path(&dir.display().to_string());
        let said = super::write_split(
            &p,
            &a,
            &o,
            Library::Include,
            None,
            &dir.display().to_string(),
        )
        .expect("writes")
        .replace(&shown, "<dir>");
        let read = |rel: &str| std::fs::read_to_string(dir.join(rel)).unwrap_or_default();
        let units = walk(&dir.join("src"))
            .into_iter()
            .map(|u| (u.clone(), read(&format!("src/{u}"))))
            .collect();
        let map = read("MAP.tsv");
        std::fs::remove_dir_all(&dir).expect("cleans up");
        (said, units, map)
    }

    /// Returns the files of a split holding a function.
    ///
    /// # Arguments
    ///
    /// * `units` - Each file with its text.
    /// * `name` - The function.
    fn holding(units: &std::collections::BTreeMap<String, String>, name: &str) -> Vec<String> {
        units
            .iter()
            .filter(|(_, text)| text.contains(&format!("// {name} @ ")))
            .map(|(u, _)| u.clone())
            .collect()
    }

    /// A method whose asserts cite nothing is filed under the one source
    /// file two of its class's methods cite in their own asserts.
    ///
    /// The reply, the map and a comment before it in its file say it was
    /// filed by class and on how many witnesses; a class whose methods cite
    /// two files, and one with a single witness, file nothing by class.
    ///
    /// `C::a` and `C::b` cite `src/c.cpp` in their own asserts, `C::c`
    /// nothing; `D::x` cites `src/d1.cpp`, `D::y` `src/d2.cpp` and `D::z`
    /// nothing; `One::a` cites `src/one.cpp` and `One::b` nothing.
    ///
    /// # Panics
    ///
    /// When a function is filed elsewhere or the reply or map differ.
    #[test]
    fn a_method_citing_nothing_is_filed_by_its_class_and_says_so() {
        let signed = ["C::a", "C::b", "D::x", "D::y", "One::a"];
        let (said, units, map) = split_of(
            "class",
            &[
                ("C::a", &["src/c.cpp"]),
                ("C::b", &["src/c.cpp"]),
                ("C::c", &[]),
                ("D::x", &["src/d1.cpp"]),
                ("D::y", &["src/d2.cpp"]),
                ("D::z", &[]),
                ("One::a", &["src/one.cpp"]),
                ("One::b", &[]),
            ],
            &signed,
            &["C", "D", "One"],
        );
        assert_eq!(
            said,
            "wrote 9 functions under <dir>/src: 6 to 4 source files (5 by the paths they reference, 1 by their class, citing none: at least 2 methods of each such class cite its file in their own asserts and none cites another, each class's count in MAP.tsv) and 3 to _unattributed.c (3 cite no source file); 3 class headers under <dir>/include and <dir>/MAP.tsv"
        );
        assert_eq!(holding(&units, "C::c"), vec!["c.cpp.c"], "{units:?}");
        for unfiled in ["D::z", "One::b"] {
            assert_eq!(
                holding(&units, unfiled),
                vec!["_unattributed.c"],
                "{units:?}"
            );
        }
        let unit = units.get("c.cpp.c").cloned().unwrap_or_default();
        assert!(
            unit.contains("/* filed by its class C, citing no source file itself: 2 of the class's 3 methods cite this one in their own asserts and none cites another */\n// C::c @ "),
            "{unit}"
        );
        assert!(!unit.contains("*/\n// C::a @ "), "{unit}");
        let row = |class: &str| {
            map.lines()
                .find(|l| l.starts_with(&format!("{class}\t")))
                .map(|l| l.split('\t').skip(2).take(2).collect::<Vec<_>>().join("\t"))
                .unwrap_or_default()
        };
        assert_eq!(
            row("C"),
            "src/c.cpp\t2 of 3 exported methods filed under it; 1 of 3 filed under it by their class, citing none themselves: 2 methods of 3 cite it in their own asserts",
            "{map}"
        );
        assert_eq!(
            row("D"),
            "src/d1.cpp\t1 of 3 exported methods filed under it; 1 other files cited too",
            "{map}"
        );
    }

    /// The map gives a class the file most of its exported methods are
    /// filed under, those cited and those filed by class counted alike.
    ///
    /// `C::a` and `C::b` cite `src/c.cpp` in their own asserts and `C::x`
    /// and `C::y` nothing, so four are filed under it; `C::t1` to `C::t3`
    /// load `src/other.cpp` beside no signature, three filed under that.
    ///
    /// # Panics
    ///
    /// When the map names `src/other.cpp`.
    #[test]
    fn the_map_names_the_file_most_exported_methods_are_filed_under() {
        let (_, _, map) = split_of(
            "most",
            &[
                ("C::a", &["src/c.cpp"]),
                ("C::b", &["src/c.cpp"]),
                ("C::t1", &["src/other.cpp"]),
                ("C::t2", &["src/other.cpp"]),
                ("C::t3", &["src/other.cpp"]),
                ("C::x", &[]),
                ("C::y", &[]),
            ],
            &["C::a", "C::b"],
            &["C"],
        );
        let row = map
            .lines()
            .find(|l| l.starts_with("C\t"))
            .unwrap_or_default();
        assert_eq!(
            row.split('\t').skip(2).take(2).collect::<Vec<_>>(),
            vec![
                "src/c.cpp",
                "2 of 7 exported methods filed under it; 2 of 7 filed under it by their class, citing none themselves: 2 methods of 7 cite it in their own asserts; 1 other files cited too"
            ],
            "{map}"
        );
    }

    /// A class files nothing by class on paths its methods reference
    /// beside no signature of their own, on a header, or in an anonymous
    /// namespace, where two classes of two files read as one.
    ///
    /// `Foo::Tick` and `Foo::Tock` load `src/physics.cpp` with no signature
    /// (an inlined assert, a file name), `Foo::a` cites nothing; `H::a` and
    /// `H::b` cite `inc/h.h` in their own asserts, `H::c` nothing; two
    /// methods of the class `Impl` in an anonymous namespace cite `src/a.cpp` in their
    /// own asserts and a third nothing.
    ///
    /// # Panics
    ///
    /// When `Foo::a`, `H::c` or the third `Impl` method is filed by class.
    #[test]
    fn a_class_without_two_own_witnesses_of_a_source_files_nothing_by_class() {
        let anon = "`anonymous namespace'::Impl";
        let (x, y, z) = (
            format!("{anon}::x"),
            format!("{anon}::y"),
            format!("{anon}::z"),
        );
        let (said, units, _) = split_of(
            "unwitnessed",
            &[
                ("Foo::Tick", &["src/physics.cpp"]),
                ("Foo::Tock", &["src/physics.cpp"]),
                ("Foo::a", &[]),
                ("H::a", &["inc/h.h"]),
                ("H::b", &["inc/h.h"]),
                ("H::c", &[]),
            ],
            &["H::a", "H::b"],
            &["Foo", "H"],
        );
        for unfiled in ["Foo::a", "H::c"] {
            assert_eq!(
                holding(&units, unfiled),
                vec!["_unattributed.c"],
                "{units:?}"
            );
        }
        assert!(!said.contains("by their class"), "{said}");
        let (said, units, _) = split_of(
            "anonymous",
            &[(&x, &["src/a.cpp"]), (&y, &["src/a.cpp"]), (&z, &[])],
            &[&x, &y],
            &[anon],
        );
        assert_eq!(holding(&units, &z), vec!["_unattributed.c"], "{units:?}");
        assert!(!said.contains("by their class"), "{said}");
    }

    /// Lists the files under a directory, relative to it, `/`-separated.
    ///
    /// # Arguments
    ///
    /// * `dir` - The directory.
    ///
    /// # Panics
    ///
    /// When the directory cannot be listed.
    fn walk(dir: &std::path::Path) -> Vec<String> {
        let mut out = Vec::new();
        for e in std::fs::read_dir(dir).expect("lists").flatten() {
            let name = e.file_name().to_string_lossy().into_owned();
            if e.path().is_dir() {
                out.extend(walk(&e.path()).into_iter().map(|f| format!("{name}/{f}")));
            } else {
                out.push(name);
            }
        }
        out.sort();
        out
    }

    /// A split whose shared SDK header would pass the bytes a mod file
    /// holds is refused as `--h` refuses it, before anything is written.
    ///
    /// Eleven hundred stated structs with names of 62,000 characters make
    /// forward declarations past 64 MiB.
    ///
    /// # Panics
    ///
    /// When the split is written or the refusal does not name the cap.
    #[test]
    fn a_split_whose_sdk_header_passes_the_cap_is_refused() {
        use borer_engine::analysis::utypes::{UserStruct, UserType};
        let text = Section::mapped(".text", 0x1000, 0, 0x10, false, true);
        let p = Program::raw(vec![0xc3; 0x10], Arch::X86_64, 0, Some(0x1000), vec![text]);
        let a = Analysis::compute(&p);
        let mut o = Overlay::default();
        for k in 0..1100 {
            o.types.insert(
                format!("S{k}{}", "x".repeat(62_000)),
                UserType::Struct(UserStruct {
                    size: 8,
                    fields: std::collections::BTreeMap::new(),
                }),
            );
        }
        let dir = std::env::temp_dir().join(format!("borer-split-cap-{}", std::process::id()));
        let refused = super::write_split(
            &p,
            &a,
            &o,
            Library::Include,
            None,
            &dir.display().to_string(),
        );
        let written = dir.exists();
        std::fs::remove_dir_all(&dir).ok();
        let why = format!("{:#}", refused.expect_err("a header past the cap"));
        assert!(
            why.starts_with("the mod SDK header passes the 67108864 bytes a mod file holds"),
            "{why}"
        );
        assert!(!written, "nothing was written");
    }

    /// A split's tally counts each way a function is filed and written:
    /// a filed function that did not decompile or was cut is rough, and an
    /// unfiled one is counted by why, its failure or cut first.
    ///
    /// # Panics
    ///
    /// When a pair is counted another way.
    #[test]
    fn the_split_tally_counts_every_filing_and_writing() {
        use borer_engine::analysis::decompile::export::Written;
        use borer_engine::analysis::split::Filed;
        let mut tally = super::Tally::default();
        let filings = [
            Filed::Source("a.cpp"),
            Filed::Nothing,
            Filed::Tie,
            Filed::Ambiguous,
            Filed::Unmatched,
            Filed::PastCap,
        ];
        for filed in filings {
            for written in [Written::Body, Written::Failed, Written::Cut] {
                let path = tally.count(filed, written);
                assert_eq!(path, (filed == Filed::Source("a.cpp")).then_some("a.cpp"));
            }
        }
        let why: Vec<(&str, usize)> = tally.why.iter().map(|(r, n)| (r.as_str(), *n)).collect();
        assert_eq!((tally.total, tally.rough), (18, 2));
        assert_eq!(
            why,
            vec![
                ("cite a file past the 4096 a split writes", 1),
                ("cite no source file", 1),
                ("cite several and settle on none", 1),
                ("did not decompile", 5),
                ("name a cut path that fits several", 1),
                ("name a file they do not reference", 1),
                ("were cut for size", 5),
            ]
        );
    }

    /// A split's tally counts a function filed by its class apart from one
    /// filed by its paths, its failures and cuts apart from theirs, and the
    /// three counts of the reply sum to the total.
    ///
    /// # Panics
    ///
    /// When a function filed by class is counted another way.
    #[test]
    fn the_split_tally_counts_filing_by_class_apart() {
        use borer_engine::analysis::decompile::export::Written;
        use borer_engine::analysis::split::{ByClass, Filed};
        let mut tally = super::Tally::default();
        for (written, cite) in [(Written::Body, 3), (Written::Failed, 2), (Written::Cut, 4)] {
            let by = ByClass {
                path: "a.cpp",
                class: "A",
                cite,
                methods: 9,
            };
            assert_eq!(tally.count(Filed::Class(by), written), Some("a.cpp"));
        }
        tally.count(Filed::Source("a.cpp"), Written::Body);
        tally.count(Filed::Nothing, Written::Body);
        let headers = borer_engine::analysis::modsdk::header::ClassHeaders::default();
        assert_eq!(
            (tally.total, tally.by_class, tally.class_rough, tally.rough),
            (5, 3, 2, 0)
        );
        assert_eq!(
            tally.said("d", 1, &headers),
            "wrote 5 functions under d/src: 4 to 1 source files (1 by the paths they reference, 3 by their class, citing none: at least 2 methods of each such class cite its file in their own asserts and none cites another, each class's count in MAP.tsv; 2 of those did not decompile or were cut for size) and 1 to _unattributed.c (1 cite no source file); 0 class headers under d/include and d/MAP.tsv"
        );
    }

    /// A split counts a filed function over the export's block budget as
    /// rough, not as unfiled, and says so.
    ///
    /// `main` calls `small` and `big`, which each load `src/a.cpp`; `big`
    /// has more blocks than the export decompiles.
    ///
    /// # Panics
    ///
    /// When the reply differs.
    #[test]
    fn a_split_counts_a_cut_filed_function_as_rough() {
        use borer_engine::analysis::decompile::export::BUDGET_BLOCKS;
        let mut bytes = vec![0xccu8; 0x5100];
        let rel = |at: u64, to: u64| borer_engine::num::lo32(to.wrapping_sub(at)).to_le_bytes();
        let mut code = vec![0xe8]; // ASM: call small
        code.extend(rel(0x1005, 0x1040));
        code.push(0xe8); // ASM: call big
        code.extend(rel(0x100a, 0x1060));
        code.push(0xc3); // ASM: ret
        bytes[..code.len()].copy_from_slice(&code);
        for at in [0x1040u64, 0x1060] {
            let off = usize::try_from(at - 0x1000).expect("fits");
            bytes[off..off + 3].copy_from_slice(&[0x48, 0x8d, 0x15]); // ASM: lea rdx, [rip+path]
            bytes[off + 3..off + 7].copy_from_slice(&rel(at + 7, 0x6000));
            bytes[off + 7..off + 10].copy_from_slice(&[0x31, 0xc0, 0xc3]); // ASM: xor eax, eax; ret
        }
        let mut at = 0x60 + 7;
        for _ in 0..BUDGET_BLOCKS / 2 + 1 {
            bytes[at..at + 8].copy_from_slice(&[0x85, 0xc0, 0x74, 0x02, 0xff, 0xc1, 0xff, 0xc0]); // ASM: test eax, eax; je +2; inc ecx; inc eax
            at += 8;
        }
        bytes[at] = 0xc3; // ASM: ret
        bytes[0x5000..0x500a].copy_from_slice(b"src/a.cpp\0");
        let p = Program::raw(
            bytes,
            Arch::X86_64,
            0,
            Some(0x1000),
            vec![
                Section::mapped(".text", 0x1000, 0, 0x5000, false, true),
                Section::mapped(".rdata", 0x6000, 0x5000, 0x100, false, false),
            ],
        );
        let a = Analysis::compute(&p);
        let dir = std::env::temp_dir().join(format!("borer-split-cut-{}", std::process::id()));
        let said = super::write_split(
            &p,
            &a,
            &Overlay::default(),
            Library::Include,
            None,
            &dir.display().to_string(),
        );
        let unit = std::fs::read_to_string(dir.join("src/a.cpp.c")).unwrap_or_default();
        std::fs::remove_dir_all(&dir).ok();
        assert_eq!(
            said.expect("writes"),
            format!(
                "wrote 3 functions under {0}/src: 2 to 1 source files and 1 to _unattributed.c (1 cite no source file); 1 of the filed did not decompile or were cut for size, filed by the one source path each references; 0 class headers under {0}/include and {0}/MAP.tsv",
                borer_engine::text::short_path(&dir.display().to_string())
            )
        );
        assert!(unit.contains("@ 0x1060: cut, not decompiled"), "{unit}");
    }

    /// A split into a directory that holds anything is refused before the
    /// SDK is built: with the deadline already passed, which the build
    /// would answer, the refusal still names the directory.
    ///
    /// # Panics
    ///
    /// When the refusal is another or the directory is written to.
    #[test]
    fn a_full_split_directory_is_refused_before_the_build() {
        let text = Section::mapped(".text", 0x1000, 0, 0x10, false, true);
        let p = Program::raw(vec![0xc3; 0x10], Arch::X86_64, 0, Some(0x1000), vec![text]);
        let a = Analysis::compute(&p);
        let dir = std::env::temp_dir().join(format!("borer-split-full-{}", std::process::id()));
        std::fs::create_dir_all(&dir).expect("a temp dir");
        std::fs::write(dir.join("kept"), "kept").expect("written");
        let flag = borer_engine::cancel::Cancel::new();
        flag.raise();
        let refused = flag.within(|| {
            super::write_split(
                &p,
                &a,
                &Overlay::default(),
                Library::Include,
                None,
                &dir.display().to_string(),
            )
        });
        let left = walk(&dir);
        std::fs::remove_dir_all(&dir).ok();
        let why = format!("{:#}", refused.expect_err("a full directory"));
        assert!(why.contains("is not empty"), "{why}");
        assert_eq!(left, vec!["kept"]);
    }

    /// A split into a directory it cannot list is refused, and nothing is
    /// written; skipped where the user can list it anyway (root).
    ///
    /// # Panics
    ///
    /// When the split is not refused or writes into the directory.
    #[cfg(unix)]
    #[test]
    fn a_split_directory_that_cannot_be_listed_is_refused() {
        use std::os::unix::fs::PermissionsExt;
        let text = Section::mapped(".text", 0x1000, 0, 0x10, false, true);
        let p = Program::raw(vec![0xc3; 0x10], Arch::X86_64, 0, Some(0x1000), vec![text]);
        let a = Analysis::compute(&p);
        let dir = std::env::temp_dir().join(format!("borer-split-shut-{}", std::process::id()));
        std::fs::create_dir_all(&dir).expect("a temp dir");
        std::fs::write(dir.join("kept"), "kept").expect("written");
        let mode = |m| std::fs::set_permissions(&dir, std::fs::Permissions::from_mode(m));
        mode(0o300).expect("chmod");
        if std::fs::read_dir(&dir).is_err() {
            let refused = super::write_split(
                &p,
                &a,
                &Overlay::default(),
                Library::Include,
                None,
                &dir.display().to_string(),
            );
            mode(0o700).expect("chmod");
            let why = format!("{:#}", refused.expect_err("an unlistable directory"));
            assert!(why.contains("nothing was written"), "{why}");
            assert!(why.starts_with("reading "), "{why}");
            assert_eq!(walk(&dir), vec!["kept"]);
        }
        mode(0o700).expect("chmod");
        std::fs::remove_dir_all(&dir).ok();
    }

    /// Makes `link` a directory link to `target`: a symlink, or on Windows
    /// a junction where symlinks need a privilege.
    ///
    /// # Arguments
    ///
    /// * `target` - The directory linked to.
    /// * `link` - The link to create.
    ///
    /// # Returns
    ///
    /// Whether the link was made.
    fn dir_link(target: &std::path::Path, link: &std::path::Path) -> bool {
        #[cfg(unix)]
        let made = std::os::unix::fs::symlink(target, link).is_ok();
        #[cfg(windows)]
        let made = std::os::windows::fs::symlink_dir(target, link).is_ok()
            || std::process::Command::new("cmd")
                .args(["/C", "mklink", "/J"])
                .arg(link)
                .arg(target)
                .output()
                .is_ok_and(|o| o.status.success());
        made
    }

    /// A split refuses to write through a link at its `src` directory, at a
    /// directory below it on a file's first write, and at one planted
    /// before a later append; skipped where links cannot be made.
    ///
    /// # Panics
    ///
    /// When a write follows a link.
    #[test]
    fn a_split_writes_through_no_link() {
        let root = std::env::temp_dir().join(format!("borer-split-link-{}", std::process::id()));
        let away = root.join("away");
        let src = root.join("src");
        std::fs::create_dir_all(&away).expect("a temp dir");
        std::fs::create_dir_all(&src).expect("a temp dir");
        let units = |dir| super::Units {
            dir,
            held: std::collections::BTreeMap::new(),
            made: std::collections::BTreeSet::new(),
            bytes: 0,
        };
        let mut split = units(&src);
        split.add("sub/a.c", "first\n").expect("held");
        split.flush().expect("a plain directory takes the file");
        std::fs::remove_dir_all(src.join("sub")).expect("removed");
        std::fs::write(away.join("a.c"), "untouched").expect("written");
        if dir_link(&away, &src.join("sub")) {
            split.add("sub/a.c", "second\n").expect("held");
            let appended = split.flush();
            assert!(appended.is_err(), "an append went through a link");
            split.add("sub/b.c", "third\n").expect("held");
            assert!(split.flush().is_err(), "a first write went through a link");
            let linked = root.join("linked");
            assert!(dir_link(&away, &linked));
            let mut through = units(&linked);
            through.add("c.c", "fourth\n").expect("held");
            assert!(through.flush().is_err(), "the src directory is a link");
            assert_eq!(
                walk(&away),
                vec!["a.c"],
                "nothing reached the link's target"
            );
            assert_eq!(
                std::fs::read_to_string(away.join("a.c")).expect("reads"),
                "untouched"
            );
        }
        std::fs::remove_dir_all(&root).ok();
    }

    /// A split file already there when the split creates it is an error,
    /// never emptied: a source file on its first write and a whole file.
    ///
    /// # Panics
    ///
    /// When either is written over.
    #[test]
    fn a_split_file_already_there_is_never_emptied() {
        let root = std::env::temp_dir().join(format!("borer-split-kept-{}", std::process::id()));
        std::fs::create_dir_all(&root).expect("a temp dir");
        std::fs::write(root.join("a.c"), "kept").expect("written");
        std::fs::write(root.join("_decls.h"), "kept").expect("written");
        let mut split = super::Units {
            dir: &root,
            held: std::collections::BTreeMap::new(),
            made: std::collections::BTreeSet::new(),
            bytes: 0,
        };
        split.add("a.c", "new\n").expect("held");
        let first = split.flush();
        let whole = super::write_whole(&root.join("_decls.h"), b"new");
        let read = |f: &str| std::fs::read_to_string(root.join(f)).unwrap_or_default();
        let kept = (read("a.c"), read("_decls.h"));
        std::fs::remove_dir_all(&root).ok();
        assert!(first.is_err() && whole.is_err(), "{first:?} {whole:?}");
        assert_eq!(kept, ("kept".to_owned(), "kept".to_owned()));
    }

    /// A split directory that cannot be created is named escaped, as the
    /// rest of the split names its paths.
    ///
    /// `split_dirs` printed the path raw, so `--split` with an escape byte
    /// in it put that byte on the terminal.
    ///
    /// # Panics
    ///
    /// When the directory is created or its name is not escaped.
    #[test]
    fn a_split_directory_that_cannot_be_made_is_named_escaped() {
        let file = std::env::temp_dir().join(format!("borer-split-esc-{}", std::process::id()));
        std::fs::write(&file, "a file, not a directory").expect("written");
        let made = super::split_dirs(&file.join("\u{1b}[7mx"));
        std::fs::remove_file(&file).ok();
        let said = format!("{:#}", made.expect_err("a file is in the way"));
        assert!(!said.contains('\u{1b}') && said.contains("[7mx"), "{said}");
    }
}
