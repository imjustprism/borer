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
    /// with its prologue, a later one appends.
    ///
    /// # Errors
    ///
    /// When a directory or file cannot be created, or a write fails.
    fn flush(&mut self) -> anyhow::Result<()> {
        use borer_engine::analysis::split::unit_prologue;
        for (file, text) in std::mem::take(&mut self.held) {
            let path = self.dir.join(&file);
            let shown = short_path(&path.display().to_string());
            let mut out = if self.made.insert(file.clone()) {
                no_link_under(self.dir, &file)?;
                if let Some(parent) = path.parent() {
                    std::fs::create_dir_all(parent)
                        .with_context(|| format!("creating the directory of {shown}"))?;
                }
                let mut f = create(&path, Existing::Replace)
                    .with_context(|| format!("creating {shown}"))?;
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

/// Refuses a link at any directory between `dir` and the file `file`
/// names under it, so a split never writes through one.
///
/// # Arguments
///
/// * `dir` - The directory the file is under.
/// * `file` - The file, relative to `dir`, `/`-separated.
///
/// # Errors
///
/// When a directory on the way is a link, or something that is not a
/// directory.
fn no_link_under(dir: &Path, file: &str) -> anyhow::Result<()> {
    let mut at = dir.to_path_buf();
    for part in file
        .split('/')
        .collect::<Vec<_>>()
        .split_last()
        .map_or(&[][..], |(_, d)| d)
    {
        at.push(part);
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

/// Writes one file of a split whole, replacing what is there.
///
/// # Arguments
///
/// * `path` - The file.
/// * `text` - Its bytes.
///
/// # Errors
///
/// When the file cannot be created or written.
fn write_whole(path: &Path, text: &[u8]) -> anyhow::Result<()> {
    let shown = short_path(&path.display().to_string());
    create(path, Existing::Replace)
        .with_context(|| format!("creating {shown}"))?
        .write_all(text)
        .with_context(|| format!("writing {shown}"))
}

/// Creates the `src` and `include` directories of a split under a new or
/// empty directory.
///
/// # Arguments
///
/// * `root` - The split's directory, cleared by
///   [`borer_engine::program::unusable_path`].
/// * `shown` - The directory as messages spell it.
///
/// # Returns
///
/// The `src` and the `include` directory.
///
/// # Errors
///
/// When the directory holds anything, or one of the two cannot be created.
fn split_dirs(root: &Path, shown: &str) -> anyhow::Result<(PathBuf, PathBuf)> {
    #[expect(clippy::disallowed_methods, reason = "unusable_path cleared the root")]
    let occupied = std::fs::read_dir(root).is_ok_and(|mut d| d.next().is_some());
    if occupied {
        anyhow::bail!(
            "{shown} is not empty; name a new or empty directory for --split; nothing was written"
        );
    }
    let (src, include) = (root.join("src"), root.join("include"));
    for d in [&src, &include] {
        std::fs::create_dir_all(d).with_context(|| format!("creating {}", d.display()))?;
    }
    Ok((src, include))
}

/// Writes the export split per source file and per class into `dir`.
///
/// The C goes to `src/`: one file per source path the functions cite,
/// each function under the one it came from
/// ([`borer_engine::analysis::split::Sources::filed`]), the functions
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
    use borer_engine::analysis::decompile::export::{Written, export_units};
    use borer_engine::analysis::{modsdk, split};
    let root = Path::new(dir);
    if let Some(why) = borer_engine::program::unusable_path(root) {
        anyhow::bail!("{why}; nothing was written");
    }
    let shown = short_path(dir);
    let sdk = modsdk::build(program, analysis, overlay);
    if borer_engine::cancel::Cancel::raised() {
        anyhow::bail!(
            "the request's deadline passed while the classes were read, so nothing was written; raise BORER_DEADLINE_SECS"
        );
    }
    let split_headers = modsdk::header::class_headers(&sdk);
    let shared = modsdk::fits(
        &sdk,
        ModFile::Header.what(),
        split_headers.shared.into_bytes(),
    )?;
    let (src, include) = split_dirs(root, &shown)?;
    let sources = split::sources(program, analysis);
    let set = only.map(|e| e.iter().copied().collect::<BTreeSet<u64>>());
    let mut units = Units {
        dir: &src,
        held: BTreeMap::new(),
        made: BTreeSet::new(),
        bytes: 0,
    };
    let mut exported: BTreeMap<u64, Option<String>> = BTreeMap::new();
    let mut why: BTreeMap<&'static str, usize> = BTreeMap::new();
    let (mut total, mut rough) = (0usize, 0usize);
    let hoisted = export_units(
        program,
        analysis,
        overlay,
        library,
        set.as_ref(),
        &mut |entry, text, written| {
            use split::Filed;
            total += 1;
            let filed = sources.filed(entry, text);
            let path = match filed {
                Filed::Source(path) => Some(path),
                Filed::Nothing
                | Filed::Tie
                | Filed::Ambiguous
                | Filed::Unmatched
                | Filed::PastCap => None,
            };
            let reason = match (path, written) {
                (Some(_), Written::Body) => None,
                (Some(_), Written::Failed | Written::Cut) => {
                    rough += 1;
                    None
                }
                (None, Written::Body) => filed.why(),
                (None, Written::Failed) => Some("did not decompile"),
                (None, Written::Cut) => Some("were cut for size"),
            };
            if let Some(reason) = reason {
                *why.entry(reason).or_default() += 1;
            }
            exported.insert(entry, path.map(str::to_owned));
            let file = path
                .and_then(|p| sources.files.get(p))
                .map_or(split::REMAINDER, String::as_str);
            units.add(file, text)
        },
    )?;
    units.flush()?;
    if borer_engine::cancel::Cancel::raised() {
        anyhow::bail!(
            "the request's deadline passed before every function was decompiled, so the files under {shown} are partial; export fewer functions (--only) or raise BORER_DEADLINE_SECS"
        );
    }
    let left: usize = why.values().sum();
    let reasons = if why.is_empty() {
        "none".to_owned()
    } else {
        why.iter()
            .map(|(reason, n)| format!("{n} {reason}"))
            .collect::<Vec<_>>()
            .join(", ")
    };
    let binary = short_path(&program.path.display().to_string());
    write_whole(&src.join(split::DECLS), hoisted.head(&binary).as_bytes())?;
    let headers = &split_headers.classes;
    write_whole(&include.join(split::SDK_HEADER), &shared)?;
    for (_, file, text) in headers {
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
    let rough = if rough > 0 {
        format!(
            "; {rough} of the filed did not decompile or were cut for size, filed by the one source path each references"
        )
    } else {
        String::new()
    };
    Ok(format!(
        "wrote {total} functions under {shown}/src: {} to {} source files and {left} to {} ({reasons}){rough}; {} class headers under {shown}/include{} and {shown}/MAP.tsv",
        total.saturating_sub(left),
        units.made.len() - usize::from(units.made.contains(split::REMAINDER)),
        split::REMAINDER,
        headers.len(),
        if split_headers.left_out > 0 {
            format!(
                " ({} classes left out past the {} MiB the headers hold)",
                split_headers.left_out,
                modsdk::FILE_MAX >> 20
            )
        } else {
            String::new()
        }
    ))
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
                parent: None,
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
        use borer_engine::program::{Symbol, SymbolKind};
        let mut bytes = vec![0xccu8; 0x2000];
        let rel = |at: u64, to: u64| borer_engine::num::lo32(to.wrapping_sub(at)).to_le_bytes();
        let mut code = vec![0x48, 0x8d, 0x0d]; // ASM: lea rcx, [rip+expr]
        code.extend(rel(0x1007, 0x2030));
        code.extend([0x48, 0x8d, 0x15]); // ASM: lea rdx, [rip+path]
        code.extend(rel(0x100e, 0x2010));
        code.extend([0x41, 0xb8, 0x07, 0, 0, 0]); // ASM: mov r8d, 7
        code.extend([0xff, 0x15]); // ASM: call qword [rip+iat]
        code.extend(rel(0x101a, 0x2000));
        code.push(0xc3); // ASM: ret
        bytes[..code.len()].copy_from_slice(&code);
        bytes[0x20..0x26].copy_from_slice(&[0xb8, 0x01, 0, 0, 0, 0xc3]); // ASM: mov eax, 1; ret
        let mut main = vec![0xe8]; // ASM: call check
        main.extend(rel(0x1045, 0x1000));
        main.push(0xe8); // ASM: call one
        main.extend(rel(0x104a, 0x1020));
        main.push(0xc3); // ASM: ret
        bytes[0x40..0x40 + main.len()].copy_from_slice(&main);
        bytes[0x1010..0x101a].copy_from_slice(b"src/a.cpp\0");
        bytes[0x1030..0x1036].copy_from_slice(b"x > 0\0");
        let mut p = Program::raw(
            bytes,
            Arch::X86_64,
            0,
            Some(0x1040),
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
        let a = Analysis::compute(&p);
        let mut o = Overlay::default();
        o.names.insert(0x1000, "check".to_owned());
        o.names.insert(0x1020, "one".to_owned());
        let typed =
            borer_engine::analysis::protos::Proto::parse("int one(int count)").expect("parses");
        o.prototypes.insert(0x1020, typed);
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
            rest.contains("// one @ 0x1020") && !rest.contains("// check @"),
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
                code.extend([0xff, 0x15]); // ASM: call qword [rip+iat]
                code.extend(rel(here + 26, 0x2000));
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
}
