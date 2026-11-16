//! Where packs come from: the files a user names, and the pack directories
//! whose packs load themselves for a program they fit.
//!
//! A user names packs with `--pack <file>` or `BORER_PACKS`; those load for
//! every program. A pack with a `[match]` section in a pack directory loads
//! by itself for a program every one of its `[match]` lines fits
//! ([`borer_engine::pack::Pack::fit`]), so a matching program picks the
//! pack up without a flag. The pack directories are `BORER_PACK_DIRS` when
//! it is set, else the user's
//! (`%APPDATA%\borer\packs`, `$XDG_CONFIG_HOME/borer/packs`,
//! `~/.config/borer/packs`) and the `packs` directory beside the executable
//! or two levels above it (a `target/release` build in the source tree).
//! `BORER_AUTO_PACKS=0` or `--no-auto-packs` turns the directories off.

use std::fmt::Write as _;
use std::path::{Path, PathBuf};
use std::sync::Arc;

use borer_engine::pack::{Fit, Packs};
use borer_engine::program::Program;
use borer_engine::session;
pub use borer_engine::session::{PACK_MAX, load_scripts};

/// The variable naming the pack directories.
pub const DIRS_ENV: &str = "BORER_PACK_DIRS";
/// The variable that turns the pack directories off when it is `0`.
pub const AUTO_ENV: &str = "BORER_AUTO_PACKS";
/// The extension of a pack file.
pub const EXTENSION: &str = "borer";

/// Tells whether packs in the pack directories may load by themselves.
#[must_use]
pub fn auto_enabled() -> bool {
    std::env::var(AUTO_ENV).map_or(true, |v| v != "0")
}

/// The paths an environment variable lists, as the platform writes a path
/// list (`;` on Windows, `:` elsewhere), empty entries dropped.
///
/// # Arguments
///
/// * `var` - The variable's name.
///
/// # Returns
///
/// The paths, or `None` when the variable is not set.
#[must_use]
pub fn env_paths(var: &str) -> Option<Vec<PathBuf>> {
    let list = std::env::var_os(var)?;
    Some(
        std::env::split_paths(&list)
            .filter(|p| !p.as_os_str().is_empty())
            .collect(),
    )
}

/// The pack directories, in search order, each once.
///
/// One that names a share or a device
/// ([`borer_engine::program::unusable_path`]) is listed as given and never
/// touched: [`pack_files`] skips it with a note.
#[must_use]
pub fn dirs() -> Vec<PathBuf> {
    let mut out: Vec<PathBuf> = Vec::new();
    if let Some(listed) = env_paths(DIRS_ENV) {
        out.extend(listed);
    } else {
        let config = std::env::var_os("APPDATA")
            .or_else(|| std::env::var_os("XDG_CONFIG_HOME"))
            .map(PathBuf::from)
            .or_else(|| std::env::var_os("HOME").map(|h| PathBuf::from(h).join(".config")));
        if let Some(base) = config {
            out.push(base.join("borer").join("packs"));
        }
        if let Ok(exe) = std::env::current_exe()
            && let Some(dir) = exe.parent()
        {
            out.push(dir.join("packs"));
            if let Some(tree) = dir.parent().and_then(Path::parent) {
                out.push(tree.join("packs"));
            }
        }
    }
    let mut seen: Vec<PathBuf> = Vec::new();
    out.retain(|d| {
        let key = if borer_engine::program::unusable_path(d).is_some() {
            d.clone()
        } else {
            #[expect(clippy::disallowed_methods, reason = "unusable_path just cleared d")]
            std::fs::canonicalize(d).unwrap_or_else(|_| d.clone())
        };
        let fresh = !seen.contains(&key);
        seen.push(key);
        fresh
    });
    out
}

/// The pack files in the pack directories, in directory then file-name
/// order: what [`session::read_found`] reads, and none when the
/// directories are off.
///
/// A directory that names a share or a device is skipped with a note,
/// unread.
///
/// # Arguments
///
/// * `auto` - Whether the pack directories are read.
/// * `notes` - Where a skipped directory's reason goes.
#[must_use]
pub fn pack_files(auto: bool, notes: &mut Vec<String>) -> Vec<PathBuf> {
    let mut out = Vec::new();
    if !auto {
        return out;
    }
    for dir in dirs() {
        if let Some(why) = borer_engine::program::unusable_path(&dir) {
            notes.push(format!("skipped a pack directory: {why}"));
            continue;
        }
        #[expect(clippy::disallowed_methods, reason = "unusable_path just cleared dir")]
        let Ok(entries) = std::fs::read_dir(&dir) else {
            continue;
        };
        let mut files: Vec<PathBuf> = entries
            .flatten()
            .map(|e| e.path())
            .filter(|p| p.extension().is_some_and(|e| e == EXTENSION))
            .collect();
        files.sort();
        out.extend(files);
    }
    out
}

/// The packs an analysis of a program runs with: the pack directories'
/// packs that fit it, then the packs the user named
/// ([`session::fitting`]).
///
/// # Arguments
///
/// * `program` - The program.
/// * `named` - The packs the user named.
/// * `auto` - Whether the pack directories are read.
///
/// # Returns
///
/// The packs, and one line per skipped pack directory or pack and per pack
/// that loaded by itself saying why.
#[must_use]
pub fn for_program(program: &Program, named: &Packs, auto: bool) -> (Arc<Packs>, Vec<String>) {
    let mut notes = Vec::new();
    let found = session::read_found(&pack_files(auto, &mut notes), &mut notes);
    let packs = session::fitting(program, named, found, &mut notes);
    (Arc::new(packs), notes)
}

/// The packs borer knows of and how each fits a program, as a table: the
/// ones the user named, then every pack in the pack directories.
///
/// # Arguments
///
/// * `program` - The program.
/// * `named` - The packs the user named.
/// * `auto` - Whether the pack directories are read.
#[must_use]
pub fn listing(program: &Program, named: &Packs, auto: bool) -> String {
    let mut notes = Vec::new();
    let found = session::read_found(&pack_files(auto, &mut notes), &mut notes);
    let dirs: Vec<String> = dirs()
        .iter()
        .map(|d| borer_engine::text::short_path(&d.to_string_lossy()))
        .collect();
    let mut out = format!(
        "# {} named, {} in the pack directories ({}){}\n",
        named.packs.len(),
        found.len(),
        if dirs.is_empty() {
            "none".to_owned()
        } else {
            dirs.join(", ")
        },
        if auto { "" } else { "; directories off" }
    );
    for note in &notes {
        let _ = writeln!(out, "# {note}");
    }
    out.push_str("pack\tversion\tfile\tloads\tmatch\n");
    let or_dash = |lines: Vec<String>| {
        if lines.is_empty() {
            "-".to_owned()
        } else {
            lines.join(", ")
        }
    };
    for p in &named.packs {
        let _ = writeln!(
            out,
            "{}\t{}\t{}\tyes: named\t{}",
            p.name,
            p.version,
            p.source,
            or_dash(p.match_lines())
        );
    }
    let mut loaded: Vec<&str> = named.packs.iter().map(|p| p.name.as_str()).collect();
    for p in &found {
        let fit = p.fit(program);
        let loads = if loaded.contains(&p.name.as_str()) {
            "no: a pack of its name loads"
        } else {
            match fit {
                Fit::Holds => {
                    loaded.push(&p.name);
                    "yes"
                }
                Fit::Unconditional => "no: no [match] lines",
                Fit::Fails(_) => "no",
            }
        };
        let why = match fit {
            Fit::Fails(line) => format!("fails {line}"),
            _ => or_dash(p.match_lines()),
        };
        let _ = writeln!(
            out,
            "{}\t{}\t{}\t{loads}\t{why}",
            p.name, p.version, p.source
        );
    }
    out
}
