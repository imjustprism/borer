//! Where packs come from: the files a user names, and the pack directories
//! whose packs load themselves for a program they fit.
//!
//! A user names packs with `--pack <file>` or `BORER_PACKS`; those load for
//! every program. A pack with a `[match]` section in a pack directory loads
//! by itself for a program every one of its `[match]` lines fits
//! ([`Pack::fit`]), so the Nebula pack reaches a Nebula game without a flag.
//! The pack directories are `BORER_PACK_DIRS` when it is set, else the user's
//! (`%APPDATA%\borer\packs`, `$XDG_CONFIG_HOME/borer/packs`,
//! `~/.config/borer/packs`) and the `packs` directory beside the executable
//! or two levels above it (a `target/release` build in the source tree).
//! `BORER_AUTO_PACKS=0` or `--no-auto-packs` turns the directories off.

use std::fmt::Write as _;
use std::path::{Path, PathBuf};
use std::sync::Arc;

use borer_engine::pack::{Fit, Pack, Packs};
use borer_engine::program::Program;

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
        let key = std::fs::canonicalize(d).unwrap_or_else(|_| d.clone());
        let fresh = !seen.contains(&key);
        seen.push(key);
        fresh
    });
    out
}

/// Reads the scripts a pack's `[scripts] run` lines name, relative to the
/// pack's own file, into the pack.
///
/// # Arguments
///
/// * `pack` - The pack, its scripts filled in place.
/// * `file` - The pack's file.
///
/// # Errors
///
/// When a script file does not read.
pub fn load_scripts(pack: &mut Pack, file: &Path) -> Result<(), String> {
    let dir = file.parent().unwrap_or_else(|| Path::new("."));
    let mut scripts = Vec::new();
    for rel in pack.script_files() {
        let path = rel
            .split(['/', '\\'])
            .filter(|part| !part.is_empty())
            .fold(dir.to_path_buf(), |p, part| p.join(part));
        let shown = borer_engine::text::short_path(&path.to_string_lossy());
        let code = std::fs::read_to_string(&path)
            .map_err(|e| format!("{}: reading script {shown}: {e}", pack.source))?;
        scripts.push((shown, code));
    }
    pack.scripts = scripts;
    Ok(())
}

/// Every pack in the pack directories, in directory then file-name order,
/// each with the file it came from as its `source`; a file that does not
/// read as a pack is skipped with a note.
///
/// # Arguments
///
/// * `notes` - Where a skipped file's reason goes.
#[must_use]
pub fn discovered(notes: &mut Vec<String>) -> Vec<Pack> {
    let mut out = Vec::new();
    for dir in dirs() {
        let Ok(entries) = std::fs::read_dir(&dir) else {
            continue;
        };
        let mut files: Vec<PathBuf> = entries
            .flatten()
            .map(|e| e.path())
            .filter(|p| p.extension().is_some_and(|e| e == EXTENSION))
            .collect();
        files.sort();
        for path in files {
            let shown = borer_engine::text::short_path(&path.to_string_lossy());
            let parsed = std::fs::read_to_string(&path)
                .map_err(|e| e.to_string())
                .and_then(|text| Pack::parse(&text, &shown))
                .and_then(|(mut pack, _)| {
                    load_scripts(&mut pack, &path)?;
                    Ok(pack)
                });
            match parsed {
                Ok(pack) => out.push(pack),
                Err(e) => notes.push(format!("skipped {shown}: {e}")),
            }
        }
    }
    out
}

/// The packs an analysis of a program runs with: the pack directories'
/// packs that fit it, then the packs the user named, so a named pack's
/// single values win.
///
/// A discovered pack is left out when the user named a pack of the same
/// name.
///
/// # Arguments
///
/// * `program` - The program.
/// * `named` - The packs the user named.
/// * `auto` - Whether the pack directories are read.
///
/// # Returns
///
/// The packs, and one line per pack that loaded by itself saying why.
#[must_use]
pub fn for_program(program: &Program, named: &Packs, auto: bool) -> (Arc<Packs>, Vec<String>) {
    let mut notes = Vec::new();
    if !auto {
        return (Arc::new(named.clone()), notes);
    }
    let mut packs: Vec<Pack> = Vec::new();
    for found in discovered(&mut Vec::new()) {
        if named.packs.iter().any(|p| p.name == found.name)
            || packs.iter().any(|p| p.name == found.name)
        {
            continue;
        }
        if found.fit(program) == Fit::Holds {
            notes.push(format!(
                "pack {} {} from {} fits: {}",
                found.name,
                found.version,
                found.source,
                found.match_lines().join(", ")
            ));
            packs.push(found);
        }
    }
    packs.extend(named.packs.iter().cloned());
    (Arc::new(Packs { packs }), notes)
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
    let found = if auto {
        discovered(&mut notes)
    } else {
        Vec::new()
    };
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
