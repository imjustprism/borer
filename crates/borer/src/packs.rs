//! Where packs come from: the files a user names, and the pack directories
//! whose packs load themselves for a program they fit.
//!
//! A user names packs with `--pack <file>` or `BORER_PACKS`; those load for
//! every program. A pack with a `[match]` section in a pack directory loads
//! by itself for a program every one of its `[match]` lines fits
//! ([`borer_engine::pack::Pack::fit`]), so a matching program picks the
//! pack up without a flag. The pack directories are `BORER_PACK_DIRS` when
//! it is set (set empty, it lists none), else the user's
//! (`%APPDATA%\borer\packs`, `$XDG_CONFIG_HOME/borer/packs`,
//! `~/.config/borer/packs`) and the `packs` directory beside the executable
//! or two levels above it (a `target/release` build in the source tree).
//! `BORER_AUTO_PACKS=0` or `--no-auto-packs` turns the directories off.

use std::fmt::Write as _;
use std::sync::Arc;

use borer_engine::pack::{Fit, Packs};
use borer_engine::program::Program;
use borer_engine::session;
pub use borer_engine::session::{PACK_MAX, load_scripts};
pub use borer_front::places::{AUTO_ENV, DIRS_ENV, auto_enabled, dirs, env_paths, searched};

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
    let found = session::read_dirs(&searched(auto), &mut notes);
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
    let found = session::read_dirs(&searched(auto), &mut notes);
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
