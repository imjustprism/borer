//! The pack commands: making a signature pack, and reporting what the
//! packs hold.

use std::fmt::Write as _;

use anyhow::{Context as _, bail};
use borer_engine::analysis::{Analysis, libnames, sigs};
use borer_engine::pack::{Pack, Packs};
use borer_engine::program::{Feature, Program};
use borer_engine::text::short_path;
use borer_engine::{libsig, script};

use super::args::arg;

/// Writes a file for a command that was asked to produce one.
///
/// # Arguments
///
/// * `path` - Where to write, as the caller gave it.
/// * `bytes` - What to write.
///
/// # Errors
///
/// When the path names a device rather than a file, or the write fails.
pub(super) fn write_file(path: &str, bytes: &[u8]) -> anyhow::Result<()> {
    writable(path)?;
    std::fs::write(path, bytes).with_context(|| format!("writing {}", short_path(path)))
}

/// Refuses a path that names a device rather than a file, before a
/// command spends an analysis on what it would write there.
///
/// # Arguments
///
/// * `path` - Where the command will write, as the caller gave it.
///
/// # Errors
///
/// When the path is empty or names a device (`NUL`, `CON`, `COM1`).
pub(super) fn writable(path: &str) -> anyhow::Result<()> {
    if let Some(why) = borer_engine::program::unusable_path(std::path::Path::new(path)) {
        bail!("{why}; nothing was written");
    }
    Ok(())
}

/// Writes the functions of static libraries, objects or IDA `.pat` signature
/// files as a pack of library signatures: `sigmake <out> <name> <library>...`.
///
/// # Arguments
///
/// * `args` - The command line, the command first.
///
/// # Errors
///
/// When an argument is missing, a library cannot be read, is neither an
/// archive, an object nor an IDA `.pat` file, or gives no function while
/// members of it are damaged (each is named on stderr), or the pack cannot
/// be written.
pub(super) fn sigmake(args: &[String]) -> anyhow::Result<()> {
    let out = arg(args, 1, "sigmake needs an output file")?;
    let name = args
        .get(2)
        .filter(|n| !n.is_empty() && !n.contains(char::is_whitespace))
        .context("sigmake needs a pack name, one word")?;
    let libraries = args
        .get(3..)
        .filter(|l| !l.is_empty())
        .context("sigmake needs at least one library or object")?;
    let mut functions = Vec::new();
    let mut files = Vec::new();
    for library in libraries {
        let bytes =
            std::fs::read(library).with_context(|| format!("reading {}", short_path(library)))?;
        let (found, damaged) = libsig::read(&bytes).with_context(|| short_path(library))?;
        for why in &damaged {
            eprintln!("borer: {}: {why}", short_path(library));
        }
        if found.is_empty() && !damaged.is_empty() {
            bail!(
                "{}: no function was read and {} member(s) are damaged (see above); nothing was written",
                short_path(library),
                damaged.len()
            );
        }
        println!("# {}: {} functions", short_path(library), found.len());
        functions.extend(found);
        files.push(
            std::path::Path::new(library)
                .file_name()
                .map_or_else(|| library.clone(), |f| f.to_string_lossy().into_owned()),
        );
    }
    let description = format!("the functions of {}", files.join(", "));
    let text = libsig::pack_text(name, &description, &functions);
    write_file(out, text.as_bytes())?;
    println!(
        "# wrote {}: {} signatures",
        short_path(out),
        text.lines().filter(|l| l.starts_with("lib ")).count()
    );
    Ok(())
}

/// Describes a pack for its author: name, version, what it is about, its
/// lines counted by section and key, and the warnings about keys borer does
/// not read.
///
/// # Arguments
///
/// * `pack` - The pack.
/// * `warnings` - What reading it reported.
pub(super) fn pack_report(pack: &Pack, warnings: &[String]) -> String {
    let mut counts: std::collections::BTreeMap<(&str, &str), usize> =
        std::collections::BTreeMap::new();
    for e in &pack.entries {
        *counts
            .entry((e.section.as_str(), e.key.as_str()))
            .or_default() += 1;
    }
    let mut out = format!(
        "# pack {} {}: {} lines in {} keys, {} warnings\n",
        pack.name,
        pack.version,
        pack.entries.len(),
        counts.len(),
        warnings.len()
    );
    if !pack.about.is_empty() {
        let _ = writeln!(out, "# {}", pack.about);
    }
    out.push_str("section\tkey\tlines\n");
    for ((section, key), n) in counts {
        let _ = writeln!(out, "{section}	{key}	{n}");
    }
    for w in warnings {
        let _ = writeln!(out, "# warning: {w}");
    }
    out
}

/// Lists the packs borer knows and whether each loads for a program, then
/// the names and scripts the loading ones give it.
///
/// # Arguments
///
/// * `program` - The program.
/// * `named` - The packs the command line and `BORER_PACKS` name.
/// * `auto` - Whether the pack directories' packs may load by themselves.
pub(super) fn packs_report(program: &Program, named: &Packs, auto: bool) -> String {
    let mut out = borer::packs::listing(program, named, auto);
    let (loaded, _) = borer::packs::for_program(program, named, auto);
    let scripts = loaded.packs.iter().any(|p| !p.scripts.is_empty());
    let names = !loaded.list("names", "fn").is_empty() || !loaded.list("names", "lib").is_empty();
    if (scripts || names) && program.arch.supports(Feature::Discover) {
        let a = Analysis::compute_with(program, loaded);
        out.push_str(&sigs::pack_names_tsv(&a.pack_names));
        out.push_str(&libnames::library_names_tsv(&a.library_names));
        out.push_str(&script::pack_scripts_tsv(&a.pack_scripts));
    }
    out
}
