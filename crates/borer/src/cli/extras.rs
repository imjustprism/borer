//! The commands that read a file for another tool or another build.
//!
//! They give its hashes, a code signature, a YARA rule, names for a
//! disassembler, its fingerprints and a diff against another build, an
//! address in every form, and encoded strings.

use anyhow::Context as _;
use borer_engine::analysis::Overlay;
use borer_engine::analysis::render;
use borer_engine::program::Feature;
use borer_engine::text::{quoted, short_path};

use super::args::arg;
use super::packs::write_file;
use super::session::{Session, open};

/// A command [`run`] answers.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(super) enum Extra {
    /// `hashes`: MD5, SHA-256, imphash, authentihash, TLSH and borer-lsh.
    Hashes,
    /// `sig <address|name>`: the shortest unique byte signature of code.
    Sig,
    /// `yara <function>[,<function>...]`: a YARA rule from functions' signatures and strings.
    Yara,
    /// `names <ida|ghidra|binja|x64dbg> [out]`: names and comments as a script or database for another tool.
    Names,
    /// `diff <other>`: which functions changed, appeared or went away in another build.
    Diff,
    /// `addr <va|rva:<n>|off:<n>>`: one place as a virtual address, relative address, file offset, section and function.
    Addr,
    /// `encoded [filter]`: base64 and hex strings that decode to text or a known file.
    Encoded,
    /// `fingerprint [out]`: function fingerprints; with out, the sidecar `diff` reads.
    Fingerprint,
}

impl Extra {
    /// Parses a command word.
    ///
    /// # Arguments
    ///
    /// * `word` - The command word.
    ///
    /// # Returns
    ///
    /// The command, or `None` when none of these has that word.
    pub(super) fn parse(word: &str) -> Option<Self> {
        Some(match word {
            "hashes" => Self::Hashes,
            "sig" => Self::Sig,
            "yara" => Self::Yara,
            "names" => Self::Names,
            "diff" => Self::Diff,
            "addr" => Self::Addr,
            "encoded" => Self::Encoded,
            "fingerprint" => Self::Fingerprint,
            _ => return None,
        })
    }

    /// The most arguments the command reads after the binary.
    pub(super) fn most_args(self) -> usize {
        match self {
            Self::Hashes => 0,
            Self::Sig
            | Self::Yara
            | Self::Diff
            | Self::Addr
            | Self::Encoded
            | Self::Fingerprint => 1,
            Self::Names => 2,
        }
    }
}

/// Runs `export`: the C file of every function and the mod files, for a
/// compiler, Cheat Engine and ReClass.NET.
///
/// # Arguments
///
/// * `args` - The command line, the command first and the binary second.
/// * `s` - The binary with its packs.
///
/// # Errors
///
/// For a bad argument, a path that names a device, an engine refusal or
/// a write that fails.
pub(super) fn export(args: &[String], s: &Session) -> anyhow::Result<()> {
    let asked = super::args::export_args(args)?;
    for out in asked.c.iter().chain(asked.mods.iter().map(|(_, out)| out)) {
        super::packs::writable(out)?;
    }
    let mut a = s.analysis(Feature::Decompile)?;
    let replace = borer::output::Existing::Replace;
    if !asked.mods.is_empty() {
        let said =
            borer::export::write_mod_files(&s.program, &a, &s.overlay, &asked.mods, replace)?;
        println!("{said}");
    }
    if let Some(out) = asked.c {
        let only = asked.only.as_deref();
        let written = borer::export::write_entries(
            &s.program,
            &mut a,
            &s.overlay,
            asked.library,
            only,
            out,
            replace,
        )?;
        println!("{}", written.line(out));
    }
    Ok(())
}

/// Runs one of these commands against an open binary.
///
/// # Arguments
///
/// * `cmd` - The command.
/// * `args` - The command line, the command first and the binary second.
/// * `s` - The binary with its packs.
///
/// # Errors
///
/// For a missing or bad argument, a file that cannot be read or written,
/// or an engine refusal.
pub(super) fn run(cmd: Extra, args: &[String], s: &Session) -> anyhow::Result<()> {
    match cmd {
        Extra::Fingerprint => {
            let a = s.analysis(Feature::Discover)?;
            let text = render::fingerprint_tsv(&a);
            match args.get(2) {
                Some(out) => {
                    write_file(out, text.as_bytes())?;
                    println!(
                        "wrote {} fingerprints to {} ({} bytes); borer://diff/{} reads it",
                        a.functions.len(),
                        short_path(out),
                        text.len(),
                        short_path(out)
                    );
                }
                None => print!("{text}"),
            }
        }
        Extra::Hashes => print!("{}", borer_engine::hashing::hashes_tsv(&s.program)),
        Extra::Sig => {
            let a = s.analysis(Feature::Discover)?;
            let va = s.address(arg(args, 2, "sig needs an address or name")?)?;
            print!(
                "{}",
                render::signature_tsv(&s.program, &a, &s.overlay, va)
                    .map_err(anyhow::Error::msg)?
            );
        }
        Extra::Yara => {
            let a = s.analysis(Feature::Discover)?;
            let list = arg(args, 2, "yara needs functions: <function>[,<function>...]")?;
            let entries = list
                .split(',')
                .map(str::trim)
                .filter(|f| !f.is_empty())
                .map(|f| s.address(f))
                .collect::<anyhow::Result<Vec<u64>>>()?;
            print!(
                "{}",
                render::yara_rule(&s.program, &a, &s.overlay, &entries)
                    .map_err(anyhow::Error::msg)?
            );
        }
        Extra::Names => {
            let a = s.analysis(Feature::Discover)?;
            let word = arg(args, 2, "names needs a tool: ida, ghidra, binja or x64dbg")?;
            let tool = render::Tool::parse(word).with_context(|| {
                format!(
                    "unknown tool {}; use one of: {}",
                    quoted(word),
                    render::Tool::NAMES
                )
            })?;
            let text = render::names_export(&s.program, &a, &s.overlay, tool);
            match args.get(3) {
                Some(out) => {
                    write_file(out, text.as_bytes())?;
                    println!("wrote {} ({} bytes)", short_path(out), text.len());
                }
                None => print!("{text}"),
            }
        }
        Extra::Diff => diff(args, s)?,
        Extra::Addr => {
            let a = s.analysis(Feature::Discover)?;
            let what = arg(args, 2, "addr needs a virtual address, rva:<n> or off:<n>")?;
            print!(
                "{}",
                borer_engine::fileinfo::locate(&s.program, Some(&a), &s.overlay, what)
                    .map_err(anyhow::Error::msg)?
            );
        }
        Extra::Encoded => {
            let filter = args.get(2).map_or("", String::as_str);
            print!(
                "{}",
                render::encoded_strings_tsv(&render::encoded_strings(&s.program), filter)
            );
        }
    }
    Ok(())
}

/// `diff <other>`: the functions another build, or a fingerprint sidecar,
/// changed, added or removed against this one.
///
/// # Arguments
///
/// * `args` - The command line, the command first and the binary second.
/// * `s` - The binary with its packs.
///
/// # Errors
///
/// When the other build is missing or cannot be loaded.
fn diff(args: &[String], s: &Session) -> anyhow::Result<()> {
    let a = s.analysis(Feature::Discover)?;
    let other = arg(args, 2, "diff needs another build or a fingerprint sidecar")?;
    let path = std::path::Path::new(other);
    let label = |p: &std::path::Path| {
        p.file_name().map_or_else(
            || p.display().to_string(),
            |n| n.to_string_lossy().into_owned(),
        )
    };
    let sidecar = std::fs::read_to_string(path)
        .ok()
        .filter(|t| t.starts_with("# borer fingerprint"));
    let text = match sidecar {
        Some(prints) => render::diff_prints_tsv(
            &render::prints_of(&a),
            &render::parse_prints(&prints),
            &label(&s.program.path),
            &label(path),
        ),
        None => {
            let (named, program) = open(&["diff".to_owned(), other.to_owned()], &s.loading)?;
            let theirs = Session::fit(program, &named, Overlay::default(), s.loading.clone())
                .analysis(Feature::Discover)?;
            render::diff_tsv(&a, &theirs, &label(&s.program.path), &label(path))
        }
    };
    print!("{text}");
    Ok(())
}
