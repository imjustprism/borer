//! The binary a command opens: its program, analysis and names, read once
//! per command.

use std::sync::Arc;

use anyhow::{Context as _, bail};
use borer_engine::analysis::{Analysis, Overlay, decompile, parse_addr, resolve_suggesting};
use borer_engine::layout::Layout;
use borer_engine::pack::Packs;
use borer_engine::program::{Feature, Program};
use borer_engine::text::short_path;

use super::USAGE;
use super::args::{arg, command_usage, decompile_args, entry_at};
use crate::params::Detail;
use crate::state::read_packs;
use crate::tools::decompile::window;

/// The refusal of a command given no binary: what it needs, then its own
/// usage lines rather than every command's.
///
/// # Arguments
///
/// * `word` - The command word.
pub(super) fn needs_a_binary(word: &str) -> String {
    format!(
        "{word} needs a binary path\n{}",
        command_usage(USAGE, word).unwrap_or_default()
    )
}

/// Reads the named packs and loads the binary the command line names.
///
/// # Arguments
///
/// * `args` - The command line, the command first and the binary second.
/// * `pack_files` - The pack files to read.
/// * `apply_pdb` - Whether a companion PDB's symbols may apply.
/// * `layout` - Where a raw file's bytes map; `None` reads its headers.
///
/// # Returns
///
/// The named packs and the loaded program.
///
/// # Errors
///
/// When a pack cannot be read, no binary is named, or it does not load.
pub(super) fn open(
    args: &[String],
    pack_files: &[String],
    apply_pdb: bool,
    layout: Option<&Layout>,
) -> anyhow::Result<(Arc<Packs>, Program)> {
    let named = read_packs(pack_files)?;
    let path = args
        .get(1)
        .with_context(|| needs_a_binary(args.first().map_or("", String::as_str)))?;
    let file = std::path::Path::new(path);
    crate::tools::load::file_fits(
        file,
        crate::tools::load::max_file_size(
            std::env::var(crate::tools::load::MAX_FILE_ENV)
                .ok()
                .as_deref(),
        ),
    )
    .map_err(anyhow::Error::msg)?;
    crate::term::busy(&format!("loading {}", file_name(file)), &head_bytes(file));
    let program = match layout {
        Some(layout) => Program::load_layout(file, layout),
        None => {
            let symsrv = crate::symsrv::cache_dir().filter(|_| apply_pdb);
            Program::load_with_symsrv(file, apply_pdb, symsrv.as_deref())
        }
    }
    .with_context(|| format!("loading {}", short_path(path)))?;
    Ok((named, program))
}

/// A file's name without its folder, for the loading line.
///
/// # Arguments
///
/// * `file` - The path.
pub(super) fn file_name(file: &std::path::Path) -> String {
    file.file_name()
        .map_or_else(|| file.to_string_lossy(), |n| n.to_string_lossy())
        .into_owned()
}

/// The first bytes of a file, for the loading line to stream; none when it
/// cannot be read.
///
/// # Arguments
///
/// * `file` - The binary.
fn head_bytes(file: &std::path::Path) -> Vec<u8> {
    use std::io::Read as _;
    let mut head = Vec::with_capacity(256);
    if let Ok(f) = std::fs::File::open(file) {
        let _ = f.take(256).read_to_end(&mut head);
    }
    head
}

/// A binary with the packs that fit it, as every query reads it.
#[derive(Debug)]
pub(super) struct Session {
    /// The loaded file.
    pub(super) program: Arc<Program>,
    /// The packs the analysis runs with: the named ones, and the pack
    /// directories' that fit the program.
    pub(super) packs: Arc<Packs>,
    /// The names, comments and types: a `--project` file's, else none.
    pub(super) overlay: Overlay,
}

/// Reads a project file into the overlay a query applies.
///
/// As the `load_project` tool does, a project saved for another build is
/// refused, and the annotations no section of the binary can hold are
/// left out and counted on stderr.
///
/// # Arguments
///
/// * `path` - The project file, as `save_project` writes it.
/// * `program` - The binary the query reads.
///
/// # Returns
///
/// The overlay.
///
/// # Errors
///
/// When the file cannot be read or parsed, states something an overlay
/// cannot hold, or was saved for another binary.
pub(super) fn project_overlay(path: &str, program: &Program) -> anyhow::Result<Overlay> {
    use borer::project::{Identity, ProjectFile};
    let pf = ProjectFile::load(path).map_err(anyhow::Error::msg)?;
    match pf.identify(program) {
        Identity::Same | Identity::PathOnly => {}
        Identity::Other | Identity::OtherPath => bail!(
            "the project {} was saved for another build ({}), not {}; nothing was loaded. borer://carry moves its names to a rebuild",
            short_path(path),
            short_path(&pf.program),
            short_path(&program.path.display().to_string())
        ),
    }
    let mut overlay = pf.to_overlay().map_err(anyhow::Error::msg)?;
    let left_out = borer::project::keep_placeable(&mut overlay, program);
    if !left_out.is_empty() {
        eprintln!(
            "borer: {} annotations of {} name no address of the binary and were skipped",
            left_out.len(),
            short_path(path)
        );
    }
    Ok(overlay)
}

impl Session {
    /// Fits the pack directories' packs to a program, saying on stderr
    /// which loaded.
    ///
    /// # Arguments
    ///
    /// * `program` - The loaded file.
    /// * `named` - The packs the command line and `BORER_PACKS` name.
    /// * `auto` - Whether the pack directories' packs may load by themselves.
    /// * `overlay` - The names, comments and types to apply.
    pub(super) fn fit(program: Program, named: &Packs, auto: bool, overlay: Overlay) -> Self {
        let (packs, notes) = borer::packs::for_program(&program, named, auto);
        for note in notes {
            eprintln!("borer: {note}");
        }
        Self {
            program: Arc::new(program),
            packs,
            overlay,
        }
    }

    /// Computes the analysis for a command that reads `feature` of the
    /// program's code.
    ///
    /// # Arguments
    ///
    /// * `feature` - The stage the command reads: [`Feature::Discover`] for
    ///   functions, blocks, references and calls, [`Feature::Decompile`]
    ///   for anything read from lifted code, [`Feature::Emulate`] for
    ///   anything that runs it.
    ///
    /// # Errors
    ///
    /// When the engine does not do `feature` with the architecture
    /// ([`Program::refuses`]).
    pub(super) fn analysis(&self, feature: Feature) -> anyhow::Result<Analysis> {
        if let Some(why) = self.program.refuses(feature) {
            bail!("{why}");
        }
        crate::term::busy(&format!("analyzing {}", file_name(&self.program.path)), &[]);
        Ok(Analysis::compute_with(
            &self.program,
            Arc::clone(&self.packs),
        ))
    }

    /// Computes the analysis, or returns an empty one when borer cannot
    /// discover the architecture's functions.
    ///
    /// For facts of the file rather than of its code: the symbol table and
    /// a crypto constant are parsed or scanned without disassembling
    /// anything, and read the analysis only to say which function they
    /// belong to. Refusing them on an architecture borer cannot disassemble
    /// threw away what it had already read out of the headers.
    pub(super) fn analysis_or_empty(&self) -> Analysis {
        self.analysis(Feature::Discover).unwrap_or_default()
    }

    /// Resolves an address or a name.
    ///
    /// # Arguments
    ///
    /// * `a` - The analysis.
    /// * `text` - `0x`-hex, decimal, or a function or symbol name.
    ///
    /// # Errors
    ///
    /// When the text is neither, naming the nearest names and the commands
    /// that list them ([`cli_hint`]).
    pub(super) fn resolve(&self, a: &Analysis, text: &str) -> anyhow::Result<u64> {
        resolve_suggesting(&self.program, a, &self.overlay, text)
            .map_err(|e| anyhow::Error::msg(cli_hint(&e)))
    }

    /// Resolves an address argument as the MCP tools do: `0x`-hex text
    /// at once, anything else as a name first (through the analysis when
    /// the architecture has one, else the symbols), then as a number.
    ///
    /// `disasm`, `hexdump` and `read` took numbers alone, where the tools
    /// of the same names take a function, an import or an export by name.
    ///
    /// # Arguments
    ///
    /// * `text` - The argument.
    ///
    /// # Errors
    ///
    /// When the text is neither an address nor a known name.
    pub(super) fn address(&self, text: &str) -> anyhow::Result<u64> {
        if borer_engine::analysis::hex_prefixed(text)
            && let Some(va) = parse_addr(text)
        {
            return Ok(va);
        }
        self.resolve(&self.analysis_or_empty(), text)
    }

    /// Computes the analysis and finds the function a positional argument
    /// names.
    ///
    /// # Arguments
    ///
    /// * `args` - The command line.
    /// * `i` - The argument's index.
    /// * `missing` - The error when the line is shorter.
    /// * `feature` - The stage the command reads ([`Session::analysis`]).
    ///
    /// # Returns
    ///
    /// The analysis and the function's entry.
    ///
    /// # Errors
    ///
    /// When the analysis cannot run, the argument is missing or does not
    /// resolve, or no discovered function contains it.
    pub(super) fn function_arg(
        &self,
        args: &[String],
        i: usize,
        missing: &'static str,
        feature: Feature,
    ) -> anyhow::Result<(Analysis, u64)> {
        let a = self.analysis(feature)?;
        let va = self.resolve(&a, arg(args, i, missing)?)?;
        let entry = entry_at(&self.program, &a, va)?;
        Ok((a, entry))
    }
}

/// Answers `decompile <binary> <address|name> [skeleton|full] [offset]
/// [limit]`: the function's pseudo-C, paged by line as the `decompile`
/// tool pages it ([`window`]).
///
/// The CLI printed every line, 6,610 of them for one function of a
/// system program, where the tool shows 300 under a `// showing N of M`
/// line saying how to read the rest.
///
/// # Arguments
///
/// * `args` - The command line, the command first and the binary second.
/// * `s` - The binary with its packs.
///
/// # Returns
///
/// The page of pseudo-C to print.
///
/// # Errors
///
/// For a bad detail, offset or limit, a function argument that is missing
/// or names no function, or a function that does not decompile.
pub(super) fn decompiled(args: &[String], s: &Session) -> anyhow::Result<String> {
    let (detail, offset, limit) = decompile_args(args.get(3..).unwrap_or_default())?;
    if limit == Some(0) {
        bail!("{}", crate::tools::decompile::LIMIT_ZERO);
    }
    let (a, entry) = s.function_arg(
        args,
        2,
        "decompile needs an address or name",
        Feature::Decompile,
    )?;
    let raw = std::env::var_os("BORER_RAW").is_some();
    let header = (!raw)
        .then(|| decompile::checked_header(&s.program, &a, &s.overlay, entry))
        .flatten();
    let text = if raw {
        decompile::decompile_raw(&s.program, &a, &s.overlay, entry)
    } else {
        decompile::decompile_named(&s.program, &a, &s.overlay, entry)
    }
    .with_context(|| format!("decompilation failed at {entry:#x}"))?;
    let warn = (!raw)
        .then(|| decompile::warnings(&s.program, &a, &s.overlay, entry, &text))
        .flatten();
    let header = match (header, warn) {
        (Some(h), Some(w)) => Some(format!("{h}\n{w}")),
        (h, w) => h.or(w),
    };
    let text = match detail {
        Detail::Skeleton => decompile::skeleton(&text),
        Detail::Full => text,
    };
    let text = decompile::with_header(&text, header.as_deref());
    Ok(window(&text, None, offset, limit))
}

/// Says an engine message's listing hint in the CLI's syntax.
///
/// The engine words it as the MCP tools take it
/// ([`borer_engine::analysis::LIST_HINT`]); at a shell the commands are
/// `borer functions` and `borer symbols`.
///
/// # Arguments
///
/// * `message` - The engine's message.
///
/// # Returns
///
/// The message with the hint replaced, or as it was when it has none.
pub(super) fn cli_hint(message: &str) -> String {
    message.replace(
        borer_engine::analysis::LIST_HINT,
        "; list them with `borer functions <binary> <filter>` or `borer symbols <binary> <filter>`",
    )
}
