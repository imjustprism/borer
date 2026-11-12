//! The binary a command opens: its program, analysis and names, read once
//! per command.

use std::cell::RefCell;
use std::sync::Arc;

use anyhow::{Context as _, bail};
use borer_engine::analysis::{
    Analysis, Overlay, decompile, parse_addr, render, resolve_suggesting, stated,
};
use borer_engine::clr::managed;
use borer_engine::layout::Layout;
use borer_engine::pack::Packs;
use borer_engine::program::{Feature, Program};
use borer_engine::text::short_path;

use super::USAGE;
use super::args::{arg, command_usage, decompile_args, entry_at};
use crate::params::Detail;
use crate::state::read_packs;
use crate::tools::decompile::window;
use crate::tools::load::skipped_classes;

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
pub(super) fn open(args: &[String], load: &Loading) -> anyhow::Result<(Arc<Packs>, Program)> {
    let (apply_pdb, layout) = (load.pdb, load.layout.as_ref());
    let named = read_packs(&load.pack_files)?;
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
/// cannot be read, or is not a regular file
/// ([`borer_engine::program::open_regular`]), so a pipe or a device is
/// never opened for it.
///
/// # Arguments
///
/// * `file` - The binary.
fn head_bytes(file: &std::path::Path) -> Vec<u8> {
    use std::io::Read as _;
    let mut head = Vec::with_capacity(256);
    if let Ok(f) = borer_engine::program::open_regular(file, u64::MAX) {
        let _ = f.take(256).read_to_end(&mut head);
    }
    head
}

/// How the command line loaded the binary, so a command that loads a
/// second one (`diff`) loads it the same way.
#[derive(Debug, Clone, Default)]
pub(super) struct Loading {
    /// The `--pack` files.
    pub(super) pack_files: Vec<String>,
    /// Whether the companion PDB is applied (`--no-pdb` turns it off).
    pub(super) pdb: bool,
    /// The raw layout `--arch` and its flags give, for a headerless file.
    pub(super) layout: Option<Layout>,
    /// Whether the pack directories' packs load by themselves.
    pub(super) auto: bool,
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
    /// How the binary was loaded.
    pub(super) loading: Loading,
    /// The analysis the project's class fields were held to the code with
    /// ([`Session::checked`]), until a command asks for one.
    pub(super) ready: RefCell<Option<Analysis>>,
}

/// Converts `pf` into an overlay and checks that its structs lay out at
/// `program`'s pointer width.
///
/// # Arguments
///
/// * `pf` - The loaded project file.
/// * `program` - The loaded binary whose pointer width governs layouts.
///
/// # Errors
///
/// When `pf` states more than an overlay holds or lays out a struct
/// inconsistently at `program`'s pointer width.
fn overlay_at_width(
    pf: &borer::project::ProjectFile,
    program: &Program,
) -> anyhow::Result<Overlay> {
    let overlay = pf.to_overlay().map_err(anyhow::Error::msg)?;
    let word: u64 = if program.is_64 { 8 } else { 4 };
    borer_engine::analysis::utypes::laid_at(&overlay.types, word).map_err(|e| {
        anyhow::anyhow!(
            "{e} with the {word}-byte pointers of {}; nothing was loaded",
            short_path(&program.path.display().to_string())
        )
    })?;
    Ok(overlay)
}

/// Reads a project file and checks that its structs lay out at `program`'s
/// pointer width.
///
/// # Arguments
///
/// * `path` - The project file.
/// * `program` - The loaded binary whose pointer width governs layouts.
///
/// # Errors
///
/// When the file cannot be read or parsed, states more than an overlay
/// holds, or lays out a struct inconsistently at `program`'s pointer width.
pub(super) fn load_for_program(
    path: &str,
    program: &Program,
) -> anyhow::Result<(borer::project::ProjectFile, Overlay)> {
    let pf = borer::project::ProjectFile::load(path).map_err(anyhow::Error::msg)?;
    let overlay = overlay_at_width(&pf, program)?;
    Ok((pf, overlay))
}

/// Reads a project file into the overlay a query applies.
///
/// As the `load_project` tool does, a project saved for another build is
/// refused, and so is one with no hash whose path is another path as text
/// ([`borer::project::ProjectFile::is_for`]); the annotations no section of
/// the binary can hold, and the names and comments the tools would not set,
/// are left out and counted on stderr.
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
/// cannot hold or a struct that does not lay out with the binary's
/// pointers, or was saved for another binary.
pub(super) fn project_overlay(path: &str, program: &Program) -> anyhow::Result<Overlay> {
    use borer::project::{Identity, ProjectFile};
    let pf = ProjectFile::load(path).map_err(anyhow::Error::msg)?;
    let (saved, loaded) = (
        short_path(&pf.program),
        short_path(&program.path.display().to_string()),
    );
    match pf.identify(program) {
        Identity::Same | Identity::PathOnly => {}
        Identity::Other => bail!(
            "the project {} was saved for another build ({saved}), not {loaded}; nothing was loaded. borer://carry moves its names to a rebuild",
            short_path(path)
        ),
        Identity::OtherPath => bail!(
            "the project {} records no sha-256, so its path names its binary, and {saved} is not {loaded} as text; nothing was loaded. Give that binary, or load the project with load_project force=true and save_project to record the hash",
            short_path(path)
        ),
    }
    let mut overlay = overlay_at_width(&pf, program)?;
    let placed = borer::project::keep_placeable(&mut overlay, program).len();
    let skipped = placed.saturating_add(crate::params::keep_settable(
        &mut overlay,
        0,
        &mut Vec::new(),
    ));
    if skipped > 0 {
        eprintln!(
            "borer: {skipped} annotations of {} name no address of the binary or are no name or comment the tools set, and were skipped",
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
    /// * `overlay` - The names, comments and types to apply.
    /// * `loading` - How it was loaded: whether the pack directories' packs
    ///   may load by themselves, and what a second file loads with.
    pub(super) fn fit(program: Program, named: &Packs, overlay: Overlay, loading: Loading) -> Self {
        let (packs, notes) = borer::packs::for_program(&program, named, loading.auto);
        for note in notes {
            eprintln!("borer: {note}");
        }
        Self {
            program: Arc::new(program),
            packs,
            overlay,
            loading,
            ready: RefCell::new(None),
        }
    }

    /// Fits a session ([`Session::fit`]) whose project's class fields are
    /// held to the binary's code, as the `load_project` tool holds them
    /// ([`stated::settled`]): what a query runs against.
    ///
    /// The fields of a class the code contradicts, or that no function
    /// belongs to, are left out and said on stderr as the tool's answer
    /// says them ([`skipped_classes`]). A project that states none costs
    /// nothing, and the analysis the check reads is kept for the command's
    /// first use of one, so no command analyzes the binary twice for its
    /// project.
    ///
    /// # Arguments
    ///
    /// As [`Session::fit`].
    ///
    /// # Errors
    ///
    /// When the check is cut short, which only a caller's deadline does.
    pub(super) fn checked(
        program: Program,
        named: &Packs,
        overlay: Overlay,
        loading: Loading,
    ) -> anyhow::Result<Self> {
        let mut s = Self::fit(program, named, overlay, loading);
        if s.overlay.fields.is_empty() {
            return Ok(s);
        }
        let a = s.analysis_or_empty();
        let unsettled = stated::settled(&s.program, &a, &s.overlay).map_err(anyhow::Error::msg)?;
        let gone = unsettled.leave_out(&mut s.overlay);
        for line in skipped_classes(&unsettled, gone).lines() {
            eprintln!("borer: {}", line.trim_start_matches("# "));
        }
        s.ready = RefCell::new(Some(a));
        Ok(s)
    }

    /// Computes the analysis for a command that reads `feature` of the
    /// program's code, or hands over the one the project was held to the
    /// code with ([`Session::checked`]).
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
        if let Some(ready) = self.ready.take() {
            return Ok(ready);
        }
        crate::term::busy(&format!("analyzing {}", file_name(&self.program.path)), &[]);
        Ok(Analysis::compute_with(
            &self.program,
            Arc::clone(&self.packs),
        ))
    }

    /// Says why the engine cannot discover the program's functions, for a
    /// command that read managed code through an empty analysis
    /// ([`Self::analysis_or_empty`]) and found none to answer from.
    ///
    /// # Errors
    ///
    /// When the engine does not disassemble the architecture.
    fn discovers(&self) -> anyhow::Result<()> {
        match self.program.refuses(Feature::Discover) {
            Some(why) => bail!("{why}"),
            None => Ok(()),
        }
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

    /// Answers `function <binary> <address|name>`: a function's facts and
    /// blocks, or a .NET method's body, callers and callees
    /// ([`managed::detail`]).
    ///
    /// # Arguments
    ///
    /// * `args` - The command line, the command first and the binary second.
    ///
    /// # Errors
    ///
    /// When the argument is missing, does not resolve, or names no function.
    pub(super) fn function_text(&self, args: &[String]) -> anyhow::Result<String> {
        self.function_answer(
            arg(args, 2, "function needs an address or name")?,
            |a, token| managed::detail(&self.program, a, token, 0),
            |a, entry| render::function_detail(a, &self.overlay, entry, 0),
        )
    }

    /// Answers a command about one function: a .NET method with an IL
    /// body by `il`, any other function by `native`.
    ///
    /// # Arguments
    ///
    /// * `text` - The function, by address or name.
    /// * `il` - Answers for the method's `MethodDef` token.
    /// * `native` - Answers for a discovered function's entry; `None`
    ///   when no function is there.
    ///
    /// # Errors
    ///
    /// When the text does not resolve or names no function, borer does
    /// not discover the architecture's functions, or `il` refuses.
    fn function_answer(
        &self,
        text: &str,
        il: impl FnOnce(&Analysis, u32) -> Result<String, String>,
        native: impl FnOnce(&Analysis, u64) -> Option<String>,
    ) -> anyhow::Result<String> {
        let a = self.analysis_or_empty();
        let va = self.resolve(&a, text).ok();
        if let Some(token) = managed::il_method_named(&self.program, text, va) {
            return il(&a, token).map_err(anyhow::Error::msg);
        }
        self.discovers()?;
        let entry = entry_at(&self.program, &a, self.resolve(&a, text)?)?;
        native(&a, entry).context("no function at address")
    }

    /// Answers `fstrings <binary> <address|name>`: the string literals a
    /// function references, or the user strings a .NET method loads
    /// ([`managed::strings_tsv`]).
    ///
    /// # Arguments
    ///
    /// * `args` - The command line, the command first and the binary second.
    ///
    /// # Errors
    ///
    /// When the argument is missing, does not resolve, or names no function.
    pub(super) fn fstrings_text(&self, args: &[String]) -> anyhow::Result<String> {
        self.function_answer(
            arg(args, 2, "fstrings needs an address or name")?,
            |a, token| managed::strings_tsv(&self.program, a, token),
            |a, entry| render::function_strings_tsv(&self.program, a, &self.overlay, entry),
        )
    }

    /// Answers `disasmfn <binary> <address|name>`: a function by blocks,
    /// or a .NET method's CIL ([`managed::listing`]).
    ///
    /// # Arguments
    ///
    /// * `args` - The command line, the command first and the binary second.
    ///
    /// # Errors
    ///
    /// When the argument is missing, does not resolve, or names no function.
    pub(super) fn disasmfn_text(&self, args: &[String]) -> anyhow::Result<String> {
        self.function_answer(
            arg(args, 2, "disasmfn needs an address or name")?,
            |_, token| managed::listing(&self.program, token, 400),
            |a, entry| render::disasm_function(&self.program, a, &self.overlay, entry, 400, false),
        )
    }

    /// Answers `xrefs <binary> <address|name>`: the references to an
    /// address, or the IL methods naming a .NET member
    /// ([`managed::xrefs_tsv`]).
    ///
    /// # Arguments
    ///
    /// * `args` - The command line, the command first and the binary second.
    ///
    /// # Errors
    ///
    /// When the argument is missing or names neither an address nor a
    /// .NET member.
    pub(super) fn xrefs_text(&self, args: &[String]) -> anyhow::Result<String> {
        let text = arg(args, 2, "xrefs needs an address")?;
        let a = self.analysis_or_empty();
        let va = self.resolve(&a, text).ok();
        if let Some(targets) = managed::named(&self.program, text, va) {
            return managed::xrefs_tsv(
                &self.program,
                &a,
                &targets,
                0,
                render::XREF_ROWS_DEFAULT,
                false,
            )
            .map_err(anyhow::Error::msg);
        }
        self.discovers()?;
        let va = self.resolve(&a, text)?;
        Ok(render::xrefs_tsv(
            &self.program,
            &a,
            &self.overlay,
            va,
            0,
            render::XREF_ROWS_DEFAULT,
            false,
        ))
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
/// [limit]`: the function's pseudo-C as the `decompile` tool answers it
/// ([`decompile::answer()`]).
///
/// The binary's name tables are not read here, where the tool reads them,
/// so a constant one of them spells for the tool stays a number here.
///
/// It is paged by line as the tool pages it ([`window`]). The CLI printed
/// every line, 6,610 of them for one function of a system program, where
/// the tool shows 300 under a `// showing N of M` line saying how to read
/// the rest. It also wrote a header of its own, the check and the warning
/// without the `// next:` lines, so a line number `grep` gave named another
/// line here. `grep` counts the index's lines ([`decompile::shown`]), which
/// are these only where nothing the index leaves out shows: a comment, name
/// or type the project gave, or the repair search's note and rendering.
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
/// or names no function, or a function that does not decompile. An address
/// inside a function's span but in none of its blocks is recovered when
/// that walk is clean. Otherwise the function whose span holds it is
/// decompiled.
pub(super) fn decompiled(args: &[String], s: &Session) -> anyhow::Result<String> {
    let (detail, offset, limit) = decompile_args(args.get(3..).unwrap_or_default())?;
    if limit == Some(0) {
        bail!("{}", crate::tools::decompile::LIMIT_ZERO);
    }
    let mut a = s.analysis(Feature::Decompile)?;
    let va = s.resolve(&a, arg(args, 2, "decompile needs an address or name")?)?;
    let entry =
        borer_engine::analysis::entry_or_gap(&s.program, &mut a, va).map_err(anyhow::Error::msg)?;
    let text = if std::env::var_os("BORER_RAW").is_some() {
        decompile::decompile_raw(&s.program, &a, &s.overlay, entry).map(|text| match detail {
            Detail::Skeleton => decompile::skeleton(&text),
            Detail::Full => text,
        })
    } else {
        decompile::answer(&s.program, &a, &s.overlay, entry, detail.into())
    }
    .with_context(|| format!("decompilation failed at {entry:#x}"))?;
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

#[cfg(test)]
mod tests {
    use borer_engine::analysis::Overlay;
    use borer_engine::analysis::stated::Field;
    use borer_engine::pack::Packs;
    use borer_engine::program::{Arch, Feature, Program, Section};

    use super::{Loading, Session};

    /// A session over one `ret`, with a project stating `fields` fields of
    /// a class no function belongs to.
    ///
    /// # Arguments
    ///
    /// * `fields` - How many fields the project states.
    ///
    /// # Panics
    ///
    /// When the check is cut short.
    fn checked(fields: u64) -> Session {
        let text = Section::mapped(".text", 0x1000, 0, 1, false, true);
        let code = vec![0xc3]; // ASM: ret
        let program = Program::raw(code, Arch::X86_64, 0, Some(0x1000), vec![text]);
        let mut overlay = Overlay::default();
        for off in 0..fields {
            let field = Field {
                name: format!("m_{off}"),
                ty: None,
            };
            let stated = overlay.fields.entry("Ghost".to_owned()).or_default();
            stated.insert(off, field);
        }
        Session::checked(program, &Packs::default(), overlay, Loading::default())
            .expect("no deadline cuts a command's check short")
    }

    /// The analysis a project was held to the code with goes to the
    /// command's first use of one.
    ///
    /// No command analyzes the binary twice for its project, a project
    /// that states no field has no analysis computed for it, and the
    /// fields of a class no function belongs to are left out.
    ///
    /// # Panics
    ///
    /// When the analysis is not kept, is handed out twice, or is computed
    /// for a project that states no field, or the fields stay.
    #[test]
    fn the_analysis_a_project_was_checked_with_goes_to_the_command() {
        assert!(checked(0).ready.borrow().is_none());
        let s = checked(2);
        assert!(s.ready.borrow().is_some() && s.overlay.fields.is_empty());
        let first = s.analysis(Feature::Discover).expect("x86-64 is analyzed");
        assert!(first.function(0x1000).is_some() && s.ready.borrow().is_none());
    }

    /// A project with no hash saved for another path is refused as another
    /// path as text, not as another build, which it need not be.
    ///
    /// # Panics
    ///
    /// When the project loads or the refusal says another build.
    #[test]
    fn a_hashless_project_for_another_path_says_so() {
        let dir = std::env::temp_dir().join(format!("borer-cli-path-{}", std::process::id()));
        std::fs::create_dir_all(&dir).expect("a temp dir");
        let path = dir.join("old.json").display().to_string();
        borer::project::ProjectFile::from_overlay("elsewhere.exe", None, &Overlay::default())
            .save(&path, borer::output::Existing::Replace)
            .expect("the project is saved");
        let refused = super::project_overlay(&path, &checked(0).program);
        std::fs::remove_dir_all(&dir).expect("cleans up");
        let refused = refused.expect_err("another path").to_string();
        assert!(
            refused.contains("as text") && !refused.contains("another build"),
            "{refused}"
        );
    }

    /// The loading line's first bytes never open a pipe, which blocks until
    /// a writer comes: only a regular file is read for them.
    ///
    /// # Panics
    ///
    /// When the pipe is read.
    #[cfg(unix)]
    #[test]
    fn the_head_bytes_never_open_a_pipe() {
        let dir = std::env::temp_dir().join(format!("borer-head-{}", std::process::id()));
        std::fs::create_dir_all(&dir).expect("a temp dir");
        let fifo = dir.join("pipe");
        let made = std::process::Command::new("mkfifo")
            .arg(&fifo)
            .status()
            .is_ok_and(|s| s.success());
        let head = made.then(|| super::head_bytes(&fifo));
        std::fs::remove_dir_all(&dir).expect("cleans up");
        assert!(head.is_none_or(|h| h.is_empty()), "the pipe was read");
    }
}
