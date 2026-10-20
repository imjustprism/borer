//! The server's state: what is loaded, its analysis and names, the locks
//! around them, and how a server starts or resumes.

use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex, MutexGuard, PoisonError, RwLock, RwLockReadGuard, RwLockWriteGuard};

use borer_engine::analysis::{Analysis, EnumSource, Overlay, parse_addr};
use borer_engine::pack::{Pack, Packs};
use borer_engine::program::{Feature, Program};
use rmcp::ErrorData;
use rmcp::handler::server::wrapper::Parameters;
use rmcp::model::InitializeRequestParams;

use crate::BorerServer;
use crate::errors::{err_internal, err_params};
use crate::handover::Resume;
use crate::params::{LoadBinaryParams, RawArch};
use crate::symsrv;

/// The raw layout `load_binary` was asked to map a file by (its `arch`,
/// `base`, `entry` and `regions`, as given); all `None` when the file's
/// own headers were read.
#[derive(Debug, Clone, Default, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub(crate) struct RawLoad {
    /// The architecture the bytes map as.
    pub(crate) arch: Option<RawArch>,
    /// Where the whole file maps.
    pub(crate) base: Option<String>,
    /// The entry address.
    pub(crate) entry: Option<String>,
    /// The parts of the file mapped instead of the whole.
    pub(crate) regions: Option<String>,
}

/// The refusal every tool answers before `load_binary`.
pub(crate) const NO_BINARY: &str = "no binary loaded; call load_binary first";

/// Reads under a lock, through a poisoning.
///
/// The value under every server lock is whole at any instant (each is
/// replaced, never edited in place), so a fault on another request leaves
/// it readable and the session alive.
///
/// # Arguments
///
/// * `lock` - The lock.
pub(crate) fn read_lock<T>(lock: &RwLock<T>) -> RwLockReadGuard<'_, T> {
    lock.read().unwrap_or_else(PoisonError::into_inner)
}

/// Writes under a lock, through a poisoning (see [`read_lock`]).
///
/// # Arguments
///
/// * `lock` - The lock.
pub(crate) fn write_lock<T>(lock: &RwLock<T>) -> RwLockWriteGuard<'_, T> {
    lock.write().unwrap_or_else(PoisonError::into_inner)
}

/// Takes a mutex, through a poisoning (see [`read_lock`]).
///
/// # Arguments
///
/// * `mutex` - The mutex.
pub(crate) fn lock<T>(mutex: &Mutex<T>) -> MutexGuard<'_, T> {
    mutex.lock().unwrap_or_else(PoisonError::into_inner)
}

/// The message a caught panic carries, for an answer that says a tool
/// faulted.
///
/// # Arguments
///
/// * `e` - The panic's payload, as `catch_unwind` hands it back.
///
/// # Returns
///
/// The payload's text, or `no message` when it is neither `&str` nor
/// `String`.
pub(crate) fn fault_text(e: &(dyn std::any::Any + Send)) -> String {
    e.downcast_ref::<&str>()
        .map(|s| (*s).to_owned())
        .or_else(|| e.downcast_ref::<String>().cloned())
        .unwrap_or_else(|| "no message".to_owned())
}

impl BorerServer {
    /// The packs an analysis of a program runs with: the pack directories'
    /// packs that fit it, then the named ones.
    ///
    /// # Arguments
    ///
    /// * `program` - The program.
    ///
    /// # Returns
    ///
    /// The packs, and a line for each pack that loaded by itself.
    pub(crate) fn packs_for(&self, program: &Program) -> (Arc<Packs>, Vec<String>) {
        borer::packs::for_program(program, &self.packs, borer::packs::auto_enabled())
    }

    /// Loads another build of the loaded program for the comparison surfaces.
    ///
    /// # Arguments
    ///
    /// * `other` - Path of the other build.
    ///
    /// # Errors
    ///
    /// When the file does not load, has no code analysis, or is not the
    /// architecture of the loaded program: a diff between a 32-bit build and a
    /// 64-bit one pairs functions that share nothing and reports it as a
    /// change.
    pub(crate) fn load_other(&self, other: &str) -> Result<Program, ErrorData> {
        let prog = Program::load_with_symsrv(
            &PathBuf::from(other),
            *read_lock(&self.pdb_applied),
            symsrv::cache_dir().as_deref(),
        )
        .map_err(|e| err_params(format!("load failed: {e:#}")))?;
        if !prog.arch.supports(Feature::Discover) {
            return Err(err_params(format!(
                "arch '{}' has no code analysis",
                prog.arch.name()
            )));
        }
        if let Some(p) = self.loaded()
            && p.arch != prog.arch
        {
            return Err(err_params(format!(
                "{other} is {} and the loaded binary is {}; a comparison across architectures would pair functions that share nothing",
                prog.arch.name(),
                p.arch.name()
            )));
        }
        Ok(prog)
    }

    /// The loaded program, `None` before `load_binary`.
    pub(crate) fn loaded(&self) -> Option<Arc<Program>> {
        read_lock(&self.program).clone()
    }

    /// The loaded program, for a tool that needs it outside a tool body.
    ///
    /// # Errors
    ///
    /// Invalid params when no binary is loaded.
    pub(crate) fn require_loaded(&self) -> Result<Arc<Program>, ErrorData> {
        self.loaded().ok_or_else(|| err_params(NO_BINARY))
    }

    /// The analysis, for a resource read outside a tool body that needs
    /// `feature` of the program's code.
    ///
    /// # Arguments
    ///
    /// * `feature` - The stage the resource reads ([`Program::refuses`]).
    ///
    /// # Errors
    ///
    /// Invalid params when no binary is loaded or the engine does not do
    /// `feature` with its architecture, as [`Self::with_analysis`] refuses
    /// both: the request came too early or asked the wrong file, and the
    /// server did not fail.
    pub(crate) fn analysis(&self, feature: Feature) -> Result<Arc<Analysis>, ErrorData> {
        if let Some(why) = self.require_loaded()?.refuses(feature) {
            return Err(err_params(why));
        }
        self.ensure_analysis().map_err(err_params)
    }

    /// Runs `f` against the loaded program.
    ///
    /// A fault in an analysis pass would unwind out of the handler and take
    /// the session with it: the call gets no reply at all, the agent cannot
    /// tell a crash from a hang, and everything learned so far in the
    /// session is gone with the process. Every tool body reaching a program
    /// comes through here, so one boundary turns a fault into an answer the
    /// caller can read and act on. The panic hook is left alone on purpose:
    /// unlike a damaged file, which is the job and expected, a fault here is
    /// a bug and worth a backtrace in the log.
    ///
    /// # Arguments
    ///
    /// * `f` - The tool body; its `Err` text becomes an invalid-params error,
    ///   since a body refuses only what it was asked (an address that names
    ///   nothing, a function that is not there) and does no I/O that could
    ///   fail on its own.
    ///
    /// # Errors
    ///
    /// Invalid params when no binary is loaded or `f` refuses the request;
    /// internal error only when `f` faults.
    pub(crate) fn with_program(
        &self,
        f: impl FnOnce(&Program) -> Result<String, String>,
    ) -> Result<String, ErrorData> {
        let guard = read_lock(&self.program);
        let Some(p) = guard.as_ref() else {
            return Err(err_params(NO_BINARY));
        };
        match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| f(p))) {
            Ok(answer) => answer.map_err(err_params),
            Err(e) => Err(err_internal(format!(
                "the analysis faulted on this binary: {}. The session is still up; another tool or another address may still answer.",
                fault_text(e.as_ref())
            ))),
        }
    }

    /// The derived analysis, or an empty one when the architecture has none.
    ///
    /// Some answers are facts of the file rather than of its code: the symbol
    /// table is parsed out of the headers, and a crypto constant is found by
    /// scanning bytes. Both read the analysis only to say more - which
    /// function a constant sits in, which import nothing calls - so refusing
    /// the whole answer on an architecture borer cannot disassemble threw
    /// away what it had already parsed. An arm64 image reported "locals: 2
    /// named functions" in its summary and then refused to list them.
    ///
    /// Tools that need the code itself keep using [`Self::ensure_analysis`],
    /// because an empty answer from those would read as "nothing found"
    /// rather than "not supported here". A tool body runs under
    /// [`Self::with_program`], so a binary is loaded and the architecture is
    /// the one way the analysis can be missing.
    pub(crate) fn analysis_or_empty(&self) -> Arc<Analysis> {
        self.ensure_analysis().unwrap_or_default()
    }

    /// Names the loaded file when its analysis has not been computed yet,
    /// so the next call that reads code will pay for all of it.
    ///
    /// # Returns
    ///
    /// The file's name, or `None` when nothing is loaded or the analysis
    /// is already held.
    pub(crate) fn analysis_pending(&self) -> Option<String> {
        if read_lock(&self.analysis).is_some() {
            return None;
        }
        self.loaded().map(|p| {
            p.path.file_name().map_or_else(
                || p.path.display().to_string(),
                |n| n.to_string_lossy().into_owned(),
            )
        })
    }

    /// Returns the derived analysis of the current program, computing and
    /// caching it on first use.
    ///
    /// # Errors
    ///
    /// When no binary is loaded or its architecture has no code analysis.
    pub(crate) fn ensure_analysis(&self) -> Result<Arc<Analysis>, String> {
        if let Some(a) = read_lock(&self.analysis).clone() {
            return Ok(a);
        }
        let program = self.loaded().ok_or(NO_BINARY)?;
        if let Some(why) = program.refuses(Feature::Discover) {
            return Err(why);
        }
        let packs = Arc::clone(&read_lock(&self.program_packs));
        let a = Arc::new(Analysis::compute_with(&program, packs));
        *write_lock(&self.analysis) = Some(a.clone());
        Ok(a)
    }

    /// Runs `f` against the loaded program, its analysis and a snapshot of
    /// the overlay: the prologue of every tool that reads code.
    ///
    /// A tool names the stage it reads, so a program whose instruction set
    /// has functions but no lifter yet answers the discovery tools and
    /// refuses the rest with the sentence [`Program::refuses`] gives,
    /// rather than an answer read as "nothing found".
    ///
    /// # Arguments
    ///
    /// * `feature` - The stage the tool reads: [`Feature::Discover`] for
    ///   functions, blocks, references and calls, [`Feature::Decompile`]
    ///   for anything read from lifted code, [`Feature::Emulate`] for
    ///   anything that runs it.
    /// * `f` - The tool body; its `Err` text becomes an internal error.
    ///
    /// # Errors
    ///
    /// Invalid params when no binary is loaded; internal error when the
    /// engine does not do `feature` with the architecture or `f` fails or
    /// faults.
    pub(crate) fn with_analysis(
        &self,
        feature: Feature,
        f: impl FnOnce(&Program, &Analysis, &Overlay) -> Result<String, String>,
    ) -> Result<String, ErrorData> {
        self.with_program(|p| {
            if let Some(why) = p.refuses(feature) {
                return Err(why);
            }
            let a = self.ensure_analysis()?;
            f(p, &a, &self.overlay())
        })
    }

    /// Returns a snapshot of the annotation overlay, rendering constants by
    /// the binary's name tables.
    ///
    /// Every tool takes the same snapshot, so an answer never depends on
    /// which calls came before it. A decompilation reads only the tables of
    /// the functions it calls, each computed once ([`EnumSource::Binary`]),
    /// so no call waits for the binary's every table.
    pub(crate) fn overlay(&self) -> Overlay {
        Overlay {
            enum_source: EnumSource::Binary,
            ..self.overlay_plain()
        }
    }

    /// Returns the annotation overlay as the user left it, without the
    /// binary's name tables.
    pub(crate) fn overlay_plain(&self) -> Overlay {
        read_lock(&self.overlay).clone()
    }

    /// Carries what the analysis read under `before` over to the names now
    /// in force, after a rename, a comment, a type or a loaded project
    /// changed them, and lets go of the rest
    /// ([`borer_engine::analysis::Derived::moved`]): a result that read none
    /// of the facts the edit changed is kept, so a rename rebuilds only the
    /// texts that read the name, and nothing read under the old names stays
    /// in memory for good.
    ///
    /// # Arguments
    ///
    /// * `before` - The overlay as it was before the edit
    ///   ([`BorerServer::overlay_plain`]).
    pub(crate) fn names_changed(&self, before: &Overlay) {
        if let Some(a) = read_lock(&self.analysis).as_ref() {
            a.derived.moved(a, before, &self.overlay_plain());
        }
    }

    /// Resolves an address argument: `0x`-hex text, else a name looked up
    /// through the analysis, symbols and overlay (agents name things), else
    /// decimal or bare-hex text ([`resolve`]).
    ///
    /// A name comes before the number reading, so a function named `cafe`
    /// or `1234` is reachable by its name; only `0x` text skips the lookup.
    /// A program with no code analysis looks names up in its symbols and
    /// the overlay alone.
    ///
    /// # Arguments
    ///
    /// * `p` - The loaded program.
    /// * `text` - The argument as the agent passed it.
    ///
    /// # Errors
    ///
    /// When the text is neither an address nor a known name, naming the
    /// names nearest it ([`borer_engine::analysis::resolve_suggesting`]).
    pub(crate) fn addr(&self, p: &Program, text: &str) -> Result<u64, String> {
        if borer_engine::analysis::hex_prefixed(text)
            && let Some(va) = parse_addr(text)
        {
            return Ok(va);
        }
        borer_engine::analysis::resolve_suggesting(
            p,
            &self.analysis_or_empty(),
            &self.overlay(),
            text,
        )
    }

    /// Resolves an argument to the entry of the discovered function containing it.
    ///
    /// # Arguments
    ///
    /// * `p` - The loaded program.
    /// * `a` - Its analysis.
    /// * `text` - Address or name (see [`Self::addr`]).
    ///
    /// # Errors
    ///
    /// When the text does not resolve or no function contains the address
    /// ([`borer_engine::analysis::function_entry`] says an import's slot is
    /// one).
    pub(crate) fn function_entry(
        &self,
        p: &Program,
        a: &Analysis,
        text: &str,
    ) -> Result<u64, String> {
        let va = self.addr(p, text)?;
        borer_engine::analysis::function_entry(p, a, va).map_err(|e| {
            let digits = text.trim();
            let hint = u64::from_str_radix(digits, 16)
                .ok()
                .filter(|hex| {
                    digits.bytes().all(|b| b.is_ascii_digit()) && a.function_at(*hex).is_some()
                })
                .map_or_else(String::new, |hex| {
                    format!("; bare digits are decimal, write {hex:#x} for the hex address")
                });
            format!("{e}{hint}")
        })
    }

    /// A server with nothing loaded, the packs `BORER_PACKS` names, and
    /// live attaching opened to any process when `BORER_LIVE_ANY` is `1`.
    pub(crate) fn new() -> BorerServer {
        BorerServer {
            live_any: std::env::var_os(crate::tools::live::LIVE_ANY_ENV).is_some_and(|v| v == "1"),
            packs: read_packs(&env_pack_files()).unwrap_or_else(|e| {
                eprintln!("borer: {e:#}; running without packs");
                Arc::default()
            }),
            ..BorerServer::default()
        }
    }

    /// Loads the file the worker before this one had loaded, the way it was
    /// loaded (its `pdb`, `entry_file_offset` and raw layout), with its
    /// names and comments.
    ///
    /// A file that no longer loads is said on stderr and the session goes on
    /// without it.
    ///
    /// # Arguments
    ///
    /// * `resume` - The state that worker wrote.
    ///
    /// # Returns
    ///
    /// What the client sent at initialize, for this worker to serve the
    /// session with; `None` when the state does not hold it.
    pub(crate) fn resume(
        &self,
        Resume {
            peer_info,
            project,
            pdb,
            entry_file_offset,
            raw,
        }: Resume,
    ) -> Option<InitializeRequestParams> {
        if let Some(project) = project {
            let overlay = project.to_overlay();
            let reloaded = self.load_binary(Parameters(LoadBinaryParams {
                path: project.program,
                entry_file_offset,
                pdb,
                arch: raw.arch,
                base: raw.base,
                entry: raw.entry,
                regions: raw.regions,
            }));
            if let Err(e) = reloaded {
                eprintln!(
                    "borer: reloading the file after the hand-over: {}",
                    e.message
                );
            } else if let Err(e) = overlay {
                eprintln!("borer: the handed-over project's types: {e}");
            } else if let Ok(o) = overlay {
                *write_lock(&self.overlay) = o;
            }
        }
        peer_info
    }
}

/// The pack files `BORER_PACKS` lists, in order ([`borer::packs::env_paths`]).
pub(crate) fn env_pack_files() -> Vec<String> {
    borer::packs::env_paths("BORER_PACKS")
        .unwrap_or_default()
        .iter()
        .map(|p| p.to_string_lossy().into_owned())
        .collect()
}

/// Reads pack files into the packs an analysis runs with, printing each
/// pack's warnings to stderr.
///
/// # Arguments
///
/// * `files` - The pack files, in load order.
///
/// # Errors
///
/// When a file cannot be read or is not a pack.
pub(crate) fn read_packs(files: &[String]) -> anyhow::Result<Arc<Packs>> {
    let mut packs = Vec::with_capacity(files.len());
    for file in files {
        let shown = borer_engine::text::short_path(file);
        let text = std::fs::read_to_string(file)
            .map_err(|e| anyhow::anyhow!("reading pack {shown}: {e}"))?;
        let (mut pack, warnings) = Pack::parse(&text, &shown).map_err(anyhow::Error::msg)?;
        for w in warnings {
            eprintln!("borer: {w}");
        }
        borer::packs::load_scripts(&mut pack, Path::new(file)).map_err(anyhow::Error::msg)?;
        packs.push(pack);
    }
    Ok(Arc::new(Packs { packs }))
}

#[cfg(test)]
mod tests {
    /// The loaded file is named as pending until its analysis is held,
    /// and nothing is pending with no file loaded.
    ///
    /// # Panics
    ///
    /// When the pending state reads otherwise.
    #[test]
    fn a_first_analysis_is_pending_until_computed() {
        assert_eq!(crate::BorerServer::default().analysis_pending(), None);
        let server = crate::testing::raw_server();
        assert!(server.analysis_pending().is_some());
        server.ensure_analysis().expect("analyzes");
        assert_eq!(server.analysis_pending(), None);
    }

    /// A fresh session renders constants by the binary's name tables, as a
    /// session that has already decompiled does: no answer depends on the
    /// calls before it.
    ///
    /// # Panics
    ///
    /// When the snapshot reads no tables.
    #[test]
    fn every_overlay_snapshot_reads_the_binarys_tables() {
        let server = crate::BorerServer::default();
        assert_eq!(
            server.overlay().enum_source,
            borer_engine::analysis::EnumSource::Binary,
            "a fresh session renders constants as one that has decompiled"
        );
    }
}
