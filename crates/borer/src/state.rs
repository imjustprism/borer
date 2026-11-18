//! The server's state: what is loaded, its analysis and names, the locks
//! around them, and how a server starts or resumes.

use std::path::Path;
use std::sync::{Arc, Mutex, MutexGuard, PoisonError, RwLock, RwLockReadGuard, RwLockWriteGuard};

use borer_engine::analysis::edit::{self, Edit, Force, Plan};
use borer_engine::analysis::{Analysis, Overlay};
use borer_engine::answer::Need;
use borer_engine::pack::{Pack, Packs};
use borer_engine::program::{Feature, Program};
use borer_front::tools::{Apply, Cause, Failure, Held, Snapshot, View};
use rmcp::ErrorData;
use rmcp::handler::server::wrapper::Parameters;
use rmcp::model::InitializeRequestParams;

use crate::BorerServer;
use crate::errors::{err_params, failed};
use crate::handover::Resume;
use crate::params::{LoadBinaryParams, RawArch};

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

pub(crate) use borer_front::tools::{NO_BINARY, fault_text};

pub(crate) use borer_front::tools::tabled;

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

/// An empty analysis with the program it was made for ([`crate::BorerServer::analysis_or_empty`]).
pub(crate) type EmptyAnalysis = (Arc<Program>, Arc<Analysis>);

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

/// Runs `f` behind the fault boundary of a tool body
/// ([`borer_front::tools::guarded`]).
///
/// # Arguments
///
/// * `f` - The work; its `Err` text becomes an invalid-params error.
///
/// # Errors
///
/// Invalid params when `f` refuses; internal error only when `f` faults.
pub(crate) fn guarded<T>(f: impl FnOnce() -> Result<T, String>) -> Result<T, ErrorData> {
    borer_front::tools::guarded(f).map_err(failed)
}

/// Says that `program`, read outside its lock, was put out of place by a
/// load since, so nothing found of it applies.
///
/// # Arguments
///
/// * `program` - The program read.
pub(crate) fn replaced(program: &Program) -> String {
    format!(
        "{} is no longer the loaded binary (a load_binary ran meanwhile); nothing was applied",
        program.path.display()
    )
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
        let prog = crate::tools::load::load_program(
            Path::new(other),
            *read_lock(&self.pdb_applied),
            None,
            crate::tools::load::configured_max_file(),
        )
        .map(|(program, _)| program)
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

    /// Returns the derived analysis of the current program, computing and
    /// caching it on first use.
    ///
    /// A caller outside a tool body holds no lock on the program while the
    /// analysis is computed, so a `load_binary` may finish meanwhile: the
    /// analysis is kept only when the program it was computed for is still
    /// the one loaded, checked under the program's lock, which
    /// `load_binary` takes to replace the program and drop its analysis.
    /// When another request stored an analysis of the same program first,
    /// that one is kept and returned, so a function it recovered
    /// ([`Held::decompile_entry`]) is not dropped. The analysis is computed
    /// under a cancel flag of its own that nothing raises: it is kept for
    /// every later request, so the deadline of the request that happened
    /// to compute it must not cut it short.
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
        let a = Arc::new(
            borer_engine::cancel::Cancel::new().within(|| Analysis::compute_with(&program, packs)),
        );
        let loaded = read_lock(&self.program);
        if loaded
            .as_ref()
            .is_some_and(|now| Arc::ptr_eq(now, &program))
        {
            let mut slot = write_lock(&self.analysis);
            if let Some(kept) = slot.as_ref() {
                return Ok(Arc::clone(kept));
            }
            *slot = Some(a.clone());
        }
        Ok(a)
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
    /// the one way the analysis can be missing. The empty analysis is held
    /// until the next load, so what its memo keeps (the string walk) is
    /// worked out once per program, as an analysis's is.
    pub(crate) fn analysis_or_empty(&self) -> Arc<Analysis> {
        self.ensure_analysis()
            .unwrap_or_else(|_| self.empty_analysis())
    }

    /// Returns a snapshot of the annotation overlay, rendering constants by
    /// the binary's name tables.
    ///
    /// Every tool takes the same snapshot, so an answer never depends on
    /// which calls came before it. A decompilation reads only the tables of
    /// the functions it calls, each computed once ([`borer_engine::analysis::EnumSource::Binary`]),
    /// so no call waits for the binary's every table.
    pub(crate) fn overlay(&self) -> Overlay {
        tabled(&read_lock(&self.overlay))
    }

    /// The loaded program, for a tool that needs it outside a tool body.
    ///
    /// # Errors
    ///
    /// Invalid params when no binary is loaded.
    pub(crate) fn require_loaded(&self) -> Result<Arc<Program>, ErrorData> {
        self.loaded().ok_or_else(|| err_params(NO_BINARY))
    }

    /// Runs `f` against the loaded program under its read lock, behind the
    /// fault boundary ([`guarded`]), for the tools the server keeps.
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
        guarded(|| f(p))
    }

    /// Returns what a script runs over: the loaded program and its
    /// analysis (empty when the architecture has none), taken together
    /// under the program's lock, then the overlay.
    ///
    /// A script runs outside any lock, so a program and an analysis taken
    /// on their own could meet a `load_binary` in between, and the script
    /// would read one program through another's analysis. The overlay is
    /// taken after the lock is let go, as every tool takes it: a script
    /// waiting on an edit's hold of the overlay must not keep a load
    /// waiting behind it, and a name it proposes for a program loaded over
    /// is refused when it is applied ([`Self::commit`]).
    ///
    /// # Errors
    ///
    /// Invalid params when no binary is loaded or borer does not
    /// disassemble its architecture.
    pub(crate) fn script_snapshot(
        &self,
    ) -> Result<(Arc<Program>, Arc<Analysis>, Overlay), ErrorData> {
        let guard = read_lock(&self.program);
        let program = guard
            .as_ref()
            .map(Arc::clone)
            .ok_or_else(|| err_params(NO_BINARY))?;
        if let Some(why) = program.refuses(Feature::Disasm) {
            return Err(err_params(why));
        }
        let analysis = self.analysis_or_empty();
        drop(guard);
        Ok((program, analysis, self.overlay()))
    }

    /// Returns the empty analysis held for the loaded program, making it on
    /// first use.
    ///
    /// The held one is served only to the program it was made for, the way
    /// [`Self::ensure_analysis`] keeps an analysis only for the program still
    /// loaded: a caller outside a tool body may ask after a `load_binary`
    /// replaced its program, and the new program must not answer from the
    /// old one's memo.
    pub(crate) fn empty_analysis(&self) -> Arc<Analysis> {
        let Some(program) = self.loaded() else {
            return Arc::default();
        };
        let mut slot = write_lock(&self.no_code);
        if let Some((of, held)) = slot.as_ref()
            && Arc::ptr_eq(of, &program)
        {
            return Arc::clone(held);
        }
        let made = Arc::<Analysis>::default();
        *slot = Some((program, Arc::clone(&made)));
        made
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

    /// Puts `program` in place of the loaded one, with the way it was
    /// loaded, and lets go of what belonged to the old one: its names and
    /// comments and its analysis, with the string walks its memo holds.
    ///
    /// All of it changes under the program's write lock, so no tool body
    /// (which holds the read lock for its whole run, [`Self::with_program`])
    /// sees the new program with the old one's names or analysis, or writes
    /// a name it checked against the old program into the new one's
    /// overlay. The lock is tried, never queued for: a body takes the read
    /// lock again inside (the analysis it asks for, an address it
    /// resolves), and a writer queued for the lock makes that second read
    /// wait behind it while the writer waits for the body, so neither would
    /// end. While a body holds it, the writer waits a moment and tries
    /// again.
    ///
    /// # Arguments
    ///
    /// * `program` - The program loaded.
    /// * `packs` - The packs its analysis runs with.
    /// * `(pdb, entry_file_offset, raw)` - How it was loaded, for a reload.
    ///
    /// # Returns
    ///
    /// The program it replaced, and that program's overlay.
    pub(crate) fn install(
        &self,
        program: Arc<Program>,
        packs: Arc<Packs>,
        (pdb, entry_file_offset, raw): (bool, Option<u64>, RawLoad),
    ) -> (Option<Arc<Program>>, Overlay) {
        /// How long the writer waits before trying the lock again.
        const RETRY: std::time::Duration = std::time::Duration::from_millis(1);
        let mut loaded = loop {
            match self.program.try_write() {
                Ok(guard) => break guard,
                Err(std::sync::TryLockError::Poisoned(e)) => break e.into_inner(),
                Err(std::sync::TryLockError::WouldBlock) => std::thread::sleep(RETRY),
            }
        };
        let dropped = std::mem::take(&mut *write_lock(&self.overlay));
        *write_lock(&self.pdb_applied) = pdb;
        *write_lock(&self.entry_file_offset) = entry_file_offset;
        *write_lock(&self.raw_load) = raw;
        *write_lock(&self.program_packs) = packs;
        *write_lock(&self.analysis) = None;
        *write_lock(&self.no_code) = None;
        (loaded.replace(program), dropped)
    }

    /// Returns the annotation overlay as the user left it, without the
    /// binary's name tables.
    pub(crate) fn overlay_plain(&self) -> Overlay {
        read_lock(&self.overlay).clone()
    }

    /// Returns the analysis when one is held, else an empty one, without
    /// computing it: for an edit whose checks read no code, and for the
    /// memo a commit carries over.
    pub(crate) fn analysis_held(&self) -> Arc<Analysis> {
        read_lock(&self.analysis).clone().unwrap_or_default()
    }

    /// Commits `plan` to the overlay under its write lock
    /// ([`edit::commit`]), or, when another edit landed since the plan was
    /// made ([`edit::Stale`]), the plan `again` makes over the overlay as it
    /// is then, under the same lock, so no edit lands in between.
    ///
    /// A tool that read the program outside its lock (a script's run, a
    /// project's identity check) must not land what it found on another
    /// program a `load_binary` put in its place meanwhile: given the
    /// program, the check and the commit hold the program's lock, which
    /// `load_binary` takes to swap the program ([`Self::install`]).
    ///
    /// # Arguments
    ///
    /// * `(p, outside)` - The program the plan was made for, and the same
    ///   program again when the caller read it outside its lock; `None`
    ///   inside a tool body, which holds it.
    /// * `plan` - The plan.
    /// * `again` - Plans the edits again over the overlay as it is. It runs
    ///   under the overlay's write lock, so it must not take that lock.
    ///
    /// # Returns
    ///
    /// The plan committed: `plan`, or the one `again` made.
    ///
    /// # Errors
    ///
    /// When another program is loaded now, the edits planned again are
    /// refused, or the overlay would hold more than a project file holds;
    /// nothing was applied.
    pub(crate) fn commit(
        &self,
        (p, outside): (&Program, Option<&Arc<Program>>),
        plan: Plan,
        again: impl FnOnce(&Overlay) -> anyhow::Result<Plan>,
    ) -> anyhow::Result<Plan> {
        let loaded = outside.map(|_| read_lock(&self.program));
        if let (Some(program), Some(loaded)) = (outside, &loaded)
            && !loaded.as_ref().is_some_and(|now| Arc::ptr_eq(now, program))
        {
            anyhow::bail!("{}", replaced(program));
        }
        let analysis = self.analysis_held();
        let mut overlay = write_lock(&self.overlay);
        match edit::commit(p, &analysis, &mut overlay, &plan) {
            Ok(()) => Ok(plan),
            Err(stale) if stale.is::<edit::Stale>() => {
                let plan = again(&overlay)?;
                edit::commit(p, &analysis, &mut overlay, &plan)?;
                Ok(plan)
            }
            Err(refused) => Err(refused),
        }
    }

    /// Puts a project's annotations in place of the overlay's through the
    /// edit path ([`Edit::Project`]): held to a project's caps, and the
    /// analysis carried over to the names it leaves.
    ///
    /// # Arguments
    ///
    /// * `program` - The program the project was read for, outside its
    ///   lock.
    /// * `put` - The edit that puts the project's annotations in place.
    /// * `made` - The plan already made of `put` over the overlay
    ///   ([`borer_engine::analysis::project::admit`]); `None` plans it here.
    ///
    /// # Returns
    ///
    /// The plan committed.
    ///
    /// # Errors
    ///
    /// When another program is loaded now, or the annotations would pass a
    /// cap; nothing was applied.
    pub(crate) fn put_project(
        &self,
        program: &Arc<Program>,
        put: Edit,
        made: Option<Plan>,
    ) -> anyhow::Result<Plan> {
        let edits = [put];
        let analysis = self.analysis_held();
        let planned = |o: &Overlay| edit::plan(program, &analysis, o, &edits, Force::Refuse);
        made.map_or_else(|| planned(&self.overlay_plain()), Ok)
            .and_then(|made| self.commit((program, Some(program)), made, planned))
    }

    /// Plans `edits` over the overlay a tool read and, unless `dry`,
    /// commits them ([`Self::commit`]), planned again over the overlay as
    /// tools read it ([`tabled`]) when another edit landed first.
    ///
    /// # Arguments
    ///
    /// * `(p, a, o)` - The loaded program, its analysis and the overlay
    ///   the tool read.
    /// * `edits` - The edits.
    /// * `force` - Whether a name another address answers to is taken.
    /// * `dry` - Plan them and write nothing.
    ///
    /// # Returns
    ///
    /// The plan, committed unless `dry`.
    ///
    /// # Errors
    ///
    /// When an edit is refused ([`edit::Refused`]) or the edits would pass
    /// a cap; nothing was applied.
    pub(crate) fn edited(
        &self,
        (p, a, o): (&Program, &Analysis, &Overlay),
        edits: &[Edit],
        force: Force,
        dry: bool,
    ) -> anyhow::Result<Plan> {
        let made = edit::plan(p, a, o, edits, force)?;
        if dry {
            return Ok(made);
        }
        self.commit((p, None), made, |now| {
            edit::plan(p, a, &tabled(now), edits, force)
        })
    }

    /// Runs `f` against the loaded program, its analysis and a snapshot of
    /// the overlay: the prologue of every tool the server keeps that reads
    /// code.
    ///
    /// # Arguments
    ///
    /// * `feature` - The stage the tool reads: [`Feature::Discover`] for
    ///   functions, blocks, references and calls, [`Feature::Decompile`]
    ///   for anything read from lifted code, [`Feature::Emulate`] for
    ///   anything that runs it.
    /// * `f` - The tool body; its `Err` text becomes an invalid-params error.
    ///
    /// # Errors
    ///
    /// Invalid params when no binary is loaded, the engine does not do
    /// `feature` with the architecture or `f` refuses; internal error when
    /// `f` faults.
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

    /// Resolves an address argument: `0x`-hex text, else a name looked up
    /// through the analysis, symbols and overlay, else decimal or bare-hex
    /// text ([`borer_engine::answer::address`]).
    ///
    /// # Arguments
    ///
    /// * `p` - The loaded program.
    /// * `text` - The argument as the agent passed it.
    ///
    /// # Errors
    ///
    /// When the text is neither an address nor a known name, naming the
    /// names nearest it.
    pub(crate) fn addr(&self, p: &Program, text: &str) -> Result<u64, String> {
        borer_engine::answer::address(p, text, || (self.analysis_or_empty(), self.overlay()))
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
    /// ([`borer_engine::answer::entry_of`] says an import's slot is one).
    pub(crate) fn function_entry(
        &self,
        p: &Program,
        a: &Analysis,
        text: &str,
    ) -> Result<u64, String> {
        let va = self.addr(p, text)?;
        borer_engine::answer::entry_of(p, a, va, text)
    }

    /// A server with nothing loaded, the packs `BORER_PACKS` names, live
    /// attaching opened to any process when `BORER_LIVE_ANY` is `1`, and
    /// the request deadline `BORER_DEADLINE_SECS` names.
    pub(crate) fn new() -> BorerServer {
        BorerServer {
            live_any: std::env::var_os(crate::tools::live::LIVE_ANY_ENV).is_some_and(|v| v == "1"),
            gate: crate::requests::Gate::from_env(),
            packs: read_packs(&env_pack_files()).unwrap_or_else(|e| {
                eprintln!("borer: {e:#}; running without packs");
                Arc::default()
            }),
            ..BorerServer::default()
        }
    }

    /// Returns the session's state as it stands, for the worker taking over
    /// on `reload` ([`Self::resume`]): the loaded file, the way it was
    /// loaded, and its names and comments.
    ///
    /// # Arguments
    ///
    /// * `peer_info` - What the client sent at initialize.
    pub(crate) fn resume_state(&self, peer_info: Option<&InitializeRequestParams>) -> Resume {
        Resume {
            peer_info: peer_info.cloned(),
            project: self.loaded().map(|p| {
                borer::project::ProjectFile::from_overlay(
                    &p.path.display().to_string(),
                    None,
                    &read_lock(&self.overlay),
                )
            }),
            pdb: Some(*read_lock(&self.pdb_applied)),
            entry_file_offset: *read_lock(&self.entry_file_offset),
            raw: read_lock(&self.raw_load).clone(),
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
                path: project.0.program,
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
                let word = if self.loaded().is_some_and(|p| p.is_64) {
                    8
                } else {
                    4
                };
                match borer_engine::analysis::utypes::laid_at(&o.types, word) {
                    Ok(()) => {
                        if let Some(program) = self.loaded()
                            && let Err(e) =
                                self.put_project(&program, Edit::Project(Box::new(o)), None)
                        {
                            eprintln!("borer: the handed-over project: {e}");
                        }
                    }
                    Err(e) => eprintln!("borer: the handed-over project's types: {e}"),
                }
            }
        }
        peer_info
    }
}

impl Held for BorerServer {
    /// Everything is decided under the program's lock, so no load in
    /// between pairs one program with another's analysis. A [`Need::Code`]
    /// or [`Need::Best`] view reads the analysis where the program does the
    /// stage, computing it on first use; a [`Need::Best`] one reads the
    /// empty analysis held for the program where it does not, which keeps
    /// a `.NET` listing's index from one read to the next; a [`Need::File`]
    /// one reads the analysis only once one is held.
    fn view(&self, need: Need) -> Option<Result<View, String>> {
        let guard = read_lock(&self.program);
        let program = Arc::clone(guard.as_ref()?);
        let analysis = match need {
            Need::Code(stage) | Need::Best(stage) if program.refuses(stage).is_none() => {
                match self.ensure_analysis() {
                    Ok(a) => Some(a),
                    Err(why) => return Some(Err(why)),
                }
            }
            Need::Code(_) => None,
            Need::Best(_) => Some(self.empty_analysis()),
            Need::File => read_lock(&self.analysis).clone(),
        };
        Some(Ok(View { program, analysis }))
    }

    fn user_overlay(&self) -> Overlay {
        self.overlay_plain()
    }

    /// The analysis is shared, so a recovered function goes into a copy of
    /// it that replaces the stored one. Recoveries run one at a time under
    /// the analysis's write lock and start from the analysis stored then,
    /// so one recovered by a request that ran first is kept; a program
    /// loaded over meanwhile keeps nothing grown for the old one. A request
    /// already holding the old analysis keeps it. The code index `grep`
    /// reads is built from what discovery found
    /// ([`crate::index::load_or_build`]), as the CLI's is, so it does not
    /// hold a function recovered here.
    fn recover(
        &self,
        program: &Arc<Program>,
        base: Arc<Analysis>,
        find: &dyn Fn(&Analysis) -> Option<(Option<Analysis>, u64)>,
    ) -> Option<(Arc<Analysis>, u64)> {
        let loaded = read_lock(&self.program);
        let held = loaded.as_ref().is_some_and(|now| Arc::ptr_eq(now, program));
        let mut slot = write_lock(&self.analysis);
        let start = slot.clone().filter(|_| held).unwrap_or(base);
        let (grown, entry) = find(&start)?;
        let Some(grown) = grown else {
            return Some((start, entry));
        };
        let grown = Arc::new(grown);
        if held {
            *slot = Some(Arc::clone(&grown));
        }
        Some((grown, entry))
    }

    /// A plan committed is committed only to the program the snapshot
    /// read, still loaded ([`BorerServer::commit`]); one another edit
    /// overtook is planned again over the overlay as tools read it.
    fn edit(
        &self,
        s: &Snapshot<'_>,
        edits: &[Edit],
        force: Force,
        apply: Apply,
    ) -> Result<Plan, String> {
        let (p, a, o) = (s.program(), s.analysis(), s.overlay());
        let made = edit::plan(p, a, o, edits, force).map_err(|e| e.to_string())?;
        if apply == Apply::Preview {
            return Ok(made);
        }
        self.commit((p, Some(s.program_arc())), made, |now| {
            edit::plan(p, a, &tabled(now), edits, force)
        })
        .map_err(|e| e.to_string())
    }

    /// The answer is [`BorerServer::read_uri`]'s, which `resources/read`
    /// sends too: the same text, the same errors, and one answer memory, so
    /// a URI read one way is remembered for the other.
    fn read(&self, uri: &str) -> Result<String, Failure> {
        self.read_uri(uri)
            .map(|(_, text)| text)
            .map_err(|e| Failure {
                cause: match e.code {
                    rmcp::model::ErrorCode::INTERNAL_ERROR => Cause::Engine,
                    rmcp::model::ErrorCode::RESOURCE_NOT_FOUND => Cause::Missing,
                    _ => Cause::Asked,
                },
                message: e.message.into_owned(),
            })
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
/// When a file's path is a share or a device (refused before it is
/// opened), a file is not a regular one, holds more than
/// [`borer::packs::PACK_MAX`] bytes, cannot be read or is not a pack.
pub(crate) fn read_packs(files: &[String]) -> anyhow::Result<Arc<Packs>> {
    let mut packs = Vec::with_capacity(files.len());
    for file in files {
        let shown = borer_engine::text::short_path(file);
        let bytes = borer_engine::program::read_regular(Path::new(file), borer::packs::PACK_MAX)
            .map_err(|e| anyhow::anyhow!("{e:#}; give a path to a pack"))?;
        let text = String::from_utf8(bytes)
            .map_err(|_| anyhow::anyhow!("pack {shown} is not a text file"))?;
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
    /// A program whose architecture has no analysis is answered from one
    /// empty analysis per load, so two string pages share one walk.
    ///
    /// # Panics
    ///
    /// When the empty analysis is made again or a page walks again.
    #[test]
    fn a_program_without_analysis_walks_its_strings_once() {
        use crate::params::StringsParams;
        use rmcp::handler::server::wrapper::Parameters;
        let server = crate::testing::code_server(
            borer_engine::program::Arch::Unknown,
            b"plain text here\0more plain text\0",
        );
        assert!(server.ensure_analysis().is_err(), "no analysis to compute");
        let held = server.analysis_or_empty();
        assert!(std::sync::Arc::ptr_eq(&held, &server.analysis_or_empty()));
        for filter in [None, Some("more".to_owned())] {
            let page = server.strings(Parameters(StringsParams {
                min_length: None,
                filter,
                encoding: None,
                offset: None,
                limit: None,
                count_only: None,
            }));
            assert!(page.is_ok(), "{page:?}");
        }
        assert_eq!(held.derived.held("string_walks"), 1);
    }

    /// The empty analysis held for one program is never served to another
    /// put in its place.
    ///
    /// # Panics
    ///
    /// When the new program is answered from the old one's analysis.
    #[test]
    fn an_empty_analysis_is_served_only_to_its_program() {
        use borer_engine::program::{Arch, Program};
        let server = crate::testing::code_server(Arch::Unknown, b"old text\0");
        let old = server.analysis_or_empty();
        let new = Program::raw(b"new text\0".to_vec(), Arch::Unknown, 0, None, Vec::new());
        *crate::state::write_lock(&server.program) = Some(std::sync::Arc::new(new));
        assert!(!std::sync::Arc::ptr_eq(&old, &server.analysis_or_empty()));
    }

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

    /// An analysis a request computed for the program it found loaded is
    /// not kept once `load_binary` loaded another program meanwhile.
    ///
    /// A resource read or a script asks for the analysis outside the
    /// program's lock, so a `load_binary` can finish while the first
    /// analysis of the old program runs; every later tool would then read
    /// the new program's bytes through the old program's functions.
    ///
    /// # Panics
    ///
    /// When the analysis held after the load is not the new program's.
    #[test]
    fn an_analysis_of_a_program_loaded_over_is_not_kept() {
        use crate::testing::load_raw;
        use borer_engine::analysis::Analysis;
        /// Functions in the big program, each calling the next.
        const CHAINED: usize = 60_000;
        let dir = std::env::temp_dir().join(format!("borer-loaded-over-{}", std::process::id()));
        std::fs::create_dir_all(&dir).expect("a scratch directory");
        let (big, small) = (dir.join("big.bin"), dir.join("small.bin"));
        let mut code = Vec::with_capacity(CHAINED * 16);
        for _ in 1..CHAINED {
            // ASM: call $+16; ret; int3 x10
            code.extend_from_slice(&[0xe8, 0x0b, 0, 0, 0, 0xc3]);
            code.extend_from_slice(&[0xcc; 10]);
        }
        code.push(0xc3);
        std::fs::write(&big, &code).expect("written");
        std::fs::write(&small, [0xc3]).expect("written");
        let server = crate::BorerServer::default();
        let load = |path: &std::path::Path| load_raw(&server, path, "0x10000");
        load(&big).expect("the big program loads");
        std::thread::scope(|s| {
            let first = s.spawn(|| server.ensure_analysis().map(|a| a.functions.len()));
            std::thread::sleep(std::time::Duration::from_millis(300));
            load(&small).expect("the small program loads");
            let first = first.join().expect("the first analysis ends");
            assert_eq!(first.expect("the big program analyzes"), CHAINED);
        });
        let held = server.ensure_analysis().expect("analyzes");
        let program = server.loaded().expect("a program is loaded");
        std::fs::remove_dir_all(&dir).expect("cleans up");
        assert_eq!(
            held.functions.len(),
            Analysis::compute(&program).functions.len(),
            "the analysis of the program loaded over was kept for the new one"
        );
    }

    /// A name set on one program never lands on the program `load_binary`
    /// puts in its place.
    ///
    /// `set_name` checks the address against the program it holds the lock
    /// of and writes the overlay; `load_binary` took the overlay away before
    /// it waited for that lock, so a rename running at that moment wrote
    /// the first program's name into the overlay the second one then took.
    /// The two programs sit at different bases, so the name's address is
    /// in no section of the second.
    ///
    /// # Panics
    ///
    /// When the second program's overlay holds the first one's name.
    #[test]
    fn a_name_set_on_one_program_never_lands_on_the_next() {
        use crate::params::SetNameParams;
        use crate::testing::load_raw;
        use rmcp::handler::server::wrapper::Parameters;
        /// Loads of the second program the test checks after.
        const ROUNDS: usize = 300;
        let dir = std::env::temp_dir().join(format!("borer-name-swap-{}", std::process::id()));
        std::fs::create_dir_all(&dir).expect("a scratch directory");
        let file = dir.join("code.bin");
        std::fs::write(&file, [0xc3; 16]).expect("written");
        let server = crate::BorerServer::default();
        let load = |base: &str| load_raw(&server, &file, base);
        let done = std::sync::atomic::AtomicBool::new(false);
        let landed = std::thread::scope(|s| {
            s.spawn(|| {
                while !done.load(std::sync::atomic::Ordering::SeqCst) {
                    let named = server.set_name(Parameters(SetNameParams {
                        address: Some("0x10000".to_owned()),
                        name: Some("from_one".to_owned()),
                        names: None,
                        force: None,
                        dry_run: Some(false),
                    }));
                    if named.is_err() {
                        std::thread::yield_now();
                    }
                }
            });
            let landed = (0..ROUNDS).find_map(|_| {
                load("0x10000").expect("the first program loads");
                load("0x20000").expect("the second program loads");
                let names = super::read_lock(&server.overlay).names.clone();
                (!names.is_empty()).then_some(names)
            });
            done.store(true, std::sync::atomic::Ordering::SeqCst);
            landed
        });
        std::fs::remove_dir_all(&dir).expect("cleans up");
        assert_eq!(
            landed, None,
            "the first program's name landed on the second"
        );
    }

    /// A tool reading the program and a `load_binary` running at once both
    /// finish.
    ///
    /// A tool body holds the program's read lock for its whole run
    /// ([`super::BorerServer::with_program`]); a body that takes the read
    /// lock again (the analysis asked for, which reads the program) while
    /// `load_binary` waits for the write lock waits behind that writer,
    /// which waits for the body: neither ends, and with both request
    /// permits held the server answers nothing again. A file with no code
    /// analysis takes the lock again on every call that asks for the
    /// analysis.
    ///
    /// # Panics
    ///
    /// When the two have not both finished their rounds in time.
    #[test]
    fn a_tool_and_a_load_running_at_once_both_finish() {
        use crate::params::{LoadBinaryParams, StringsParams};
        use rmcp::handler::server::wrapper::Parameters;
        /// Rounds each side runs.
        const ROUNDS: usize = 2_000;
        let path = std::env::temp_dir().join(format!("borer-relock-{}.bin", std::process::id()));
        std::fs::write(&path, b"no code here, only some text to find").expect("written");
        let shown = path.display().to_string();
        let server = crate::BorerServer::default();
        let load = {
            let server = server.clone();
            move || {
                server.load_binary(Parameters(LoadBinaryParams {
                    path: shown.clone(),
                    entry_file_offset: None,
                    pdb: Some(false),
                    arch: None,
                    base: None,
                    entry: None,
                    regions: None,
                }))
            }
        };
        load().expect("the file loads");
        let (done, finished) = std::sync::mpsc::channel();
        let reader = {
            let done = done.clone();
            std::thread::spawn(move || {
                for _ in 0..ROUNDS {
                    let read = server.strings(Parameters(StringsParams {
                        min_length: None,
                        filter: None,
                        encoding: None,
                        offset: None,
                        limit: None,
                        count_only: Some(true),
                    }));
                    assert!(read.is_ok(), "{read:?}");
                }
                done.send("reader").expect("the test waits");
            })
        };
        let loader = std::thread::spawn(move || {
            for _ in 0..ROUNDS {
                load().expect("the file loads");
            }
            done.send("loader").expect("the test waits");
        });
        let ended: Vec<&str> = (0..2)
            .map_while(|_| {
                finished
                    .recv_timeout(std::time::Duration::from_mins(1))
                    .ok()
            })
            .collect();
        std::fs::remove_file(&path).ok();
        assert_eq!(
            ended.len(),
            2,
            "only {ended:?} finished: the tool and the load hold each other"
        );
        reader.join().expect("the reader ends");
        loader.join().expect("the loader ends");
    }

    /// The shipped build unwinds on panic, so the request guard in
    /// [`super::BorerServer::with_program`] catches a fault instead of the
    /// process aborting and ending the session.
    ///
    /// # Panics
    ///
    /// When the `dist` profile aborts on panic.
    #[test]
    fn the_shipped_build_unwinds_on_panic() {
        let manifest = include_str!("../../../Cargo.toml");
        let dist: Vec<&str> = manifest
            .lines()
            .skip_while(|l| l.trim() != "[profile.dist]")
            .skip(1)
            .take_while(|l| !l.starts_with('['))
            .collect();
        assert!(
            dist.iter().any(|l| l.trim() == "panic = \"unwind\""),
            "{dist:?}"
        );
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

    /// A pack file, and every script a pack names, is refused before it is
    /// read when its path names a share or a device.
    ///
    /// A script's path is the pack's own directory joined to the line's
    /// words, so one climbing with `..` from a `\\.\` pack path reached the
    /// share it named, and a `nul` line read the device as a script.
    ///
    /// # Panics
    ///
    /// When such a path is read.
    #[test]
    fn a_pack_and_its_scripts_are_checked_before_they_are_read() {
        if !cfg!(windows) {
            return;
        }
        let share = super::read_packs(&[r"\\host.invalid\share\p.borer".to_owned()])
            .expect_err("a share is never read");
        assert!(
            share.to_string().contains("names a network share"),
            "{share}"
        );
        let dir = std::env::temp_dir().join(format!("borer-pack-paths-{}", std::process::id()));
        std::fs::create_dir_all(&dir).expect("a scratch directory");
        let climb = format!("{}UNC/host.invalid/share/x.rhai", "../".repeat(32));
        let mut refused = Vec::new();
        for (name, script, why) in [
            ("climb", climb.as_str(), "`..`"),
            ("device", "nul", "device"),
        ] {
            let pack = dir.join(format!("{name}.borer"));
            std::fs::write(&pack, format!("pack {name} 1\n[scripts]\nrun {script}\n"))
                .expect("written");
            let read = super::read_packs(&[format!(r"\\.\{}", pack.display())]);
            refused.push((why, read.map(|_| ()).map_err(|e| e.to_string())));
        }
        std::fs::remove_dir_all(&dir).expect("cleans up");
        for (why, read) in refused {
            let said = read.expect_err("a script path is checked before it is read");
            assert!(said.contains(why), "{said}");
        }
    }

    /// A pack is read through the checked reader, which judges the file
    /// before it opens it: a directory is refused by its metadata, where
    /// the read failed with whatever the system said.
    ///
    /// # Panics
    ///
    /// When the directory is read as a pack.
    #[test]
    fn a_pack_that_is_a_directory_is_refused_by_its_metadata() {
        let dir = std::env::temp_dir().display().to_string();
        let refused = super::read_packs(&[dir]).expect_err("a directory is no pack");
        assert!(refused.to_string().contains("is a directory"), "{refused}");
    }

    /// A handed-over project whose types do not lay out at the reloaded
    /// program's pointer width installs none of its annotations on resume,
    /// and one whose types do installs its names.
    ///
    /// # Panics
    ///
    /// When the narrow layout's names are installed, or the plain
    /// project's are not.
    #[test]
    fn resume_refuses_types_the_reloaded_width_does_not_lay_out() {
        use crate::handover::Resume;
        let path =
            std::env::temp_dir().join(format!("borer-resume-layout-{}.bin", std::process::id()));
        std::fs::write(&path, [0xc3; 16]).expect("written");
        let program = serde_json::to_string(&path.display().to_string()).expect("a path");
        let resumed = |types: &str| {
            let json = format!(
                r#"{{"program":{program},"names":{{"0x10000":"kept"}},"comments":{{}}{types}}}"#
            );
            let server = crate::BorerServer::default();
            server.resume(Resume {
                project: Some(borer::project::ProjectFile(
                    serde_json::from_str(&json).expect("a project"),
                )),
                pdb: Some(false),
                raw: super::RawLoad {
                    arch: Some(super::RawArch::X64),
                    base: Some("0x10000".to_owned()),
                    ..super::RawLoad::default()
                },
                ..Resume::default()
            });
            assert!(server.loaded().is_some(), "the program reloads");
            super::read_lock(&server.overlay)
                .names
                .get(&0x10000)
                .cloned()
        };
        let plain = resumed("");
        let narrow = resumed(
            r#","types":{"W":{"Struct":{"size":8,"fields":{"0":{"name":"ptr","ty":{"Ptr":"U16"}},"4":{"name":"tag","ty":"U32"}}}}}"#,
        );
        std::fs::remove_file(&path).expect("cleans up");
        assert_eq!(plain.as_deref(), Some("kept"));
        assert_eq!(narrow, None, "a 4-byte pointer layout installed on x64");
    }

    /// A script's snapshot is the loaded program with its own analysis,
    /// and is refused with nothing loaded or nothing to disassemble.
    ///
    /// # Panics
    ///
    /// When the parts do not belong together or a refusal answers.
    #[test]
    fn a_script_snapshot_holds_one_program() {
        let server = crate::testing::code_server(borer_engine::program::Arch::X86_64, &[0xc3]);
        let (program, analysis, _) = server.script_snapshot().expect("snapshots");
        assert!(
            server
                .loaded()
                .is_some_and(|now| std::sync::Arc::ptr_eq(&now, &program))
        );
        let held = server.ensure_analysis().expect("analyzed");
        assert!(std::sync::Arc::ptr_eq(&held, &analysis));
        let none = crate::BorerServer::default()
            .script_snapshot()
            .expect_err("nothing loaded");
        assert_eq!(none.message, super::NO_BINARY);
        let unknown = crate::testing::code_server(borer_engine::program::Arch::Unknown, &[0xc3]);
        assert!(unknown.script_snapshot().is_err());
    }
}
