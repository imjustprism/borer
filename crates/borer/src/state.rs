//! The server's state: what is loaded, its analysis and names, the locks
//! around them, and how a server starts or resumes.

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex, MutexGuard, PoisonError, RwLock, RwLockReadGuard, RwLockWriteGuard};

use borer_engine::analysis::{Analysis, EnumSource, Overlay, parse_addr};
use borer_engine::clr::managed;
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

    /// Returns an answer drawn from facts of the loaded file, the facts kept
    /// in the memo of its analysis ([`Analysis::derived`]) once the
    /// analysis is held.
    ///
    /// Some answers read the file's bytes alone, hashing, carving or
    /// decoding all of them, which took a second on every read of a
    /// hundred-megabyte file. The facts are kept once, whatever the
    /// question, and `answer` reads each question off them. They do not
    /// wait for an analysis that is not there yet: without one the facts
    /// are worked out each time, as before.
    ///
    /// # Arguments
    ///
    /// * `kind` - What the facts are, as a fixed name.
    /// * `make` - Works the facts out from the program.
    /// * `answer` - Renders the answer from the facts.
    ///
    /// # Errors
    ///
    /// When no binary is loaded.
    pub(crate) fn file_fact<T: Send + Sync + 'static>(
        &self,
        kind: &'static str,
        make: impl FnOnce(&Program) -> T,
        answer: impl FnOnce(&T) -> String,
    ) -> Result<String, ErrorData> {
        self.with_program(|p| {
            let held = read_lock(&self.analysis).clone();
            Ok(match held {
                Some(a) => answer(&a.derived.get_or_build(kind, (), || make(p))),
                None => answer(&make(p)),
            })
        })
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
    /// A caller outside a tool body holds no lock on the program while the
    /// analysis is computed, so a `load_binary` may finish meanwhile: the
    /// analysis is kept only when the program it was computed for is still
    /// the one loaded, checked under the program's lock, which
    /// `load_binary` takes to replace the program and drop its analysis.
    /// When another request stored an analysis of the same program first,
    /// that one is kept and returned, so a function it recovered
    /// ([`Self::decompile_entry`]) is not dropped. The analysis is computed
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

    /// Puts `program` in place of the loaded one, with the way it was
    /// loaded, and lets go of what belonged to the old one: its names and
    /// comments, its analysis and its string walks.
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
        *write_lock(&self.strings) = None;
        (loaded.replace(program), dropped)
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

    /// Edits the overlay with `edit` when `program` is still the program
    /// loaded, then carries the analysis over to the names it leaves
    /// ([`Self::names_changed`]).
    ///
    /// A tool that read the program outside its lock (a script's run, a
    /// project's identity check) must not land what it found on another
    /// program a `load_binary` put in its place meanwhile: the check and
    /// the edit hold the program's lock, which `load_binary` takes to swap
    /// the program ([`Self::install`]).
    ///
    /// # Arguments
    ///
    /// * `program` - The program the edit was worked out for.
    /// * `edit` - The edit.
    ///
    /// # Errors
    ///
    /// When another program is loaded now; nothing was edited.
    pub(crate) fn edit_overlay_of(
        &self,
        program: &Arc<Program>,
        edit: impl FnOnce(&mut Overlay),
    ) -> Result<(), String> {
        let loaded = read_lock(&self.program);
        if !loaded.as_ref().is_some_and(|now| Arc::ptr_eq(now, program)) {
            return Err(format!(
                "{} is no longer the loaded binary (a load_binary ran meanwhile); nothing was applied",
                program.path.display()
            ));
        }
        let before = self.overlay_plain();
        edit(&mut write_lock(&self.overlay));
        self.names_changed(&before);
        Ok(())
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

    /// The .NET members an argument names, when it names managed code
    /// ([`managed::named`]).
    ///
    /// # Arguments
    ///
    /// * `p` - The loaded program.
    /// * `text` - The argument as the agent passed it.
    pub(crate) fn managed_targets(&self, p: &Program, text: &str) -> Option<BTreeSet<u32>> {
        p.clr()?;
        managed::named(p, text, self.addr(p, text).ok())
    }

    /// The IL method an argument names ([`managed::il_method_named`]).
    ///
    /// # Arguments
    ///
    /// * `p` - The loaded program.
    /// * `text` - The argument as the agent passed it.
    pub(crate) fn il_method(&self, p: &Program, text: &str) -> Option<u32> {
        p.clr()?;
        managed::il_method_named(p, text, self.addr(p, text).ok())
    }

    /// Answers a request about managed code with the program and its
    /// analysis, or an empty analysis when the machine has no native
    /// discovery: .NET metadata and IL read the same on any machine.
    ///
    /// # Arguments
    ///
    /// * `f` - The answer.
    ///
    /// # Errors
    ///
    /// When no binary is loaded, or `f`'s error.
    pub(crate) fn with_managed(
        &self,
        f: impl FnOnce(&Program, &Analysis) -> Result<String, String>,
    ) -> Result<String, ErrorData> {
        self.with_program(|p| f(p, &self.analysis_or_empty()))
    }

    /// Answers through [`Self::with_managed`] with what `pick` read off the
    /// program loaded now, refusing when another binary was loaded between
    /// the pick and the answer, so no token meets another file.
    ///
    /// # Arguments
    ///
    /// * `pick` - What the request names, `None` when it names no managed
    ///   code.
    /// * `f` - The answer for what was picked.
    ///
    /// # Returns
    ///
    /// The answer, `None` when nothing is loaded or `pick` found nothing.
    fn managed_pick<T>(
        &self,
        pick: impl FnOnce(&Program) -> Option<T>,
        f: impl FnOnce(&Program, &Analysis, T) -> Result<String, String>,
    ) -> Option<Result<String, ErrorData>> {
        let picked_from = self.loaded()?;
        let picked = pick(&picked_from)?;
        Some(self.with_managed(|p, a| {
            if !std::ptr::eq(p, Arc::as_ptr(&picked_from)) {
                return Err("another binary was loaded during the request; ask again".to_owned());
            }
            f(p, a, picked)
        }))
    }

    /// Answers a request naming .NET members ([`Self::managed_targets`])
    /// through [`Self::with_managed`].
    ///
    /// # Arguments
    ///
    /// * `text` - The argument as the agent passed it.
    /// * `f` - The answer for the tokens it names.
    ///
    /// # Returns
    ///
    /// The answer, `None` when the argument names no managed code and the
    /// caller answers it natively.
    pub(crate) fn managed_answer(
        &self,
        text: &str,
        f: impl FnOnce(&Program, &Analysis, &BTreeSet<u32>) -> Result<String, String>,
    ) -> Option<Result<String, ErrorData>> {
        self.managed_pick(
            |p| self.managed_targets(p, text),
            |p, a, targets| f(p, a, &targets),
        )
    }

    /// Answers a request naming an IL method ([`Self::il_method`]) through
    /// [`Self::with_managed`].
    ///
    /// # Arguments
    ///
    /// * `text` - The argument as the agent passed it.
    /// * `f` - The answer for the method's token.
    ///
    /// # Returns
    ///
    /// The answer, `None` when the argument names no IL method and the
    /// caller answers it natively.
    pub(crate) fn il_answer(
        &self,
        text: &str,
        f: impl FnOnce(&Program, &Analysis, u32) -> Result<String, String>,
    ) -> Option<Result<String, ErrorData>> {
        self.managed_pick(|p| self.il_method(p, text), f)
    }

    /// Resolves an argument to the function to decompile, starting one at an
    /// ARM32 address no discovered function's blocks hold.
    ///
    /// The analysis is shared, so a recovered function goes into a copy of
    /// it ([`borer_engine::analysis::entry_or_gap`]) that replaces the stored
    /// one. Recoveries run one at a time under the analysis's write lock and
    /// start from the analysis stored then, so one recovered by a request
    /// that ran first is kept; the program cannot change meanwhile, as the
    /// tool body holds its read lock. A request already holding the old
    /// analysis keeps it. The code index `grep` reads is built from what
    /// discovery found ([`crate::index::load_or_build`]), as the CLI's is, so
    /// it does not hold a function recovered here.
    ///
    /// # Arguments
    ///
    /// * `p` - The loaded program.
    /// * `a` - Its analysis.
    /// * `text` - Address or name (see [`Self::addr`]).
    ///
    /// # Returns
    ///
    /// The analysis that holds the function, and the function's entry.
    ///
    /// # Errors
    ///
    /// As [`Self::function_entry`], when no function holds the address and
    /// none starts there.
    pub(crate) fn decompile_entry(
        &self,
        p: &Program,
        a: Arc<Analysis>,
        text: &str,
    ) -> Result<(Arc<Analysis>, u64), String> {
        let va = self.addr(p, text)?;
        let held = borer_engine::analysis::function_entry(p, &a, va)
            .ok()
            .filter(|&e| borer_engine::analysis::in_blocks(p, &a, e, va));
        if let Some(entry) = held {
            return Ok((a, entry));
        }
        if p.arch == borer_engine::program::Arch::Arm {
            let mut slot = write_lock(&self.analysis);
            let base = slot.clone().unwrap_or_else(|| Arc::clone(&a));
            let held = borer_engine::analysis::function_entry(p, &base, va)
                .ok()
                .filter(|&e| borer_engine::analysis::in_blocks(p, &base, e, va));
            if let Some(entry) = held {
                return Ok((base, entry));
            }
            let mut grown = (*base).clone();
            if let Ok(entry) = borer_engine::analysis::entry_or_gap(p, &mut grown, va)
                && grown.functions.len() > base.functions.len()
            {
                let grown = Arc::new(grown);
                *slot = Some(Arc::clone(&grown));
                return Ok((grown, entry));
            }
        }
        let entry = self.function_entry(p, &a, text)?;
        Ok((a, entry))
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
        use borer_engine::program::Feature;
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
            let first = s.spawn(|| {
                server
                    .analysis(Feature::Discover)
                    .map(|a| a.functions.len())
            });
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
}
