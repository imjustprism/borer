//! What a tool reads through.
//!
//! A front end gives the catalog one thing: a consistent view of the program
//! it holds and that program's analysis, as a tool's [`Need`] asks for them
//! ([`Held::view`]), with the names the user left. The catalog owns the rest
//! of a tool's execution ([`run`]): the refusal before a load, the fault
//! guard, the overlay as tools read it ([`tabled`]) and one [`Snapshot`] a
//! body reads everything from, so its program and analysis are one pair.

use std::collections::BTreeSet;
use std::sync::Arc;

use borer_engine::analysis::edit::{self, Edit, Force, Plan};
use borer_engine::analysis::{Analysis, EnumSource, Overlay};
use borer_engine::answer::{self, Need};
use borer_engine::clr::managed;
use borer_engine::program::{Feature, Program};
use borer_engine::script::Query;

/// Who a failed tool call is on.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Cause {
    /// The request: an argument that does not read, an address that names
    /// nothing, nothing loaded. The caller fixes the call.
    Asked,
    /// The engine: an analysis pass faulted. Another call may still answer.
    Engine,
    /// The thing named is not there: a resource URI no resource answers.
    Missing,
}

/// Why a tool did not answer, in words its caller can act on.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Failure {
    /// Who it is on.
    pub cause: Cause,
    /// What happened, one line or a few.
    pub message: String,
}

impl Failure {
    /// Returns the refusal of a request.
    ///
    /// # Arguments
    ///
    /// * `message` - What is wrong with it.
    #[must_use]
    pub fn asked(message: impl Into<String>) -> Failure {
        Failure {
            cause: Cause::Asked,
            message: message.into(),
        }
    }
}

impl std::fmt::Display for Failure {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.message)
    }
}

/// The refusal every tool answers before a binary is loaded.
pub const NO_BINARY: &str = "no binary loaded; call load_binary first";

/// Returns the message a caught panic carries, for an answer that says a
/// tool faulted.
///
/// # Arguments
///
/// * `e` - The panic's payload, as `catch_unwind` hands it back.
///
/// # Returns
///
/// The payload's text, or `no message` when it is neither `&str` nor
/// `String`.
#[must_use]
pub fn fault_text(e: &(dyn std::any::Any + Send)) -> String {
    e.downcast_ref::<&str>()
        .map(|s| (*s).to_owned())
        .or_else(|| e.downcast_ref::<String>().cloned())
        .unwrap_or_else(|| "no message".to_owned())
}

/// Runs `f` behind the fault boundary of a tool body.
///
/// A fault in an analysis pass would unwind out of the handler and take
/// the front end's session with it; caught here, it is an answer the caller
/// can read and act on.
///
/// # Arguments
///
/// * `f` - The work; its `Err` text is a refusal of the request.
///
/// # Errors
///
/// [`Cause::Asked`] when `f` refuses; [`Cause::Engine`] only when `f`
/// faults.
pub fn guarded<T>(f: impl FnOnce() -> Result<T, String>) -> Result<T, Failure> {
    match std::panic::catch_unwind(std::panic::AssertUnwindSafe(f)) {
        Ok(answer) => answer.map_err(Failure::asked),
        Err(e) => Err(Failure {
            cause: Cause::Engine,
            message: format!(
                "the analysis faulted on this binary: {}. The session is still up; another tool or another address may still answer.",
                fault_text(e.as_ref())
            ),
        }),
    }
}

/// Returns `o` as tools read it: constants rendered by the binary's own
/// name tables ([`EnumSource::Binary`]).
///
/// # Arguments
///
/// * `o` - The overlay as the user left it.
#[must_use]
pub fn tabled(o: &Overlay) -> Overlay {
    Overlay {
        enum_source: EnumSource::Binary,
        ..o.clone()
    }
}

/// The program a front end holds and its analysis, taken together.
#[derive(Debug, Clone)]
pub struct View {
    /// The program held.
    pub program: Arc<Program>,
    /// Its analysis as the [`Need`] asked: the program's own for
    /// [`Need::Code`] and [`Need::Best`] where it does the stage, an empty
    /// one for [`Need::Best`] where it does not, `None` for [`Need::Code`]
    /// where it does not, and the one already held, if any, for
    /// [`Need::File`].
    pub analysis: Option<Arc<Analysis>>,
}

/// Finds a function in an analysis, or grows a copy that holds it: the grown
/// copy (`None` when the analysis given holds it) and the entry.
pub type Find<'a> = &'a dyn Fn(&Analysis) -> Option<(Option<Analysis>, u64)>;

/// Whether an edit a tool planned is written.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Apply {
    /// Plan only: a dry run, or a proposal the face holds for its person.
    Preview,
    /// Plan and commit, where the face commits edits.
    Commit,
}

/// What a front end holds for its tools: one program, its analysis and the
/// names in force.
///
/// The MCP server holds them behind its session's locks, computing the
/// analysis on first use; the app holds a binary's snapshot ([`super::Loaded`]).
/// A tool reads only through a [`Snapshot`] the catalog builds from these.
pub trait Held {
    /// Returns the program held with its analysis as `need` asks, taken
    /// together, so the analysis is that program's.
    ///
    /// # Arguments
    ///
    /// * `need` - What the tool reads of the program.
    ///
    /// # Returns
    ///
    /// `None` before a program is loaded; `Err` when the analysis the need
    /// asks for cannot be had, with the reason.
    fn view(&self, need: Need) -> Option<Result<View, String>>;

    /// Returns the names, comments and types as the user left them.
    fn user_overlay(&self) -> Overlay;

    /// Finds the function a decompile names in the analysis this face keeps
    /// for `program`, starting one where `find` grows one
    /// ([`borer_engine::answer::recovered`]), and keeps what it grew.
    ///
    /// This default grows `base` for the one read; a face that keeps its
    /// analysis between reads stores the grown one.
    ///
    /// # Arguments
    ///
    /// * `_program` - The program the snapshot holds.
    /// * `base` - The snapshot's analysis.
    /// * `find` - Finds the function in an analysis, or grows a copy holding it.
    ///
    /// # Returns
    ///
    /// The analysis that holds the function and its entry; `None` when
    /// `find` finds none.
    fn recover(
        &self,
        _program: &Arc<Program>,
        base: Arc<Analysis>,
        find: Find<'_>,
    ) -> Option<(Arc<Analysis>, u64)> {
        let (grown, entry) = find(&base)?;
        Some((grown.map_or(base, Arc::new), entry))
    }

    /// Plans edits over the names in force and, where this face commits
    /// edits and `apply` asks, commits them: the seam every edit tool goes
    /// through, so a face decides whether a plan lands or waits as a
    /// proposal.
    ///
    /// This default only plans, whatever `apply` asks: a face that holds
    /// proposals for a person overrides it to keep the plan, which the
    /// tool's answer words as applied when `apply` asked, so the face shows
    /// it as a proposal and never commits it from the handler.
    ///
    /// # Arguments
    ///
    /// * `s` - The snapshot the tool read.
    /// * `edits` - The edits.
    /// * `force` - Whether a name another address answers to is taken.
    /// * `_apply` - Whether to commit where the face commits.
    ///
    /// # Returns
    ///
    /// The plan, committed when the face committed it.
    ///
    /// # Errors
    ///
    /// An [`edit::Refused`] naming the edit refused, or the cap the edits
    /// would pass; nothing was applied.
    fn edit(
        &self,
        s: &Snapshot<'_>,
        edits: &[Edit],
        force: Force,
        _apply: Apply,
    ) -> anyhow::Result<Plan> {
        edit::plan(s.program(), s.analysis(), s.overlay(), edits, force)
    }

    /// Returns how a script's `query(uri)` reads a resource on this face:
    /// the text alone, page suffixes read, without a session's memory of
    /// answers or byte budget.
    ///
    /// The script holds it past the call that made it, so it owns what it
    /// reads through.
    fn querier(&self) -> Query;

    /// Answers a `borer://` resource URI as the `query` tool reads it, page
    /// suffixes and all; [`super::ask`] answers what the engine answers.
    ///
    /// # Arguments
    ///
    /// * `uri` - The URI as the caller wrote it.
    ///
    /// # Errors
    ///
    /// When the URI names no resource, a suffix does not read, or the
    /// resource refuses.
    fn read(&self, uri: &str) -> Result<String, Failure>;
}

/// One consistent reading of what a front end holds: the program, its
/// analysis and the names as tools read them, built by [`run`].
pub struct Snapshot<'h> {
    /// What the front end holds, for a later view of the same program.
    held: &'h dyn Held,
    /// What the snapshot was taken for.
    need: Need,
    /// The program.
    program: Arc<Program>,
    /// Its analysis as `need` asked, an empty one where none was given.
    analysis: Arc<Analysis>,
    /// Whether the front end gave an analysis.
    given: bool,
    /// The names as tools read them.
    overlay: Overlay,
}

impl std::fmt::Debug for Snapshot<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Snapshot")
            .field("need", &self.need)
            .field("program", &self.program.path)
            .field("given", &self.given)
            .finish_non_exhaustive()
    }
}

impl Snapshot<'_> {
    /// Returns the program.
    #[must_use]
    pub fn program(&self) -> &Program {
        &self.program
    }

    /// Returns the program as held, shared.
    #[must_use]
    pub fn program_arc(&self) -> &Arc<Program> {
        &self.program
    }

    /// Returns the analysis taken, an empty one where none was given.
    #[must_use]
    pub fn analysis(&self) -> &Analysis {
        &self.analysis
    }

    /// Returns the analysis taken, shared.
    #[must_use]
    pub fn analysis_arc(&self) -> &Arc<Analysis> {
        &self.analysis
    }

    /// Returns the analysis the front end gave, `None` where it gave none.
    #[must_use]
    pub fn kept(&self) -> Option<&Analysis> {
        self.given.then_some(&*self.analysis)
    }

    /// Returns the names, comments and types as tools read them.
    #[must_use]
    pub fn overlay(&self) -> &Overlay {
        &self.overlay
    }

    /// Returns the analysis a body reading `stage` reads.
    ///
    /// # Arguments
    ///
    /// * `stage` - The stage the body reads.
    ///
    /// # Errors
    ///
    /// The sentence [`Program::refuses`] gives when the program does not do
    /// the stage.
    pub fn code(&self, stage: Feature) -> Result<&Analysis, String> {
        match self.program.refuses(stage) {
            Some(why) => Err(why),
            None => Ok(&self.analysis),
        }
    }

    /// Returns the analysis names are looked up in: the one taken, or, for
    /// a snapshot taken for the file alone, the program's own or an empty
    /// one, asked for only now.
    fn names(&self) -> Arc<Analysis> {
        if !matches!(self.need, Need::File) {
            return Arc::clone(&self.analysis);
        }
        match self.held.view(Need::Best(Feature::Discover)) {
            Some(Ok(View {
                program,
                analysis: Some(a),
            })) if Arc::ptr_eq(&program, &self.program) => a,
            Some(_) | None => Arc::default(),
        }
    }

    /// Resolves an address argument: `0x`-hex text, else a name looked up
    /// through the analysis, symbols and names in force, else decimal
    /// ([`borer_engine::answer::address`]).
    ///
    /// # Arguments
    ///
    /// * `text` - The argument as the caller passed it.
    ///
    /// # Errors
    ///
    /// When the text is neither an address nor a known name, naming the
    /// names nearest it.
    pub fn addr(&self, text: &str) -> Result<u64, String> {
        answer::address(&self.program, text, || (self.names(), &self.overlay))
    }

    /// Resolves an argument to the entry of the discovered function
    /// containing it.
    ///
    /// # Arguments
    ///
    /// * `text` - Address or name ([`Snapshot::addr`]).
    ///
    /// # Errors
    ///
    /// When the text does not resolve or no function contains the address.
    pub fn entry(&self, text: &str) -> Result<u64, String> {
        answer::entry_of(&self.program, &self.analysis, self.addr(text)?, text)
    }

    /// Returns the .NET members an argument names, when it names managed
    /// code ([`managed::named`]).
    ///
    /// # Arguments
    ///
    /// * `text` - The argument as the caller passed it.
    #[must_use]
    pub fn managed(&self, text: &str) -> Option<BTreeSet<u32>> {
        self.program.clr()?;
        managed::named(&self.program, text, self.addr(text).ok())
    }

    /// Returns the IL method an argument names ([`managed::il_method_named`]).
    ///
    /// # Arguments
    ///
    /// * `text` - The argument as the caller passed it.
    #[must_use]
    pub fn il_method(&self, text: &str) -> Option<u32> {
        self.program.clr()?;
        managed::il_method_named(&self.program, text, self.addr(text).ok())
    }

    /// Resolves the function to decompile at an argument, starting one at an
    /// ARM32 address no discovered function's blocks hold, through the
    /// front end that keeps it ([`Held::recover`]).
    ///
    /// # Arguments
    ///
    /// * `text` - Address or name ([`Snapshot::addr`]).
    ///
    /// # Returns
    ///
    /// The analysis that holds the function, and its entry.
    ///
    /// # Errors
    ///
    /// When the text names nothing, or no function holds the address and
    /// none starts there.
    pub fn decompile_entry(&self, text: &str) -> Result<(Arc<Analysis>, u64), String> {
        let (p, a) = (&self.program, &self.analysis);
        let va = self.addr(text)?;
        if let Some(entry) = answer::held_entry(p, a, va) {
            return Ok((Arc::clone(a), entry));
        }
        let find = |base: &Analysis| answer::recovered(p, base, va);
        match self.held.recover(p, Arc::clone(a), &find) {
            Some(found) => Ok(found),
            None => Ok((Arc::clone(a), answer::entry_of(p, a, va, text)?)),
        }
    }

    /// Plans edits and, where the front end commits and `apply` asks,
    /// commits them ([`Held::edit`]).
    ///
    /// # Arguments
    ///
    /// * `edits` - The edits.
    /// * `force` - Whether a name another address answers to is taken.
    /// * `apply` - Whether to commit where the face commits.
    ///
    /// # Errors
    ///
    /// An [`edit::Refused`] naming the edit refused, the cap the edits
    /// would pass, or why the face did not commit.
    pub fn edit(&self, edits: &[Edit], force: Force, apply: Apply) -> anyhow::Result<Plan> {
        self.held.edit(self, edits, force, apply)
    }
}

/// Runs a tool body against one snapshot of what a front end holds: the
/// execution policy every tool shares.
///
/// Nothing loaded is [`NO_BINARY`]; a [`Need::Code`] stage the program
/// does not do is refused with the sentence [`Program::refuses`] gives;
/// the view, the body and anything they fault in run behind [`guarded`].
///
/// # Arguments
///
/// * `h` - What the front end holds.
/// * `need` - What the body reads of the program.
/// * `body` - The tool body; its `Err` text is a refusal.
///
/// # Errors
///
/// [`Cause::Asked`] for a refusal, [`Cause::Engine`] for a fault.
pub fn run(
    h: &dyn Held,
    need: Need,
    body: impl FnOnce(&Snapshot<'_>) -> Result<String, String>,
) -> Result<String, Failure> {
    guarded(|| body(&snapshot(h, need)?))
}

/// Takes a snapshot of what a front end holds ([`run`]).
///
/// # Arguments
///
/// * `h` - What the front end holds.
/// * `need` - What the body reads of the program.
///
/// # Errors
///
/// [`NO_BINARY`] before a load; the view's refusal; the program's when a
/// [`Need::Code`] stage is one it does not do.
pub fn snapshot(h: &dyn Held, need: Need) -> Result<Snapshot<'_>, String> {
    let view = h.view(need).ok_or(NO_BINARY)??;
    if let Need::Code(stage) = need
        && let Some(why) = view.program.refuses(stage)
    {
        return Err(why);
    }
    Ok(Snapshot {
        held: h,
        need,
        given: view.analysis.is_some(),
        analysis: view.analysis.unwrap_or_default(),
        program: view.program,
        overlay: tabled(&h.user_overlay()),
    })
}
