//! What a tool reads through: the program a front end holds, its analysis
//! and its names ([`Held`]), the lookups every tool makes over them
//! ([`HeldExt`]), and how a tool fails ([`Failure`]).

use std::collections::BTreeSet;
use std::sync::Arc;

use borer_engine::analysis::{Analysis, Overlay};
use borer_engine::clr::managed;
use borer_engine::program::{Feature, Program};

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

/// A tool body, run against the program held.
pub type Body<'a> = Box<dyn FnOnce(&Program) -> Result<String, String> + 'a>;

/// What a front end holds for its tools: one program, its analysis and the
/// names in force.
///
/// The MCP server holds them behind its session's locks, computing the
/// analysis on first use; the app holds a binary's snapshot. A tool reads
/// only through these, so it answers alike on both.
pub trait Held {
    /// Runs a tool body against the program held, under whatever keeps
    /// that program in place while it runs, behind the fault boundary
    /// ([`guarded`]).
    ///
    /// # Arguments
    ///
    /// * `body` - The tool body; its `Err` text is a refusal.
    ///
    /// # Errors
    ///
    /// [`NO_BINARY`] when nothing is loaded; the body's refusal or fault.
    fn run(&self, body: Body<'_>) -> Result<String, Failure>;

    /// Returns the program held, `None` before one is loaded.
    fn loaded(&self) -> Option<Arc<Program>>;

    /// Returns the analysis of the program held, computing it on first use.
    ///
    /// # Errors
    ///
    /// When nothing is loaded or its architecture has no code analysis.
    fn ensure_analysis(&self) -> Result<Arc<Analysis>, String>;

    /// Returns the analysis, or an empty one held for the program when its
    /// architecture has none, so facts of the file still answer.
    fn analysis_or_empty(&self) -> Arc<Analysis>;

    /// Returns the analysis when one is held, without computing it.
    fn analysis_kept(&self) -> Option<Arc<Analysis>>;

    /// Returns a snapshot of the names, comments and types in force, with
    /// constants rendered by the binary's name tables.
    fn overlay(&self) -> Overlay;

    /// Resolves the function to decompile at an argument, starting one at
    /// an ARM32 address no discovered function's blocks hold
    /// ([`borer_engine::answer::decompile_entry`]).
    ///
    /// A front end that keeps the recovered function for later reads stores
    /// the grown analysis; this default keeps it for the one read.
    ///
    /// # Arguments
    ///
    /// * `p` - The program held.
    /// * `a` - Its analysis.
    /// * `text` - The function as the caller wrote it.
    ///
    /// # Returns
    ///
    /// The analysis that holds the function, and its entry.
    ///
    /// # Errors
    ///
    /// When the text names nothing, or no function holds the address and
    /// none starts there.
    fn decompile_entry(
        &self,
        p: &Program,
        a: Arc<Analysis>,
        text: &str,
    ) -> Result<(Arc<Analysis>, u64), String> {
        let (grown, entry) = borer_engine::answer::decompile_entry(p, &a, &self.overlay(), text)?;
        Ok((grown.map_or(a, Arc::new), entry))
    }

    /// Answers a `borer://` resource URI as the `query` tool reads it, page
    /// suffixes and all.
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

/// The lookups every tool makes through what a front end holds.
pub trait HeldExt: Held {
    /// Runs `f` against the program held, its analysis and a snapshot of
    /// the names: the prologue of every tool that reads code.
    ///
    /// A tool names the stage it reads, so a program whose instruction set
    /// has functions but no lifter yet answers the discovery tools and
    /// refuses the rest with the sentence [`Program::refuses`] gives,
    /// rather than an answer read as "nothing found".
    ///
    /// # Arguments
    ///
    /// * `feature` - The stage the tool reads.
    /// * `f` - The tool body; its `Err` text is a refusal.
    ///
    /// # Errors
    ///
    /// When nothing is loaded, the engine does not do `feature` with the
    /// architecture, or `f` refuses or faults.
    fn with_analysis(
        &self,
        feature: Feature,
        f: impl FnOnce(&Program, &Analysis, &Overlay) -> Result<String, String>,
    ) -> Result<String, Failure> {
        self.run(Box::new(|p| {
            if let Some(why) = p.refuses(feature) {
                return Err(why);
            }
            let a = self.ensure_analysis()?;
            f(p, &a, &self.overlay())
        }))
    }

    /// Resolves an address argument: `0x`-hex text, else a name looked up
    /// through the analysis, symbols and names in force, else decimal
    /// ([`borer_engine::answer::address`]).
    ///
    /// # Arguments
    ///
    /// * `p` - The program held.
    /// * `text` - The argument as the caller passed it.
    ///
    /// # Errors
    ///
    /// When the text is neither an address nor a known name, naming the
    /// names nearest it.
    fn addr(&self, p: &Program, text: &str) -> Result<u64, String> {
        borer_engine::answer::address(p, text, || (self.analysis_or_empty(), self.overlay()))
    }

    /// Resolves an argument to the entry of the discovered function
    /// containing it.
    ///
    /// # Arguments
    ///
    /// * `p` - The program held.
    /// * `a` - Its analysis.
    /// * `text` - Address or name ([`HeldExt::addr`]).
    ///
    /// # Errors
    ///
    /// When the text does not resolve or no function contains the address.
    fn function_entry(&self, p: &Program, a: &Analysis, text: &str) -> Result<u64, String> {
        let va = self.addr(p, text)?;
        borer_engine::answer::entry_of(p, a, va, text)
    }

    /// Answers a request about managed code with the program and its
    /// analysis, or an empty one when the machine has no native discovery:
    /// .NET metadata and IL read the same on any machine.
    ///
    /// # Arguments
    ///
    /// * `f` - The answer.
    ///
    /// # Errors
    ///
    /// When nothing is loaded, or `f`'s error.
    fn with_managed(
        &self,
        f: impl FnOnce(&Program, &Analysis) -> Result<String, String>,
    ) -> Result<String, Failure> {
        self.run(Box::new(|p| f(p, &self.analysis_or_empty())))
    }

    /// Answers through [`HeldExt::with_managed`] with what `pick` read off
    /// the program loaded now, refusing when another binary was loaded
    /// between the pick and the answer, so no token meets another file.
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
    ) -> Option<Result<String, Failure>> {
        let picked_from = self.loaded()?;
        let picked = pick(&picked_from)?;
        Some(self.with_managed(|p, a| {
            if !std::ptr::eq(p, Arc::as_ptr(&picked_from)) {
                return Err("another binary was loaded during the request; ask again".to_owned());
            }
            f(p, a, picked)
        }))
    }

    /// Answers a request naming .NET members ([`managed::named`]) through
    /// [`HeldExt::with_managed`].
    ///
    /// # Arguments
    ///
    /// * `text` - The argument as the caller passed it.
    /// * `f` - The answer for the tokens it names.
    ///
    /// # Returns
    ///
    /// The answer, `None` when the argument names no managed code and the
    /// caller answers it natively.
    fn managed_answer(
        &self,
        text: &str,
        f: impl FnOnce(&Program, &Analysis, &BTreeSet<u32>) -> Result<String, String>,
    ) -> Option<Result<String, Failure>> {
        self.managed_pick(
            |p| {
                p.clr()?;
                managed::named(p, text, self.addr(p, text).ok())
            },
            |p, a, targets| f(p, a, &targets),
        )
    }

    /// Answers a request naming an IL method ([`managed::il_method_named`])
    /// through [`HeldExt::with_managed`].
    ///
    /// # Arguments
    ///
    /// * `text` - The argument as the caller passed it.
    /// * `f` - The answer for the method's token.
    ///
    /// # Returns
    ///
    /// The answer, `None` when the argument names no IL method and the
    /// caller answers it natively.
    fn il_answer(
        &self,
        text: &str,
        f: impl FnOnce(&Program, &Analysis, u32) -> Result<String, String>,
    ) -> Option<Result<String, Failure>> {
        self.managed_pick(
            |p| {
                p.clr()?;
                managed::il_method_named(p, text, self.addr(p, text).ok())
            },
            f,
        )
    }
}

impl<H: Held + ?Sized> HeldExt for H {}
