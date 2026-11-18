//! Resources read through what a front end holds: the engine's answers
//! ([`read_engine`]), the plainest front end ([`Loaded`]) and the `query`
//! answer of a face without the MCP server's session ([`ask`]).

use std::num::NonZeroUsize;
use std::sync::Arc;

use borer_engine::analysis::{Analysis, Overlay};
use borer_engine::answer::{self, Need, Page};
use borer_engine::program::Program;

use super::{Cause, Failure, Held, View, run, tabled};

/// The resources only the MCP server answers, each with why.
pub const SERVER_RESOURCES: &[(&str, &str)] = &[
    ("anchors", "it loads another file from disk"),
    ("bench", "it times the MCP server"),
    ("carry", "it loads another file from disk"),
    ("changes", "it loads another file from disk"),
    ("diff", "it loads another file from disk"),
    ("difffn", "it loads another file from disk"),
    ("find", "the MCP server answers it until the engine does"),
    ("grep", "it reads the code index cached on disk"),
    ("help", "the resource list is the MCP server's"),
    ("index", "it reads the code index cached on disk"),
    ("info", "it lists the MCP server's resources"),
    ("migrate", "it loads another file from disk"),
    ("packs", "it reads the pack files on disk"),
    ("playbook", "the playbooks are the MCP server's prompts"),
    ("script", "it runs a script file from disk"),
    (
        "session",
        "the session ledger and its evidence are the MCP server's",
    ),
    ("stats", "the MCP server answers it until the engine does"),
];

/// Answers a resource the engine answers, through what a front end holds.
///
/// The view is what the resource's [`Need`] asks; a decompile's function is
/// found or recovered through the face that keeps it
/// ([`super::Snapshot::decompile_entry`]); the ledger answers before a load,
/// from the names alone. A page asked of a listing the engine pages is
/// the engine's.
///
/// # Arguments
///
/// * `h` - What the front end holds.
/// * `core` - The URI without its suffixes.
/// * `page` - The page asked.
///
/// # Returns
///
/// The answer, `None` when the engine does not answer the URI.
#[must_use]
pub fn read_engine(h: &dyn Held, core: &str, page: Page<'_>) -> Option<Result<String, Failure>> {
    let (name, arg) = answer::split(core)?;
    let need = match answer::need(name, arg.as_deref())? {
        Ok(need) => need,
        Err(why) => return Some(Err(Failure::asked(why))),
    };
    if name == "annotations" && h.view(Need::File).is_none() {
        let text = answer::annotations(&tabled(&h.user_overlay()));
        return Some(Ok(paged(&text, page)));
    }
    Some(run(h, need, |s| {
        let grown = match (name, arg.as_deref()) {
            ("decompile", Some(text)) => s.decompile_entry(text).ok().map(|(a, _)| a),
            _ => None,
        };
        let analysis = grown.as_deref().or_else(|| s.kept());
        answer::read(s.program(), analysis, s.overlay(), core, page).unwrap_or_else(|| {
            Err(format!(
                "the engine does not answer {}",
                borer_engine::text::one_line(core)
            ))
        })
    }))
}

/// Returns the page asked of a listing's rows, the whole when none was.
///
/// # Arguments
///
/// * `text` - The listing.
/// * `page` - The page asked.
fn paged(text: &str, page: Page<'_>) -> String {
    if !page.paged() {
        return text.to_owned();
    }
    borer_engine::table::page(
        text,
        page.offset.unwrap_or(0),
        page.limit.map_or(usize::MAX, NonZeroUsize::get),
        page.again,
    )
}

/// Answers a resource URI as a face without the MCP server's session reads it.
///
/// The page suffixes are read as the server reads them; what the engine
/// answers is answered ([`read_engine`]); a resource only the server
/// answers is refused by name with the reason ([`SERVER_RESOURCES`]).
///
/// # Arguments
///
/// * `h` - What the front end holds.
/// * `uri` - The URI as the caller wrote it.
///
/// # Errors
///
/// When a suffix does not read, the resource refuses, the server alone
/// answers it, or no resource has the name.
pub fn ask(h: &dyn Held, uri: &str) -> Result<String, Failure> {
    let asked = answer::Suffixed::read(uri).map_err(Failure::asked)?;
    let again = asked.again();
    if let Some(answered) = read_engine(h, asked.core, asked.page(&again)) {
        return answered;
    }
    let shown = borer_engine::text::one_line(asked.core);
    let name = answer::split(asked.core).map_or("", |(name, _)| name);
    if let Some((_, why)) = SERVER_RESOURCES.iter().find(|(n, _)| *n == name) {
        return Err(Failure::asked(format!(
            "{shown} is not answered here: {why}"
        )));
    }
    if answer::names().any(|n| n == name) {
        return Err(Failure::asked(format!(
            "{shown} is not answered here: name borer://{name} with an argument, or without one, as the resource takes it"
        )));
    }
    Err(Failure {
        cause: Cause::Missing,
        message: format!("unknown resource {shown}"),
    })
}

/// A program held with its analysis and names, as one value: the plainest
/// front end, a snapshot nothing changes while a tool reads it.
#[derive(Debug, Clone)]
pub struct Loaded {
    /// The program.
    pub program: Arc<Program>,
    /// Its analysis, an empty one where its architecture has none.
    pub analysis: Arc<Analysis>,
    /// The names, comments and types as the user left them.
    pub overlay: Overlay,
}

impl Held for Loaded {
    fn view(&self, need: Need) -> Option<Result<View, String>> {
        let analysis = match need {
            Need::Code(stage) | Need::Best(stage) if self.program.refuses(stage).is_none() => {
                Some(Arc::clone(&self.analysis))
            }
            Need::Code(_) => None,
            Need::Best(_) => Some(Arc::default()),
            Need::File => Some(Arc::clone(&self.analysis)),
        };
        Some(Ok(View {
            program: Arc::clone(&self.program),
            analysis,
        }))
    }

    fn user_overlay(&self) -> Overlay {
        self.overlay.clone()
    }

    fn read(&self, uri: &str) -> Result<String, Failure> {
        ask(self, uri)
    }
}
