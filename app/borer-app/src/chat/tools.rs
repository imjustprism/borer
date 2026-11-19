//! The chat's tools: the catalog's rows an MCP agent calls ([`TOOLS`]).
//!
//! They run over the open binary through the catalog's own execution; an edit row asked to
//! apply leaves its plan waiting as a proposal for the person.
//!
//! The face the catalog reads ([`Face`]) is the catalog's plain one ([`Loaded`]) over the
//! open binary's snapshot, so a tool answers here the bytes it answers an MCP agent and
//! `query` refuses a resource only the server has by name, with why; its edits go through
//! the catalog's plan-keeping face ([`Keeping`]), which the person's inline editor plans
//! through too: it refuses a name a person could not read whole, keeps the plan for the
//! proposal card and commits nothing.

use std::sync::{Arc, LazyLock};

use borer_engine::analysis::Overlay;
use borer_engine::analysis::edit::{Edit, Force, Plan};
use borer_engine::answer::{Need, catalog};
use borer_engine::program::FileShown;
use borer_engine::text::one_line;
use borer_front::tools::{self, Apply, Failure, Held, Keeping, Loaded, TOOLS, View};
use serde_json::{Map, Value};

use crate::worker::LoadedBinary;

/// A plan the model's edit tool asked to apply, with the edits it plans and whether it takes
/// a name another address holds, kept for the person.
pub type Proposed = (Vec<Edit>, Force, Plan);

/// What the catalog reads through in the chat: the open binary's program, analysis and
/// names as one snapshot, its paths named by the file alone.
struct Face {
    /// The catalog's plain face over the open binary.
    plain: Loaded,
}

impl Held for Face {
    fn view(&self, need: Need) -> Option<Result<View, String>> {
        self.plain.view(need)
    }

    fn user_overlay(&self) -> Arc<Overlay> {
        Arc::new(Overlay {
            file_shown: FileShown::Name,
            ..Overlay::clone(&self.plain.overlay)
        })
    }

    fn querier(&self) -> borer_engine::script::Query {
        self.plain.querier()
    }

    fn read(&self, uri: &str) -> Result<String, Failure> {
        let asked = borer_engine::answer::Suffixed::read(uri).map_err(Failure::asked)?;
        if asked.core == "borer://help" {
            return Ok(help());
        }
        tools::ask(self, uri)
    }
}

/// Returns `borer://help` as the chat answers it, from the engine's resource catalog.
///
/// Each row of [`catalog::RESOURCES`] and [`catalog::RESOURCE_TEMPLATES`] the engine
/// answers ([`borer_engine::answer::names`]) is listed with what it answers, in the
/// catalog's order.
fn help() -> String {
    let answered: std::collections::BTreeSet<&str> = borer_engine::answer::names().collect();
    let fixed = catalog::RESOURCES.iter().map(|(uri, said)| (*uri, *said));
    let templates = catalog::RESOURCE_TEMPLATES
        .iter()
        .map(|(uri, said, _)| (*uri, *said));
    let rows: Vec<String> = fixed
        .chain(templates)
        .filter(|(uri, _)| answered.contains(catalog::resource_name(uri)))
        .map(|(uri, said)| format!("{uri}\t{said}"))
        .collect();
    format!(
        "# {} resources query answers here: read one by its URI, with its argument where it takes one; one read without the argument it needs says what it takes\n{}\n",
        rows.len(),
        rows.join("\n")
    )
}

/// The tool definitions every request sends, built once from [`TOOLS`].
pub static DEFINITIONS: LazyLock<Vec<language_model::LanguageModelRequestTool>> =
    LazyLock::new(|| {
        TOOLS
            .iter()
            .map(|t| {
                language_model::LanguageModelRequestTool::function(
                    t.name.to_owned(),
                    t.description.to_owned(),
                    Value::Object(t.input_schema()),
                    false,
                )
            })
            .collect()
    });

/// Answers the model's call of tool `name` with `args` over `loaded`, as the MCP server
/// answers it.
///
/// Where an answer prints the open file's path it names the file alone
/// ([`FileShown::Name`]), so no folder of the person's disk reaches a provider.
///
/// A tool only the MCP server runs is refused by name with why
/// ([`borer_front::tools::server_only`]).
///
/// Must be called inside [`crate::worker::spawn_engine`].
///
/// # Arguments
///
/// * `loaded` - The open binary.
/// * `name` - The tool the model called.
/// * `args` - Its arguments: an object, or null for none.
///
/// # Returns
///
/// The answer or the refusal, and the plan an edit tool made, which waits for the person.
pub fn answer(
    loaded: &LoadedBinary,
    name: &str,
    args: Value,
) -> (Result<String, String>, Option<Proposed>) {
    let face = Face {
        plain: Loaded {
            program: Arc::clone(&loaded.program),
            analysis: Arc::clone(&loaded.analysis),
            overlay: Arc::clone(&loaded.overlay),
        },
    };
    let keeping = Keeping::new(&face);
    let args = match args {
        Value::Object(args) => Some(args),
        Value::Null => Some(Map::new()),
        _ => None,
    };
    let answered = match (tools::tool(name), args) {
        (Some(t), Some(args)) => (t.run)(&keeping, args).map_err(|f| f.message),
        (Some(t), None) => Err(format!("the arguments of {} are not a JSON object", t.name)),
        (None, _) => Err(tools::server_only(name).map_or_else(
            || format!("no tool is named {}", one_line(name)),
            |refused| format!("{}{}", refused.message, instead(name)),
        )),
    };
    let proposed = keeping
        .into_kept()
        .and_then(|kept| match (kept.apply, kept.planned) {
            (Apply::Commit, Ok(plan)) => Some((kept.edits, kept.force, plan)),
            (Apply::Commit | Apply::Preview, _) => None,
        });
    (answered, proposed)
}

/// Returns what the person can do in borer-app in place of a server-only tool the model
/// called, as a clause to end its refusal; empty where the app offers nothing in its place.
///
/// # Arguments
///
/// * `name` - The tool the model called.
pub(super) fn instead(name: &str) -> &'static str {
    match name {
        "load_binary" | "load_project" | "reload" => {
            "; here the person opens a file in borer-app (Open in the command palette): ask them to, and the chat reads the binary they open"
        }
        "save_project" => "; ask the person to save the project in borer-app",
        _ => "",
    }
}
