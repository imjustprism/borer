//! borer MCP server: exposes the analysis engine over stdio JSON-RPC.
//!
//! The server layer stays thin on purpose: everything interesting lives in
//! `borer-engine` (sync, pure, testable). Tool outputs are plain text with
//! server-side filtering, hard caps, and a showing-N-of-M header on any
//! list-shaped result. With command-line arguments the same binary runs
//! one-shot CLI commands ([`cli`]); without them it is the relay that keeps
//! the client's pipes and runs the server as a worker process ([`relay`]).
//!
//! This file holds the server type, the tool router (the sum of the
//! per-area routers in [`tools`]) and the resource dispatch. The state and
//! its locks are in [`state`], the parameter types in [`params`], the
//! prompts in [`prompts`], the resource catalog in [`catalog`], the
//! `borer://` handlers in [`resources`], and the answer memory and byte
//! budget every reply passes through in [`recall`].

/// The allocator the shipped binary uses.
///
/// Analysis and decompilation are allocation-bound: an expression tree is
/// boxed per node and a function's dataflow builds a map per instruction.
/// The Windows system allocator serializes more of that than mimalloc does,
/// and the choice is global to a binary, so it belongs here rather than in
/// the engine, which stays free of it and wasm-buildable.
#[global_allocator]
static ALLOCATOR: mimalloc::MiMalloc = mimalloc::MiMalloc;

mod catalog;
mod cli;
mod doctor;
mod errors;
mod handover;
mod paging;
mod params;
mod playbooks;
mod prompts;
mod recall;
mod relay;
mod resources;
mod session;
mod setup;
mod state;
mod strwalk;
mod symsrv;
mod term;
#[cfg(test)]
mod testing;
mod tools;
mod update;

use std::path::PathBuf;
use std::sync::{Arc, Mutex, RwLock};

use borer_engine::analysis::{Analysis, Overlay};
use borer_engine::pack::Packs;
use borer_engine::program::Program;
use rmcp::handler::server::router::tool::ToolRouter;
use rmcp::handler::server::wrapper::Parameters;
use rmcp::model::{
    CacheScope, CallToolRequestParams, CallToolResponse, CompleteRequestParams, CompleteResult,
    CompletionInfo, ContentBlock, CustomRequest, CustomResult, ErrorCode,
    ListResourceTemplatesResult, ListResourcesResult, ListToolsResult, PaginatedRequestParams,
    ProtocolVersion, ReadResourceRequestParams, ReadResourceResponse, ReadResourceResult,
    Reference, Resource, ResourceContents, ResourceTemplate, ResultType, Tool,
};
use rmcp::service::RequestContext;
use rmcp::{ErrorData, RoleServer, ServerHandler, ServiceExt, prompt_handler, tool_handler};

use crate::catalog::{RESOURCE_TEMPLATES, RESOURCES, TEXT_PLAIN, resource_name};
use crate::errors::{err_internal, err_params};
use crate::handover::{HandOver, HandOverTransport, Resume, end_quietly_when_stdout_closes};
use crate::paging::percent_decode;
use crate::params::{
    AnnotationsParams, DecompileParams, DisassembleFunctionParams, FunctionParams,
};
use crate::recall::{Narrow, Recall, SINCE_ARG, Tag, budgeted};
use crate::session::{EVIDENCE_URI, SESSION_URI};
use crate::state::{RawLoad, lock, read_lock};
use crate::tools::live::LiveSession;

/// The MCP server state: one loaded program, its lazily computed analysis,
/// and the annotation overlay.
///
/// Every field is shared behind a lock because rmcp clones the handler per
/// request; a poisoned lock is recovered rather than propagated
/// ([`read_lock`]). The default is a server with nothing loaded and no
/// packs.
#[derive(Debug, Clone, Default)]
struct BorerServer {
    /// What this session was last answered for each request, so an
    /// identical answer repeated is a one-line note, not the text again.
    recall: Arc<Mutex<Recall>>,
    /// What this session changed and asked, for `borer://session`.
    ledger: Arc<Mutex<session::Ledger>>,
    /// The loaded program, `None` before `load_binary`.
    program: Arc<RwLock<Option<Arc<Program>>>>,
    /// Whether the loaded program's companion PDB was applied: a
    /// comparison build loads the same way, or a diff of a binary against
    /// itself pairs functions a PDB names with ones it does not.
    pdb_applied: Arc<RwLock<bool>>,
    /// The `entry_file_offset` the loaded program was loaded with, so a
    /// reload loads it the same way.
    entry_file_offset: Arc<RwLock<Option<u64>>>,
    /// The raw layout the loaded program was mapped by, so a reload maps
    /// it the same way.
    raw_load: Arc<RwLock<RawLoad>>,
    /// Derived analysis of `program`, computed on first use and reset by `load_binary`.
    analysis: Arc<RwLock<Option<Arc<Analysis>>>>,
    /// The loaded program's string walks, computed on the first `strings`
    /// call and reset by `load_binary`; see [`strwalk`].
    strings: Arc<RwLock<Option<Arc<strwalk::StringWalks>>>>,
    /// User names and comments.
    overlay: Arc<RwLock<Overlay>>,
    /// The packs the user named in `BORER_PACKS`, read at start; every
    /// analysis runs with them.
    packs: Arc<Packs>,
    /// The packs the loaded program's analysis runs with: the pack
    /// directories' packs that fit it, then `packs`; set by `load_binary`.
    program_packs: Arc<RwLock<Arc<Packs>>>,
    /// The process attached for reading, `None` until `live_attach`.
    live: Arc<Mutex<Option<LiveSession>>>,
    /// The hand-over to the next worker: asked for by `reload`, carried out
    /// by the transport once the reload reply and every earlier one are
    /// written.
    hand_over: Arc<HandOver>,
}

impl BorerServer {
    /// Returns every tool the server answers, one router per area
    /// ([`tools`]).
    ///
    /// The live tools read another process through the Windows API, so
    /// off Windows they are left out rather than listed and always refused.
    fn tool_router() -> ToolRouter<Self> {
        let live = if cfg!(windows) {
            Self::live_tools()
        } else {
            ToolRouter::new()
        };
        Self::load_tools()
            + Self::bytes_tools()
            + Self::search_tools()
            + Self::function_tools()
            + Self::decompile_tools()
            + Self::annotate_tools()
            + live
            + Self::query_tools()
    }
}

#[tool_handler]
#[prompt_handler]
impl ServerHandler for BorerServer {
    /// Returns capabilities (tools, prompts, resources, completions), the
    /// implementation name and version, and the agent-facing instructions,
    /// built from the routers and the resource tables
    /// ([`playbooks::instructions`]).
    fn get_info(&self) -> rmcp::model::ServerInfo {
        let tools: Vec<String> = Self::tool_router()
            .list_all()
            .into_iter()
            .map(|t| t.name.into_owned())
            .collect();
        rmcp::model::ServerInfo::new(
            rmcp::model::ServerCapabilities::builder()
                .enable_tools()
                .enable_prompts()
                .enable_resources()
                .enable_completions()
                .build(),
        )
        .with_server_info(rmcp::model::Implementation::new(
            "borer",
            env!("CARGO_PKG_VERSION"),
        ))
        .with_instructions(playbooks::instructions(
            &tools,
            &Self::prompt_router().list_all(),
        ))
    }

    /// Runs a tool, then passes its text through the session's answer
    /// memory, the byte budget and the evidence line.
    ///
    /// Any tool takes a `since` argument the schemas leave out (every tool
    /// would pay for it in the tool list): the tag of the answer the reader
    /// holds, taken off here before the tool parses its arguments
    /// ([`recall::Recall`]); `"since": null` is no tag, as null is no value
    /// for every other parameter. A `reload` call schedules the hand-over whatever
    /// it answers: the relay holds the client's lines from that call on
    /// until this worker has ended, so a worker that stayed would hold them
    /// for good. A `query` answer has been through both already, keyed by
    /// its URI as a resource read is ([`BorerServer::read_uri`]), so its tag
    /// goes on the URI, where a URI's own tag goes ([`recall::tagged_uri`]).
    /// An argument the parser refuses is named in the
    /// message, from the tool's schema ([`params::misfit`]): serde words
    /// the value alone.
    ///
    /// # Arguments
    ///
    /// * `request` - The tool and its arguments.
    /// * `context` - Request context.
    ///
    /// A tool that runs and fails answers with `isError` set and its
    /// message as the text ([`errors::tool_failure`]), so the agent reads
    /// it; only a request the server cannot run is a protocol error.
    ///
    /// # Errors
    ///
    /// When the tool is unknown or `since` is not a tag.
    async fn call_tool(
        &self,
        mut request: CallToolRequestParams,
        context: RequestContext<RoleServer>,
    ) -> Result<CallToolResponse, ErrorData> {
        let since = request
            .arguments
            .as_mut()
            .and_then(|a| a.remove(SINCE_ARG))
            .and_then(|v| match v {
                serde_json::Value::Null => None,
                serde_json::Value::String(s) => Some(Tag::parse(&s)),
                other => Some(Tag::parse(&other.to_string())),
            })
            .transpose()
            .map_err(err_params)?;
        if let Some(tag) = since
            && request.name == "query"
            && let Some(serde_json::Value::String(uri)) =
                request.arguments.as_mut().and_then(|a| a.get_mut("uri"))
        {
            *uri = recall::tagged_uri(uri, tag);
        }
        let args = request
            .arguments
            .as_ref()
            .map(|a| serde_json::to_string(a).unwrap_or_default())
            .unwrap_or_default();
        let key = format!("tool:{}:{args}", request.name);
        let again = format!(
            "calling {}",
            borer_engine::text::one_line(format!("{} {args}", request.name).trim_end())
        );
        let remembered = request.name != "query";
        let reloading = request.name == "reload";
        let peer_info = context.peer.peer_info();
        let named = (request.name.clone(), request.arguments.clone());
        let known = Self::tool_router().has_route(&request.name);
        let call = rmcp::handler::server::tool::ToolCallContext::new(self, request, context);
        let response = Self::tool_router().call(call).await;
        if reloading {
            self.hand_over.schedule(Resume {
                peer_info: peer_info.as_deref().cloned(),
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
            });
        }
        let response = match response {
            Ok(response) => response,
            Err(error) => errors::tool_failure(known, error)?,
        };
        Ok(match response {
            CallToolResponse::Complete(mut result)
                if remembered && result.is_error != Some(true) =>
            {
                self.note_change(&named.0, named.1.as_ref(), &args);
                if let [ContentBlock::Text(t)] = result.content.as_mut_slice() {
                    let full = std::mem::take(&mut t.text);
                    let paged = named
                        .1
                        .as_ref()
                        .is_some_and(|a| a.contains_key("offset") || a.contains_key("limit"));
                    lock(&self.ledger).answered(
                        &key,
                        session::shows_fewer(&full) || recall::over_budget(full.len()),
                        paged,
                    );
                    let sent = match self.recall.lock() {
                        Ok(mut recall) => recall.answer(&key, since, &again, full),
                        Err(_) => full,
                    };
                    t.text = self.evidence(budgeted(sent, Narrow::Tool));
                }
                CallToolResponse::Complete(result)
            }
            CallToolResponse::Complete(mut result) if result.is_error == Some(true) => {
                if let [ContentBlock::Text(t)] = result.content.as_mut_slice()
                    && let Some(rest) = t.text.strip_prefix(params::DESERIALIZE_PREFIX)
                    && let (name, Some(args)) = &named
                    && let Some(field) = Self::tool_router()
                        .get(name)
                        .and_then(|tool| params::misfit(&tool.input_schema, args))
                {
                    t.text = format!("{} field `{field}`:{rest}", params::DESERIALIZE_PREFIX);
                }
                CallToolResponse::Complete(result)
            }
            other => other,
        })
    }

    /// Lists the tools with slimmed schemas.
    ///
    /// The list never changes while the server runs, so clients speaking
    /// protocol 2026-07-28 or newer get a one-hour public cache hint.
    ///
    /// # Arguments
    ///
    /// * `_request` - Paging (unused; the list is complete).
    /// * `context` - Request context carrying the negotiated protocol version.
    ///
    /// # Errors
    ///
    /// Never.
    async fn list_tools(
        &self,
        _request: Option<PaginatedRequestParams>,
        context: RequestContext<RoleServer>,
    ) -> Result<ListToolsResult, ErrorData> {
        let cache = context
            .protocol_version()
            .is_some_and(|v| v >= ProtocolVersion::V_2026_07_28);
        Ok(ListToolsResult {
            result_type: Some(ResultType::COMPLETE),
            tools: Self::tool_router()
                .list_all()
                .into_iter()
                .map(slim_tool)
                .collect(),
            meta: None,
            next_cursor: None,
            ttl_ms: cache.then_some(3_600_000),
            cache_scope: cache.then_some(CacheScope::Public),
        })
    }

    /// Returns one tool with its slimmed schema.
    ///
    /// # Arguments
    ///
    /// * `name` - Tool name.
    fn get_tool(&self, name: &str) -> Option<Tool> {
        Self::tool_router().get(name).cloned().map(slim_tool)
    }

    /// Lists the fixed resources (`borer://info`, `borer://annotations`,
    /// `borer://enums`).
    ///
    /// # Arguments
    ///
    /// * `_request` - Paging (unused).
    /// * `_context` - Request context (unused).
    ///
    /// # Errors
    ///
    /// Never.
    async fn list_resources(
        &self,
        _request: Option<PaginatedRequestParams>,
        _context: RequestContext<RoleServer>,
    ) -> Result<ListResourcesResult, ErrorData> {
        Ok(ListResourcesResult::with_all_items(
            RESOURCES
                .iter()
                .map(|&(uri, description)| {
                    Resource::new(uri, resource_name(uri))
                        .with_description(description)
                        .with_mime_type(TEXT_PLAIN)
                })
                .collect(),
        ))
    }

    /// Lists the per-function resource templates (function, decompile, disasm).
    ///
    /// # Arguments
    ///
    /// * `_request` - Paging (unused).
    /// * `_context` - Request context (unused).
    ///
    /// # Errors
    ///
    /// Never.
    async fn list_resource_templates(
        &self,
        _request: Option<PaginatedRequestParams>,
        _context: RequestContext<RoleServer>,
    ) -> Result<ListResourceTemplatesResult, ErrorData> {
        Ok(ListResourceTemplatesResult::with_all_items(
            RESOURCE_TEMPLATES
                .iter()
                .map(|&(uri, description, _)| {
                    ResourceTemplate::new(uri, resource_name(uri))
                        .with_description(description)
                        .with_mime_type(TEXT_PLAIN)
                })
                .collect(),
        ))
    }

    /// Reads a `borer://` resource ([`BorerServer::read_uri`]).
    ///
    /// # Arguments
    ///
    /// * `request` - The resource URI.
    /// * `_context` - Request context (unused).
    ///
    /// # Errors
    ///
    /// Resource-not-found for an unknown URI; otherwise the delegated tool's error.
    async fn read_resource(
        &self,
        request: ReadResourceRequestParams,
        _context: RequestContext<RoleServer>,
    ) -> Result<ReadResourceResponse, ErrorData> {
        let (uri, text) = self.read_uri(&request.uri)?;
        Ok(ReadResourceResult::new(vec![ResourceContents::text(text, uri)]).into())
    }

    /// Completes prompt and resource-template arguments.
    ///
    /// Any `address` or `function` argument (the `{function}` of
    /// `borer://difffn`, `migrate`, `schema`, `encode` and `shape`)
    /// completes to function names; `find_check`'s `what` completes to the
    /// usual validation targets.
    ///
    /// # Arguments
    ///
    /// * `request` - The reference and the partial argument.
    /// * `_context` - Request context (unused).
    ///
    /// # Errors
    ///
    /// Internal error when the completion list exceeds the protocol's limits.
    async fn complete(
        &self,
        request: CompleteRequestParams,
        _context: RequestContext<RoleServer>,
    ) -> Result<CompleteResult, ErrorData> {
        let prefix = request.argument.value.to_lowercase();
        let all: Vec<String> = match (&request.r#ref, request.argument.name.as_str()) {
            (Reference::Prompt(p), "what") if p.name == "find_check" => CHECK_KINDS
                .iter()
                .filter(|k| k.starts_with(&prefix))
                .map(|k| (*k).to_owned())
                .collect(),
            (_, "address" | "function") => self.complete_names(&prefix),
            _ => Vec::new(),
        };
        let total = all.len();
        let values: Vec<String> = all.into_iter().take(CompletionInfo::MAX_VALUES).collect();
        let has_more = total > values.len();
        let mut info = CompletionInfo::new(values).map_err(err_internal)?;
        info.total = Some(u32::try_from(total).unwrap_or(u32::MAX));
        info.has_more = Some(has_more);
        Ok(CompleteResult::new(info))
    }

    /// Answers a request no typed handler took: a method rmcp does not
    /// know, or one it knows whose params do not parse, which it hands
    /// over the same way.
    ///
    /// Both were answered method-not-found, so a `resources/read` sent
    /// without its `uri` read as a server with no resources at all. A
    /// method borer serves is refused as invalid params, with the shape
    /// its params take.
    ///
    /// # Arguments
    ///
    /// * `request` - The method and its params as sent.
    /// * `_context` - Request context (unused).
    ///
    /// # Errors
    ///
    /// Always: invalid params for a method borer serves, method-not-found
    /// for any other.
    async fn on_custom_request(
        &self,
        request: CustomRequest,
        _context: RequestContext<RoleServer>,
    ) -> Result<CustomResult, ErrorData> {
        match PARAMS_SHAPES
            .iter()
            .find(|(method, _)| *method == request.method)
        {
            Some((method, shape)) => Err(err_params(format!(
                "{method} needs params of the form {shape}"
            ))),
            None => Err(ErrorData::new(
                ErrorCode::METHOD_NOT_FOUND,
                request.method,
                None,
            )),
        }
    }
}

/// The methods borer serves that take params, each with the shape they
/// take, for the refusal of one sent without them
/// ([`BorerServer::on_custom_request`]).
const PARAMS_SHAPES: &[(&str, &str)] = &[
    ("resources/read", r#"{"uri": "borer://info"}"#),
    ("tools/call", r#"{"name": "<tool>", "arguments": {...}}"#),
    ("prompts/get", r#"{"name": "<prompt>", "arguments": {...}}"#),
    (
        "completion/complete",
        r#"{"ref": {...}, "argument": {"name": "...", "value": "..."}}"#,
    ),
];

impl BorerServer {
    /// Reads a `borer://` resource: the text its handler answers, through
    /// the session's answer memory, the byte budget and the evidence line.
    ///
    /// `resources/read` and the `query` tool both come here, so a URI is
    /// answered alike either way: the same text, the same errors, and one
    /// answer memory keyed by the URI and the page it asks for. The
    /// argument is percent-decoded: a client is free to escape the reserved
    /// characters an argument uses, and an experiment spec is full of them.
    /// An unknown URI is refused with the few resources nearest it, and
    /// `borer://help` lists every one, which is how an agent whose host
    /// lists no resources finds them. An evidence URI
    /// (`borer://session/evidence/<id>`) skips the memory, the budget's
    /// cut apart, and mints no evidence of its own: the text an id names
    /// comes back exactly as it was sent.
    ///
    /// # Arguments
    ///
    /// * `uri` - The URI as the client sent it, with any suffixes
    ///   ([`paging::Asked`]): `!offset=<n>` and `!limit=<n>` page a
    ///   listing, `!since=<tag>` passes back the tag of the answer the
    ///   reader holds, and `!fresh` asks for the text whole whatever tag
    ///   comes with it.
    ///
    /// # Returns
    ///
    /// The URI with only its page suffixes, and the text to send.
    ///
    /// # Errors
    ///
    /// Resource-not-found for an unknown URI; invalid-params for a suffix
    /// that does not read; otherwise the handler's error.
    pub(crate) fn read_uri(&self, uri: &str) -> Result<(String, String), ErrorData> {
        let asked = paging::Asked::read(uri).map_err(err_params)?;
        let text = self.listing(&asked)?;
        let key = asked.key();
        if asked.core.starts_with(EVIDENCE_URI) {
            return Ok((key, budgeted(text, Narrow::Uri)));
        }
        if asked.core != SESSION_URI {
            lock(&self.ledger).answered(
                &key,
                session::shows_fewer(&text) || recall::over_budget(text.len()),
                asked.paged(),
            );
        }
        let again = format!("reading {key} (resources/read or the query tool)");
        let text = match self.recall.lock() {
            Ok(mut recall) => recall.answer(&key, asked.since, &again, text),
            Err(_) => text,
        };
        Ok((key, self.evidence(budgeted(text, Narrow::Uri))))
    }

    /// The text of one resource, as its handler answers it: no answer
    /// memory, no byte budget, no suffix; what the tests read.
    ///
    /// # Arguments
    ///
    /// * `uri` - The URI, suffixes already taken off.
    ///
    /// # Errors
    ///
    /// As [`BorerServer::listing`].
    #[cfg(test)]
    pub(crate) fn resource_text(&self, uri: &str) -> Result<String, ErrorData> {
        self.listing(&paging::Asked::whole(uri))
    }

    /// The text of one resource, paged as its URI asks: no answer memory
    /// and no byte budget.
    ///
    /// [`BorerServer::read_uri`] wraps it for `resources/read` and the
    /// `query` tool, and a script's `query(uri)` calls it directly
    /// ([`BorerServer::script`]). A listing that pages itself
    /// (`attrs`, `messages`, `fieldrefs`, `grep`, `iocs`, `calls`, `clr`) is
    /// handed the page; any other answer's rows are paged here
    /// ([`borer_engine::table::page`]), under a `# showing N of M from K`
    /// line and over the URI that reads the next page.
    ///
    /// A template named without its argument (`borer://emulate`) answers
    /// how to read it ([`BorerServer::help_text`]).
    ///
    /// # Arguments
    ///
    /// * `asked` - The URI with its suffixes read off.
    ///
    /// # Errors
    ///
    /// Resource-not-found for an unknown URI, naming the resources nearest
    /// it ([`resources::unknown_resource`]); otherwise the handler's error.
    pub(crate) fn listing(&self, asked: &paging::Asked) -> Result<String, ErrorData> {
        let uri = asked.core.as_str();
        let Some(path) = uri.strip_prefix("borer://") else {
            return Err(resources::unknown_resource(uri));
        };
        let (kind, arg) = match path.split_once('/') {
            Some((k, a)) => (k, Some(percent_decode(a))),
            None => (path, None),
        };
        let text = match (kind, arg) {
            ("info", None) => self.binary_info()?,
            ("annotations", None) => self.annotations(Parameters(AnnotationsParams::default()))?,
            ("enums", None) => self.enums_text()?,
            ("dynimports", None) => self.dynamic_imports_text()?,
            ("checks", None) => self.checks_text()?,
            ("antianalysis", None) => self.anti_analysis_text()?,
            ("protection", None) => self.protection_text()?,
            ("iocs", None) => return self.iocs_text(&asked.spec_words("")),
            ("iocs", Some(filter)) => return self.iocs_text(&asked.spec_words(&filter)),
            ("calls", Some(spec)) => return self.calls_text(&asked.spec_words(&spec)),
            ("triage", None) => self.triage_text()?,
            ("fingerprint", None) => self.fingerprint_text()?,
            ("hashes", None) => self.hashes_text()?,
            ("children", None) => self.children_text()?,
            ("capabilities", None) => self.capabilities_text()?,
            ("qt", None) => self.qt_text()?,
            ("objc", None) => return self.objc_text("", asked),
            ("objc", Some(filter)) => return self.objc_text(&filter, asked),
            ("clr", None) => return self.clr_text(&asked.spec_words("")),
            ("clr", Some(filter)) => return self.clr_text(&asked.spec_words(&filter)),
            ("stackstrings", None) => self.stack_strings_text("")?,
            ("stackstrings", Some(filter)) => self.stack_strings_text(&filter)?,
            ("emulate", Some(address)) => self.emulate_text(&address)?,
            ("taint", Some(spec)) => self.taint_text(&spec)?,
            ("layout", Some(spec)) => self.layout_text(&spec)?,
            ("why", Some(target)) => self.why_text(&target)?,
            ("solve", Some(spec)) => self.solve_text(&spec)?,
            ("partial", Some(address)) => self.partial_text(&address)?,
            ("flat", None) => self.flattening_text("")?,
            ("flat", Some(filter)) => self.flattening_text(&filter)?,
            ("devirt", Some(address)) => self.devirtualize_text(&address)?,
            ("unpack", Some(address)) => self.unpack_text(&address)?,
            ("hidden", None) => self.hidden_text("")?,
            ("hidden", Some(filter)) => self.hidden_text(&filter)?,
            ("decoded", None) => return self.decoded_text(&asked.spec_words("")),
            ("decoded", Some(filter)) => return self.decoded_text(&asked.spec_words(&filter)),
            ("oracle", Some(address)) => self.oracle_text(&address)?,
            ("run", Some(spec)) => self.run_text(&spec)?,
            ("diverge", Some(spec)) => self.diverge_text(&spec)?,
            ("vectors", Some(spec)) => self.vectors_text(&spec)?,
            ("diff", Some(other)) => self.diff_text(&other)?,
            ("difffn", Some(spec)) => self.diff_function_text(&spec)?,
            ("migrate", Some(spec)) => self.migrate_text(&spec)?,
            ("carry", Some(path)) => self.carry_text(&path)?,
            ("vm", None) => self.vm_text("")?,
            ("vm", Some(address)) => self.vm_text(&address)?,
            ("asserts", None) => self.asserts_text("")?,
            ("asserts", Some(filter)) => self.asserts_text(&filter)?,
            ("sources", None) => self.sources_text("")?,
            ("sources", Some(filter)) => self.sources_text(&filter)?,
            ("classes", None) => self.classes_text("")?,
            ("classes", Some(filter)) => self.classes_text(&filter)?,
            ("singletons", None) => self.singletons_text("")?,
            ("singletons", Some(filter)) => self.singletons_text(&filter)?,
            ("fields", Some(address)) => self.fields_text(&address)?,
            ("fieldrefs", Some(spec)) => return self.fieldrefs_text(&spec, asked),
            ("vslot", Some(spec)) => self.vslot_text(&spec)?,
            ("grep", Some(text)) => return self.grep_text(&text, asked),
            ("packs", None) => self.packs_text()?,
            ("exportpack", Some(spec)) => self.export_pack_text(&spec)?,
            ("script", Some(path)) => self.script_text(&path)?,
            ("scenario", Some(spec)) => self.scenario_text(&spec)?,
            ("scenarios", Some(spec)) => self.scenarios_text(&spec)?,
            ("index", None) => self.index_text()?,
            ("bench", None) => self.bench_text()?,
            ("schema", Some(what)) => self.schema_text(&what)?,
            ("schemas", Some(spec)) => self.schemas_text(&spec)?,
            ("encode", Some(what)) => self.encode_text(&what)?,
            ("encodes", Some(spec)) => self.encodes_text(&spec)?,
            ("senders", Some(spec)) => self.senders_text(&spec)?,
            ("protocol", Some(spec)) => self.protocol_text(&spec)?,
            ("hooks", Some(spec)) => self.hooks_text(&spec)?,
            ("shape", Some(address)) => self.shape_text(&address)?,
            ("messages", None) => return self.messages_text("", asked),
            ("attrs", None) => return self.attrs_text("", asked),
            ("map", None) => self.map_text("")?,
            ("about", Some(name)) => self.about_text(&name)?,
            ("changes", Some(path)) => self.changes_text(&path)?,
            ("map", Some(namespace)) => self.map_text(&namespace)?,
            ("ports", None) => self.ports_text("")?,
            ("ports", Some(filter)) => self.ports_text(&filter)?,
            ("attrs", Some(filter)) => return self.attrs_text(&filter, asked),
            ("messages", Some(filter)) => return self.messages_text(&filter, asked),
            ("anchors", Some(path)) => self.anchors_text(&path)?,
            ("function", Some(address)) => {
                self.function_summary(Parameters(FunctionParams { address }))?
            }
            ("decompile", Some(address)) => self.decompile(Parameters(DecompileParams {
                address,
                detail: None,
                filter: None,
                offset: None,
                limit: None,
            }))?,
            ("disasm", Some(address)) => {
                self.disassemble_function(Parameters(DisassembleFunctionParams {
                    address,
                    max_instrs: None,
                    bytes: None,
                }))?
            }
            ("playbook", Some(spec)) => resources::playbook_text(&spec)?,
            ("help", None) => resources::help_index(self.loaded().as_deref()),
            ("session", None) => self.session_text(),
            ("session", Some(spec)) => return self.session_evidence(&spec),
            ("help", Some(name)) => self.help_text(&name)?,
            (name, None)
                if RESOURCE_TEMPLATES
                    .iter()
                    .any(|t| resource_name(t.0) == name) =>
            {
                self.help_text(name)?
            }
            _ => return Err(resources::unknown_resource(uri)),
        };
        if !asked.paged() {
            return Ok(text);
        }
        Ok(borer_engine::table::page(
            &text,
            asked.offset.unwrap_or(0),
            asked.limit.unwrap_or(usize::MAX),
            &asked.again(),
        ))
    }
}

/// What agents most often ask `find_check` about.
const CHECK_KINDS: &[&str] = &[
    "activation code",
    "checksum",
    "license key",
    "password",
    "registration",
    "serial",
    "signature",
    "token",
];

/// Strips schema noise an agent never needs.
///
/// Gone are the draft URL, integer formats, non-negativity bounds (every
/// count documents its own default and maximum), the `null` alternative
/// schemars adds to an optional parameter's type or enum (leaving the
/// parameter out is how a client says null), and `additionalProperties:
/// false`, which every parameter struct enforces at the boundary through
/// `deny_unknown_fields` with an error that names the field. An enum
/// parameter's `$defs` entry is written into the parameter itself, with the
/// parameter's own description, so a client reads its choices in place
/// rather than following a `$ref`.
///
/// # Arguments
///
/// * `t` - The tool as generated by rmcp.
fn slim_tool(mut t: Tool) -> Tool {
    let mut schema = (*t.input_schema).clone();
    schema.remove("$schema");
    schema.remove("additionalProperties");
    let defs = match schema.remove("$defs") {
        Some(serde_json::Value::Object(defs)) => defs,
        _ => serde_json::Map::new(),
    };
    if let Some(serde_json::Value::Object(props)) = schema.get_mut("properties") {
        for p in props.values_mut() {
            if let serde_json::Value::Object(o) = p {
                o.remove("format");
                o.remove("minimum");
                if let Some(serde_json::Value::Array(any)) = o.get("anyOf") {
                    let mut rest = any.iter().filter(|s| s.get("type") != Some(&"null".into()));
                    if let (Some(serde_json::Value::Object(only)), None) =
                        (rest.next(), rest.next())
                    {
                        let only = only.clone();
                        o.remove("anyOf");
                        o.extend(only);
                    }
                }
                let inlined = o
                    .get("$ref")
                    .and_then(serde_json::Value::as_str)
                    .and_then(|r| r.strip_prefix("#/$defs/"))
                    .and_then(|name| defs.get(name))
                    .and_then(serde_json::Value::as_object)
                    .cloned();
                if let Some(def) = inlined {
                    o.remove("$ref");
                    for (k, v) in def {
                        if k != "description" || !o.contains_key("description") {
                            o.insert(k, v);
                        }
                    }
                }
                let only = match o.get("type") {
                    Some(serde_json::Value::Array(kinds)) => {
                        let mut rest = kinds.iter().filter(|k| k.as_str() != Some("null"));
                        match (rest.next(), rest.next()) {
                            (Some(kind), None) => Some(kind.clone()),
                            _ => None,
                        }
                    }
                    _ => None,
                };
                if let Some(kind) = only {
                    o.insert("type".to_owned(), kind);
                }
            }
        }
    }
    if !defs.is_empty()
        && serde_json::Value::Object(schema.clone())
            .to_string()
            .contains("\"$ref\"")
    {
        schema.insert("$defs".to_owned(), serde_json::Value::Object(defs));
    }
    t.input_schema = Arc::new(schema);
    t
}

impl BorerServer {
    /// Lists function names (overlay, symbols, `sub_X`) starting with a prefix.
    ///
    /// # Arguments
    ///
    /// * `prefix` - Lower-cased prefix; empty lists everything.
    ///
    /// # Returns
    ///
    /// Sorted, deduplicated names; empty when no analysis is available.
    fn complete_names(&self, prefix: &str) -> Vec<String> {
        let Ok(a) = self.ensure_analysis() else {
            return Vec::new();
        };
        let o = self.overlay();
        let mut names: Vec<String> = a
            .functions
            .iter()
            .map(|f| borer_engine::analysis::name_of(&a, &o, f.entry))
            .filter(|n| n.to_lowercase().starts_with(prefix))
            .collect();
        names.sort();
        names.dedup();
        names
    }
}

/// Runs a worker of the MCP server, the relay in front of it, or a CLI
/// command, by what the process was started with.
///
/// The host launches the binary with no arguments, which is the relay
/// ([`relay::run`]); the relay starts this same binary again as the worker
/// ([`relay::WORKER`]), which serves the session ([`serve`]). With
/// arguments it runs a CLI command.
///
/// Every one of them runs below normal priority
/// ([`borer_live::run_below_normal`]): an analysis takes every core it is
/// given, and a machine running several of them at once stays usable
/// because its desktop goes first. Its allocator commits memory as it is
/// touched and hands freed memory back soon ([`borer_live::tune_allocator`]).
///
/// # Errors
///
/// When the tokio runtime cannot be built, the server or the relay fails,
/// or the CLI command fails.
fn main() -> anyhow::Result<()> {
    borer_live::run_below_normal();
    borer_live::tune_allocator();
    if let Some(state) = std::env::var_os(relay::WORKER) {
        let resume = std::env::var_os(relay::RESUME).map(PathBuf::from);
        return tokio::runtime::Runtime::new()?.block_on(serve(PathBuf::from(state), resume));
    }
    let args: Vec<String> = std::env::args().skip(1).collect();
    if args.is_empty() {
        if std::io::IsTerminal::is_terminal(&std::io::stdin()) {
            print!("{}", term::welcome());
            return Ok(());
        }
        return relay::run();
    }
    end_quietly_when_stdout_closes();
    let check = (args.first().map(String::as_str) != Some("update"))
        .then(update::start_check)
        .flatten();
    let result = cli::cli(&args);
    term::flush();
    result?;
    if let Some(line) = check.and_then(update::notice) {
        eprintln!("{line}");
    }
    Ok(())
}

/// Serves the MCP session over this worker's standard handles.
///
/// A worker taking over from one that handed over serves without a
/// handshake, since the client initialized the session with an earlier
/// worker; it loads the file that worker had loaded, with its names and
/// comments, and tells the client the tools changed.
///
/// # Arguments
///
/// * `state` - The file this worker writes the session's state to when
///   `reload` hands it over ([`relay::WORKER`]).
/// * `resume` - The state of the worker before this one, when this one
///   takes over ([`relay::RESUME`]).
///
/// # Errors
///
/// When the handshake or the transport fails.
async fn serve(state: PathBuf, resume: Option<PathBuf>) -> anyhow::Result<()> {
    let server = BorerServer::new();
    let transport = HandOverTransport::new(Arc::clone(&server.hand_over), state);
    let Some(file) = resume else {
        server.serve(transport).await?.waiting().await?;
        return Ok(());
    };
    let resume = Resume::take(&file).unwrap_or_else(|e| {
        eprintln!("borer: the session resumes without its state: {e}");
        Resume::default()
    });
    let info = server.resume(resume);
    let service = rmcp::service::serve_directly(server, transport, info);
    if let Err(e) = service.peer().notify_tool_list_changed().await {
        eprintln!("borer: the client was not told the tools changed: {e}");
    }
    service.waiting().await?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use crate::testing::{listed_rows, raw_server, tiny_server};

    /// Every answer ends with an evidence line naming it, and the id it
    /// names returns the answer exactly as it was sent.
    ///
    /// The line is the answer's last, a `# since=` line before it, and the
    /// id is `<n>-<8 hex digits>`; an id no `# evidence:` line carried is
    /// refused as invalid params.
    ///
    /// # Panics
    ///
    /// When the line is missing or malformed, or the read is not the text.
    #[test]
    fn an_answer_ends_with_evidence_that_returns_it() {
        use borer_engine::program::{Arch, Program, Section};
        let mut code = vec![0x90; 0x200];
        code.push(0xc3);
        let text = Section::mapped(".text", 0x1000, 0, 0x201, false, true);
        let program = Program::raw(code, Arch::X86_64, 0, Some(0x1000), vec![text]);
        let server = super::BorerServer {
            program: std::sync::Arc::new(std::sync::RwLock::new(Some(std::sync::Arc::new(
                program,
            )))),
            pdb_applied: std::sync::Arc::new(std::sync::RwLock::new(true)),
            ..super::BorerServer::default()
        };
        let whole = server.read_uri("borer://disasm/0x1000").expect("reads").1;
        let last = whole.lines().last().expect("a last line");
        let id = last
            .strip_prefix("# evidence: ")
            .expect("the answer ends with its evidence line")
            .to_owned();
        let (counter, digest) = id.split_once('-').expect("the id is <n>-<digest>");
        assert!(!counter.is_empty() && counter.chars().all(|c| c.is_ascii_alphanumeric()));
        assert_eq!(digest.len(), 8, "{id}");
        assert!(digest.chars().all(|c| c.is_ascii_hexdigit()), "{id}");
        let evidence_uri = format!("borer://session/evidence/{id}");
        let (read_as, back) = server.read_uri(&evidence_uri).expect("reads");
        assert_eq!((read_as.as_str(), back), (evidence_uri.as_str(), whole));
        let refused = server
            .read_uri("borer://session/evidence/9999-00000000")
            .expect_err("never minted");
        assert_eq!(refused.code, rmcp::model::ErrorCode::INVALID_PARAMS);
    }

    /// A fault inside a tool becomes an answer, not a dead session.
    ///
    /// An analysis pass that faults would otherwise unwind out of the handler
    /// and end the process: the call gets no reply, the agent cannot tell a
    /// crash from a hang, and the session's work is gone with it. Every tool
    /// body that reaches a program comes through one place, so the fault is
    /// turned into an error there and the message says what happened. The
    /// panic hook is silenced for the fault: the backtrace it would print is
    /// the point of leaving it alone in the real path, and only noise in a
    /// test that expects the fault. The server is then still usable, which
    /// is the whole point. Only a fault is an internal error: a body that
    /// refuses its request (an address naming nothing) answers invalid
    /// params, so the agent knows to fix the call rather than retry it.
    ///
    /// # Panics
    ///
    /// When a fault escapes, its message is lost on the way out, or a
    /// refusal and a fault share one error code.
    #[test]
    fn a_fault_inside_a_tool_is_answered_not_fatal() {
        let exe = std::env::current_exe().expect("the test binary has a path");
        let program = borer_engine::program::Program::load(&exe).expect("it loads itself");
        let server = super::BorerServer {
            program: std::sync::Arc::new(std::sync::RwLock::new(Some(std::sync::Arc::new(
                program,
            )))),
            pdb_applied: std::sync::Arc::new(std::sync::RwLock::new(true)),
            ..super::BorerServer::default()
        };

        let hook = std::panic::take_hook();
        std::panic::set_hook(Box::new(|_| {}));
        let faulted = server.with_program(|_| panic!("a pass fell over"));
        let sound = server.with_program(|p| Ok(format!("{} sections", p.sections.len())));
        let refused = server.with_program(|_| Err("'nowhere' names nothing".to_owned()));
        std::panic::set_hook(hook);

        let refused = refused.expect_err("the refusal reached the caller");
        assert_eq!(refused.code, rmcp::model::ErrorCode::INVALID_PARAMS);
        let faulted = faulted.expect_err("the fault reached the caller");
        assert_eq!(faulted.code, rmcp::model::ErrorCode::INTERNAL_ERROR);
        let err = faulted.message;
        assert!(err.contains("faulted"), "{err}");
        assert!(!err.contains("  "), "the message reads as one line: {err}");
        assert!(
            err.contains("a pass fell over"),
            "the message is lost: {err}"
        );
        assert!(sound.is_ok(), "the next call failed too");
    }

    /// Every resource read before a binary is loaded is refused as invalid
    /// params, the code every tool answers then.
    ///
    /// `qt`, `map`, `classes`, `singletons` and `enums` answered an
    /// internal error, which reads as the server failing rather than the
    /// request coming too early.
    ///
    /// # Panics
    ///
    /// When a resource answers an internal error, or one of the five does
    /// not refuse with [`crate::state::NO_BINARY`].
    #[test]
    fn every_resource_refuses_without_a_binary_as_invalid_params() {
        let server = super::BorerServer::default();
        for uri in ["qt", "map", "classes", "singletons", "enums"] {
            let refused = server
                .resource_text(&format!("borer://{uri}"))
                .expect_err("nothing is loaded");
            assert_eq!(
                refused.code,
                rmcp::model::ErrorCode::INVALID_PARAMS,
                "{uri}"
            );
            assert_eq!(refused.message, crate::state::NO_BINARY, "{uri}");
        }
        let uris = crate::catalog::RESOURCES
            .iter()
            .map(|r| r.0)
            .chain(crate::catalog::RESOURCE_TEMPLATES.iter().map(|t| t.0))
            .map(|uri| {
                uri.split('/')
                    .map(|part| if part.starts_with('{') { "x" } else { part })
                    .collect::<Vec<_>>()
                    .join("/")
            });
        for uri in uris {
            if let Err(e) = server.resource_text(&uri) {
                assert_ne!(
                    e.code,
                    rmcp::model::ErrorCode::INTERNAL_ERROR,
                    "{uri}: {e:?}"
                );
            }
        }
    }

    /// An arm64 program disassembles, lists its functions and decompiles.
    ///
    /// The `disassemble` tool lists from the word an address falls inside,
    /// a script's `disasm` reads the same words and its `functions` the one
    /// function, the `functions` tool lists it, and `decompile` writes it,
    /// with the line saying what of it was checked against the arm64
    /// machine.
    ///
    /// # Panics
    ///
    /// When a listing or the text differs.
    #[test]
    fn an_arm64_program_lists_and_decompiles_its_functions() {
        use crate::params::DecompileParams;
        use crate::params::DisassembleParams;
        use crate::params::FunctionsParams;
        use crate::params::ScriptParams;
        use borer_engine::program::{Arch, Program, Section};
        use rmcp::handler::server::wrapper::Parameters;
        let code: Vec<u8> = [
            // ASM: bti c
            0xd503_245fu32,
            // ASM: ret
            0xd65f_03c0,
        ]
        .iter()
        .flat_map(|w| w.to_le_bytes())
        .collect();
        let text = Section::mapped(".text", 0x1000, 0, 8, false, true);
        let program = Program::raw(code, Arch::Arm64, 0, Some(0x1000), vec![text]);
        let server = super::BorerServer {
            program: std::sync::Arc::new(std::sync::RwLock::new(Some(std::sync::Arc::new(
                program,
            )))),
            pdb_applied: std::sync::Arc::new(std::sync::RwLock::new(true)),
            ..super::BorerServer::default()
        };
        let out = server
            .disassemble(Parameters(DisassembleParams {
                address: "0x1002".to_owned(),
                count: None,
                bytes: None,
            }))
            .expect("arm64 disassembles");
        assert!(
            out.starts_with(
                "# 2 instructions at 0x1000; 0x1002 is inside an instruction, listing from 0x1000;"
            ) && out.contains("\n0x1000  bti c\n0x1004  ret\n"),
            "{out}"
        );
        let out = server
            .script(Parameters(ScriptParams {
                code: "print(disasm(0x1000, 2)[1].text); print(functions().len);".to_owned(),
                dry_run: None,
            }))
            .expect("a script answers");
        assert!(out.starts_with("ret\n1\n"), "{out}");
        let listed = server
            .functions(Parameters(FunctionsParams {
                filter: None,
                sort: None,
                offset: None,
                limit: None,
                count_only: None,
            }))
            .expect("arm64 functions are discovered");
        assert!(listed.lines().any(|l| l.starts_with("0x1000 ")), "{listed}");
        let text = server
            .decompile(Parameters(DecompileParams {
                address: "0x1000".to_owned(),
                detail: None,
                filter: None,
                offset: None,
                limit: None,
            }))
            .expect("arm64 decompiles");
        assert!(
            text.contains("// signature: void sub_1000()")
                && text.contains("// checked vs binary: statements as emitted, 1/1 blocks")
                && text.contains("return;"),
            "{text}"
        );
    }

    /// An arm64 function runs under `borer://emulate` and `borer://run`,
    /// and a surface built on the x86 machine refuses it as an invalid
    /// request.
    ///
    /// # Panics
    ///
    /// When a run answers otherwise, or the refusal does not come.
    #[test]
    fn an_arm64_function_runs_under_emulate_and_run() {
        use borer_engine::program::{Arch, Program, Section};
        let code: Vec<u8> = [
            // ASM: add x0, x0, #0x1
            0x9100_0400u32,
            // ASM: ret
            0xd65f_03c0,
        ]
        .iter()
        .flat_map(|w| w.to_le_bytes())
        .collect();
        let text = Section::mapped(".text", 0x1000, 0, 8, false, true);
        let program = Program::raw(code, Arch::Arm64, 0, Some(0x1000), vec![text]);
        let server = super::BorerServer {
            program: std::sync::Arc::new(std::sync::RwLock::new(Some(std::sync::Arc::new(
                program,
            )))),
            pdb_applied: std::sync::Arc::new(std::sync::RwLock::new(true)),
            ..super::BorerServer::default()
        };
        let out = server
            .resource_text("borer://emulate/0x1000,x0=0x29")
            .expect("an arm64 routine runs");
        assert!(
            out.contains("returned after 2 steps") && out.contains("# registers: x0=0x2a x1=0x0"),
            "{out}"
        );
        let table = server
            .resource_text("borer://run/0x1000/41")
            .expect("an arm64 function runs on an input");
        assert!(
            table.contains("\t0x2a\treturned\t2\t-\tunchecked\n")
                && table.contains("a run's text is checked for x86 code only"),
            "{table}"
        );
        let refused = server
            .resource_text("borer://oracle/0x1000")
            .expect_err("the oracle drives the x86 machine");
        assert!(
            refused
                .message
                .contains("oracle runs x86 and x86-64 code only for now"),
            "{}",
            refused.message
        );
    }

    /// Page one and page two of a listing hold its first rows, in order.
    ///
    /// So they do whether the server pages the rows (`borer://help`) or
    /// the listing pages itself (`borer://fieldrefs`, `borer://calls`);
    /// each page says what it shows and names the next.
    ///
    /// # Panics
    ///
    /// When a page drops, repeats or reorders a row, or misnames the next.
    #[test]
    fn page_one_and_page_two_are_the_first_rows_of_the_whole() {
        use borer_engine::program::{Arch, Program, Section};
        let mut code = vec![
            0xe8, 0x1b, 0x00, 0x00, 0x00, // ASM: call 0x1020
            0xe8, 0x16, 0x00, 0x00, 0x00, // ASM: call 0x1020
            0xe8, 0x11, 0x00, 0x00, 0x00, // ASM: call 0x1020
            0xc3, // ASM: ret
        ];
        code.resize(0x20, 0xcc);
        for n in 0u8..8 {
            code.extend_from_slice(&[0x89, 0x41, 0x10 + n * 8]); // ASM: mov [rcx+0x10+n*8], eax
        }
        code.extend_from_slice(&[0x89, 0x41, 0x10, 0x89, 0x41, 0x10, 0xc3]); // ASM: mov [rcx+0x10], eax (twice); ret
        let len = u64::try_from(code.len()).expect("small");
        let text = Section::mapped(".text", 0x1000, 0, len, false, true);
        let program = Program::raw(code, Arch::X86_64, 0, Some(0x1000), vec![text]);
        let server = super::BorerServer {
            program: std::sync::Arc::new(std::sync::RwLock::new(Some(std::sync::Arc::new(
                program,
            )))),
            pdb_applied: std::sync::Arc::new(std::sync::RwLock::new(true)),
            ..super::BorerServer::default()
        };
        let read = |uri: &str| server.read_uri(uri).expect("reads").1;
        for (uri, size) in [
            ("borer://help", 10),
            ("borer://fieldrefs/0x10", 1),
            ("borer://calls/0x1020", 1),
        ] {
            let whole = listed_rows(&server.resource_text(uri).expect("reads whole"));
            let one = read(&format!("{uri}!limit={size}"));
            let two = read(&format!("{uri}!offset={size}!limit={size}"));
            let paged: Vec<String> = listed_rows(&one)
                .into_iter()
                .chain(listed_rows(&two))
                .collect();
            assert!(whole.len() > 2 * size, "{uri}: {whole:?}");
            assert_eq!(paged, whole[..2 * size], "{uri}");
            assert!(
                one.contains(&format!("# showing {size} of {} from 0", whole.len()))
                    || one.contains(&format!("# {} sites touch", whole.len())),
                "{one}"
            );
            assert!(two.contains(" for the next page\n"), "{two}");
        }
        let help = read("borer://help!limit=10");
        assert!(
            help.contains("borer://help!limit=10!offset=10 for the next page"),
            "{help}"
        );
        let calls = read("borer://calls/0x1020!limit=1");
        assert!(
            calls.contains(",offset=1,limit=1 for the next page"),
            "{calls}"
        );
        let (asked, _) = server
            .read_uri("borer://help!limit=3!offset=1")
            .expect("reads");
        assert_eq!(asked, "borer://help!offset=1!limit=3");
        let refused = server
            .read_uri("borer://help!limit=0")
            .expect_err("no rows");
        assert_eq!(refused.code, rmcp::model::ErrorCode::INVALID_PARAMS);
    }

    /// Every template read without its argument says how to read it.
    ///
    /// The answer is its URI, its description with the grammar in it, and
    /// an example built from the loaded binary, the same bytes each time;
    /// `borer://help/<name>` says the same of any resource, and
    /// `borer://help` lists each one once.
    ///
    /// # Panics
    ///
    /// When a template's bare read refuses or lacks a part, the example is
    /// not filled in, or the list misses or repeats a resource.
    #[test]
    fn a_template_read_bare_says_its_grammar_and_an_example() {
        let server = raw_server();
        for &(uri, description, _) in crate::catalog::RESOURCE_TEMPLATES {
            let name = crate::catalog::resource_name(uri);
            let fixed = crate::catalog::RESOURCES
                .iter()
                .any(|r| crate::catalog::resource_name(r.0) == name);
            let bare = if fixed {
                format!("borer://help/{name}")
            } else {
                format!("borer://{name}")
            };
            let help = server
                .resource_text(&bare)
                .expect("a bare template answers");
            assert!(
                help.contains(&format!("# {uri}\n{description}\n")),
                "{help}"
            );
            let example = help
                .lines()
                .find_map(|l| l.strip_prefix("# example: "))
                .unwrap_or_else(|| panic!("{uri} has no example: {help}"));
            assert!(
                example.starts_with(&format!("borer://{name}/")) && !example.contains('{'),
                "{uri}: {example}"
            );
            assert_eq!(server.resource_text(&bare).expect("again"), help);
        }
        let emulate = server.resource_text("borer://emulate").expect("answers");
        assert!(
            emulate.contains("# example: borer://emulate/0x1000,a1=5,steps=10000\n"),
            "{emulate}"
        );
        let triage = server
            .resource_text("borer://help/triage")
            .expect("answers");
        assert!(triage.starts_with("# borer://triage\n"), "{triage}");
        let index = server.resource_text("borer://help").expect("answers");
        let listed: Vec<&str> = index
            .lines()
            .skip(1)
            .filter_map(|l| l.split('\t').next())
            .collect();
        let every: Vec<&str> = crate::catalog::RESOURCES
            .iter()
            .map(|r| r.0)
            .chain(crate::catalog::RESOURCE_TEMPLATES.iter().map(|t| t.0))
            .collect();
        assert_eq!(listed, every, "{index}");
    }

    /// An unknown URI is refused with at most three resources nearest it.
    ///
    /// The refusal says where every resource is listed, in a few hundred
    /// bytes where the list of every resource took two thousand; a fixed
    /// resource given an argument is told it takes none, and a name nothing
    /// resembles says so.
    ///
    /// # Panics
    ///
    /// When a refusal is long, names the wrong resources, or reads as
    /// another error.
    #[test]
    fn an_unknown_uri_names_the_nearest_resources() {
        let server = raw_server();
        let refused = |uri: &str| {
            let e = server.resource_text(uri).expect_err("unknown");
            assert_eq!(e.code, rmcp::model::ErrorCode::RESOURCE_NOT_FOUND, "{uri}");
            e.message.into_owned()
        };
        let typo = refused("borer://emulat");
        assert!(typo.len() < 600, "{} bytes: {typo}", typo.len());
        assert_eq!(
            typo,
            "unknown resource borer://emulat; nearest: borer://emulate/{address}; borer://help lists every resource"
        );
        let guessed = refused("borer://disassemble/0x1000");
        assert!(
            guessed.contains("; nearest: borer://disasm/{address}; "),
            "{guessed}"
        );
        let wide = refused("borer://ma");
        assert!(
            wide.contains("nearest: borer://map, ") && wide.matches(", ").count() == 2,
            "three at most: {wide}"
        );
        assert!(
            refused("borer://emulat/0x1000").contains("nearest: borer://emulate/{address}"),
            "the name is matched without its argument"
        );
        assert_eq!(
            refused("borer://triage/0x1000"),
            "borer://triage takes no argument; read borer://triage"
        );
        assert!(
            refused("borer://zzzzqqqq").contains("; no resource is near it; "),
            "nothing near"
        );
        assert!(
            refused("http://emulate").contains("a resource's URI starts with borer://"),
            "not a borer URI"
        );
        assert!(
            refused("borer://help/emulat").starts_with(
                "unknown resource borer://help/emulat; nearest: borer://emulate/{address}"
            ),
            "help for a misspelled name"
        );
    }

    /// A name nothing matches is refused with the names nearest it,
    /// wherever a tool takes an address or a name.
    ///
    /// # Panics
    ///
    /// When the refusal leaves the nearest name out.
    #[test]
    fn a_misspelled_name_is_refused_with_the_nearest() {
        use crate::params::FunctionParams;
        use rmcp::handler::server::wrapper::Parameters;
        let server = raw_server();
        crate::state::write_lock(&server.overlay)
            .names
            .insert(0x1000, "check_serial".to_owned());
        let refused = server
            .function_summary(Parameters(FunctionParams {
                address: "chk_serial".to_owned(),
            }))
            .expect_err("no such name");
        assert!(
            refused.message.contains("; nearest: check_serial; "),
            "{}",
            refused.message
        );
    }

    /// A count above a tool's cap is cut to the cap and the answer opens by
    /// saying so, naming the parameter, what was asked and the cap; a count
    /// within the cap leaves the answer as it was.
    ///
    /// # Panics
    ///
    /// When a cut goes unsaid, or an uncut answer carries a note.
    #[test]
    fn a_count_above_the_cap_is_noted_in_the_answer() {
        use crate::params::FunctionsParams;
        use crate::params::HexdumpParams;
        use crate::params::ReadParams;
        use crate::params::StringsParams;
        use rmcp::handler::server::wrapper::Parameters;
        let server = raw_server();
        let functions = |limit| {
            server
                .functions(Parameters(FunctionsParams {
                    filter: None,
                    sort: None,
                    offset: None,
                    limit,
                    count_only: None,
                }))
                .expect("lists")
        };
        let capped = functions(Some(99_999));
        assert!(
            capped.starts_with("# limit 99999 capped at 300\n"),
            "{capped}"
        );
        assert_eq!(
            capped.strip_prefix("# limit 99999 capped at 300\n"),
            Some(functions(Some(300)).as_str()),
            "the note is the only difference"
        );
        assert!(!functions(Some(300)).contains("capped"));

        let strings = server
            .strings(Parameters(StringsParams {
                min_length: None,
                filter: None,
                encoding: None,
                offset: None,
                limit: Some(1_000),
                count_only: None,
            }))
            .expect("lists");
        assert!(
            strings.starts_with("# limit 1000 capped at 500\n# showing "),
            "{strings}"
        );
        let dump = server
            .hexdump(Parameters(HexdumpParams {
                address: "0x1000".to_owned(),
                length: Some(99_999),
            }))
            .expect("dumps");
        assert!(
            dump.starts_with("# length 99999 capped at 4096\n# 0x1000..0x1100 .text\n"),
            "{dump}"
        );
        let read = server
            .read(Parameters(ReadParams {
                address: "0x1000".to_owned(),
                kind: Some(super::params::ReadKind::U8),
                r#type: None,
                count: Some(300),
            }))
            .expect("reads");
        assert!(
            read.starts_with("# count 300 capped at 256\n# 256 x u8 at 0x1000"),
            "{read}"
        );
    }

    /// Every list tool refuses `limit: 0` alike, before anything is loaded,
    /// and so does a watch of no bytes; `decompile` reads zero as every line,
    /// as it documents.
    ///
    /// # Panics
    ///
    /// When a zero is answered, or refused another way.
    #[test]
    fn every_list_tool_refuses_a_zero_limit_alike() {
        use crate::params::DecompileParams;
        use crate::params::FindFunctionByStringParams;
        use crate::params::FunctionsParams;
        use crate::params::LiveInstancesParams;
        use crate::params::LiveModulesParams;
        use crate::params::LiveWatchParams;
        use crate::params::SearchParams;
        use crate::params::StringsParams;
        use crate::params::SymbolsParams;
        use crate::params::XrefsParams;
        use rmcp::handler::server::wrapper::Parameters;
        let server = super::BorerServer::default();
        let refusals = [
            server.strings(Parameters(StringsParams {
                min_length: None,
                filter: None,
                encoding: None,
                offset: None,
                limit: Some(0),
                count_only: None,
            })),
            server.symbols(Parameters(SymbolsParams {
                kind: None,
                filter: None,
                offset: None,
                limit: Some(0),
                count_only: None,
            })),
            server.functions(Parameters(FunctionsParams {
                filter: None,
                sort: None,
                offset: None,
                limit: Some(0),
                count_only: None,
            })),
            server.xrefs(Parameters(XrefsParams {
                address: "main".to_owned(),
                offset: None,
                limit: Some(0),
                count_only: None,
            })),
            server.search(Parameters(SearchParams {
                query: "90".to_owned(),
                kind: None,
                offset: None,
                limit: Some(0),
                count_only: None,
            })),
            server.find_function_by_string(Parameters(FindFunctionByStringParams {
                filter: "x".to_owned(),
                offset: None,
                limit: Some(0),
            })),
            server.live_instances(Parameters(LiveInstancesParams {
                class: "Player".to_owned(),
                offset: None,
                limit: Some(0),
                count_only: None,
            })),
            server.live_modules(Parameters(LiveModulesParams {
                filter: None,
                offset: None,
                limit: Some(0),
                count_only: None,
            })),
        ];
        for refused in refusals {
            let e = refused.expect_err("a zero limit is refused");
            assert_eq!(e.code, rmcp::model::ErrorCode::INVALID_PARAMS);
            assert_eq!(e.message, "limit must be at least 1");
        }
        let watch = server
            .live_watch(Parameters(LiveWatchParams {
                name: "w".to_owned(),
                address: Some("0x1000".to_owned()),
                length: Some(0),
                class: None,
            }))
            .expect_err("a watch of no bytes is refused");
        assert_eq!(watch.code, rmcp::model::ErrorCode::INVALID_PARAMS);
        assert_eq!(watch.message, "length must be at least 1");
        let all = server
            .decompile(Parameters(DecompileParams {
                address: "main".to_owned(),
                detail: None,
                filter: None,
                offset: None,
                limit: Some(0),
            }))
            .expect_err("nothing is loaded");
        assert_eq!(
            all.message,
            crate::state::NO_BINARY,
            "zero is every line, not refused"
        );
    }

    /// `borer://script` refuses a device by name, as the other file
    /// resources do, where reading `CON` waited on the console forever.
    ///
    /// # Panics
    ///
    /// When a device is read.
    #[test]
    fn a_script_resource_refuses_a_device() {
        if cfg!(windows) {
            let refused = tiny_server().script_text("CON").expect_err("a device");
            assert_eq!(refused.code, rmcp::model::ErrorCode::INVALID_PARAMS);
            assert!(refused.message.contains("device"), "{}", refused.message);
        }
    }

    /// A failing script file answers as the `script` tool answers one:
    /// what it printed before the error, then the error; the resource
    /// answered the error alone and the printed lines were lost.
    ///
    /// # Panics
    ///
    /// When the failure loses its output or its error.
    #[test]
    fn a_failing_script_resource_keeps_what_it_printed() {
        let path = std::env::temp_dir().join(format!("borer-fail-{}.rhai", std::process::id()));
        std::fs::write(&path, "print(\"before the error\");\nlet x = 1 / 0;\n")
            .expect("the script is written");
        let answer = tiny_server().script_text(&path.to_string_lossy());
        std::fs::remove_file(&path).expect("the script is removed");
        let text = answer.expect("a failed script still answers");
        assert!(text.starts_with("before the error\n"), "{text}");
        assert!(text.contains("\n# script failed: "), "{text}");
    }

    /// `borer://anchors` refuses a manifest past its size or anchor cap by
    /// name and lists at most a page of rows, saying so; a 200 MB manifest
    /// ran for minutes and every row came back.
    ///
    /// # Panics
    ///
    /// When an oversized manifest is judged or the rows are not capped.
    #[test]
    fn the_anchors_resource_caps_its_manifest_and_rows() {
        let server = tiny_server();
        let dir = std::env::temp_dir();
        let id = std::process::id();
        let write = |name: &str, lines: usize| {
            let path = dir.join(format!("borer-anchors-{id}-{name}.txt"));
            std::fs::write(&path, "function nosuch 0x1\n".repeat(lines))
                .expect("the manifest is written");
            path
        };
        let huge = write("huge", 60_000);
        let many = write("many", 5001);
        let page = write("page", 600);
        let answers: Vec<_> = [&huge, &many, &page]
            .iter()
            .map(|p| server.anchors_text(&p.to_string_lossy()))
            .collect();
        for p in [&huge, &many, &page] {
            std::fs::remove_file(p).expect("the manifest is removed");
        }
        let [huge, many, page] = <[_; 3]>::try_from(answers).expect("three answers");
        let huge = huge.expect_err("past the size cap");
        assert!(huge.message.contains("bytes, past the"), "{}", huge.message);
        let many = many.expect_err("past the anchor cap");
        assert!(
            many.message.contains("has 5001 anchors, past the 5000"),
            "{}",
            many.message
        );
        let page = page.expect("a page of rows");
        assert!(
            page.starts_with(
                "# 600 anchors: 0 held, 0 moved, 0 changed, 600 gone, showing 500 of 600"
            ),
            "{page}"
        );
        assert_eq!(page.lines().count(), 502, "{page}");
    }
}
