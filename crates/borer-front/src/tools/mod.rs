//! The tool catalog: the tools both faces list and run.
//!
//! The faces are the MCP server over stdio and the app's chat. Each row
//! ([`Tool`]) ties a tool's name, its typed parameters (whose schema states
//! the caps and defaults), its description, effects and hints, and the
//! handler that answers it over what a front end holds ([`Held`]). The
//! server builds its list, schemas and dispatch for these rows from
//! [`TOOLS`]; the app builds its model's tool list from the same rows
//! ([`Tool::input_schema`]) and runs a call with [`Tool::run`].
//!
//! Given the same program, analysis and names, a catalog tool's answer, its
//! refusal and the field a bad argument names are the same bytes on both
//! faces: the catalog owns how a tool runs ([`run`]). What differs is the
//! face's own: the server's session adds the `# since=` memory of answers,
//! the `# evidence:` line, a deadline's note and the cut to its byte budget
//! ([`crate::budget`]); `query` reads every resource on the server and,
//! elsewhere, what the engine answers, refusing a server resource by name
//! ([`ask`]). The tools that need what only the server has stay the
//! server's, each named in [`SERVER_ONLY`] with its reason.

mod bytes;
mod code;
mod edit;
mod held;
pub mod params;
mod propose;
mod read;

use schemars::JsonSchema;
use serde_json::{Map, Value};

pub use bytes::{
    annotations, disassemble, entropy, entropy_threshold, find_crypto_constants,
    find_function_by_string, hexdump, query, read, render_hits, search, strings, symbols, types,
};
pub use code::{
    callgraph, cfg, class_field, decompile, disassemble_function, function, function_strings,
    function_summary, functions, reaches, xrefs,
};
pub use edit::{class_layout, script, set_comment, set_name, set_type};
pub use held::{
    Apply, Cause, Edited, Failure, Find, Held, NO_BINARY, Outcome, Snapshot, View, fault_text,
    guarded, run, snapshot, tabled,
};
use params::{DESERIALIZE_PREFIX, misfit};
pub use propose::{Keeping, Kept, propose};
pub use read::{Loaded, SERVER_RESOURCES, ask, read_engine};

/// Something a tool touches outside the loaded program and its analysis.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Effect {
    /// Reads a file at a path the caller names.
    ReadsFiles,
    /// Writes a file: under the output root, or the symbol cache. The
    /// decompilation index a read of `borer://index` or `borer://grep`
    /// builds is borer's own cache of what it derived and is not one.
    WritesFiles,
    /// Connects to a server over the network.
    Network,
    /// Reads the memory of another running process, never writing it.
    ReadsProcessMemory,
    /// Changes the session: its names, comments, types, loaded program or attach.
    ChangesSession,
    /// Replaces the server process with the borer binary now on disk.
    RestartsServer,
}

impl Effect {
    /// Every effect, in the manifest's order.
    pub const ALL: [Self; 6] = [
        Self::ReadsFiles,
        Self::WritesFiles,
        Self::Network,
        Self::ReadsProcessMemory,
        Self::ChangesSession,
        Self::RestartsServer,
    ];

    /// Returns the effect's word in a tool's `_meta` and the manifest.
    #[must_use]
    pub const fn word(self) -> &'static str {
        match self {
            Self::ReadsFiles => "reads-files",
            Self::WritesFiles => "writes-files",
            Self::Network => "network",
            Self::ReadsProcessMemory => "reads-process-memory",
            Self::ChangesSession => "changes-session",
            Self::RestartsServer => "restarts-server",
        }
    }

    /// Returns the effect's meaning, for the manifest's legend.
    #[must_use]
    pub const fn meaning(self) -> &'static str {
        match self {
            Self::ReadsFiles => "reads a file at a path the caller names",
            Self::WritesFiles => {
                "writes a file under the output root or into the symbol cache; not counted: the decompilation index a read of borer://index or borer://grep builds in borer's own cache directory"
            }
            Self::Network => "connects to a server over the network (https only)",
            Self::ReadsProcessMemory => {
                "reads the memory of another running process (Windows), never writing it"
            }
            Self::ChangesSession => {
                "changes the session in memory: names, comments, types, the loaded program or the attach; never the binary"
            }
            Self::RestartsServer => "replaces the server process with the borer binary now on disk",
        }
    }
}

/// The four MCP annotation hints a tool states.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Hints {
    /// It changes nothing.
    pub read_only: bool,
    /// What it changes it may overwrite (meaningful only when not read-only).
    pub destructive: bool,
    /// Calling it again with the same arguments changes nothing more.
    pub idempotent: bool,
    /// It reaches past the session (the network, another process).
    pub open_world: bool,
}

/// The hints of a tool that only reads the program.
const READS: Hints = Hints {
    read_only: true,
    destructive: false,
    idempotent: true,
    open_world: false,
};

/// The hints of a tool that edits the session's names, comments or types,
/// a dry run unless told otherwise.
const EDITS: Hints = Hints {
    read_only: false,
    destructive: false,
    idempotent: true,
    open_world: false,
};

/// Answers one call: what the front end holds and the call's arguments.
pub type Run = fn(&dyn Held, Map<String, Value>) -> Result<String, Failure>;

/// One tool both faces list and run, built by the catalog's `row!` macro so
/// its schema and its handler read one parameters type.
#[derive(Debug, Clone, Copy)]
pub struct Tool {
    /// Its name, as a caller calls it.
    pub name: &'static str,
    /// What it returns, its caps and defaults, for a caller that never saw
    /// the project.
    pub description: &'static str,
    /// What it touches beyond the program; empty for one that only reads it.
    pub effects: &'static [Effect],
    /// Its annotation hints.
    pub hints: Hints,
    /// Its parameters' JSON schema as derived, before [`slim`], keys sorted.
    pub schema: fn() -> Map<String, Value>,
    /// Answers a call: parses the arguments into the typed parameters and
    /// runs the handler.
    pub run: Run,
}

impl Tool {
    /// Returns the parameters' schema as a caller reads it ([`slim`]), keys
    /// sorted.
    #[must_use]
    pub fn input_schema(&self) -> Map<String, Value> {
        sorted_map(slim((self.schema)()))
    }
}

/// Returns the catalog tool a name names.
///
/// # Arguments
///
/// * `name` - The tool's name.
#[must_use]
pub fn tool(name: &str) -> Option<&'static Tool> {
    TOOLS.iter().find(|t| t.name == name)
}

/// Reads a call's arguments into a tool's typed parameters.
///
/// # Arguments
///
/// * `args` - The arguments as sent.
///
/// # Errors
///
/// A refusal starting with [`DESERIALIZE_PREFIX`], as the MCP SDK words
/// one, naming the first argument the schema does not admit ([`misfit`])
/// and saying what did not read.
pub fn parse<P: serde::de::DeserializeOwned + JsonSchema>(
    args: &Map<String, Value>,
) -> Result<P, Failure> {
    serde_json::from_value(Value::Object(args.clone())).map_err(|e| {
        let field =
            misfit(&schema::<P>(), args).map_or_else(String::new, |f| format!(" field `{f}`:"));
        Failure::asked(format!("{DESERIALIZE_PREFIX}{field} {e}"))
    })
}

/// Returns a parameters type's JSON schema as derived.
///
/// It is JSON Schema 2020-12, without the root's title and description (the
/// type's name and rustdoc), its keys sorted at every level whatever order
/// the JSON map keeps.
#[must_use]
pub fn schema<P: JsonSchema>() -> Map<String, Value> {
    let root = schemars::generate::SchemaSettings::draft2020_12()
        .into_generator()
        .into_root_schema_for::<P>();
    let mut object = match serde_json::to_value(root) {
        Ok(Value::Object(object)) => object,
        Ok(_) | Err(_) => Map::new(),
    };
    object.remove("title");
    object.remove("description");
    sorted_map(object)
}

/// Returns a JSON object with its keys sorted at every level.
///
/// # Arguments
///
/// * `object` - The object, its keys in any order.
fn sorted_map(object: Map<String, Value>) -> Map<String, Value> {
    let mut entries: Vec<(String, Value)> = object.into_iter().collect();
    entries.sort_by(|a, b| a.0.cmp(&b.0));
    entries.into_iter().map(|(k, v)| (k, sorted(v))).collect()
}

/// Returns a JSON value with every object's keys sorted ([`sorted_map`]).
///
/// # Arguments
///
/// * `value` - The value.
fn sorted(value: Value) -> Value {
    match value {
        Value::Object(object) => Value::Object(sorted_map(object)),
        Value::Array(items) => Value::Array(items.into_iter().map(sorted).collect()),
        other => other,
    }
}

/// Strips schema noise a caller never needs.
///
/// Gone are the draft URL, integer formats, non-negativity bounds (every
/// count documents its own default and maximum), the `null` alternative
/// schemars adds to an optional parameter's type or enum (leaving the
/// parameter out is how a caller says null), and `additionalProperties:
/// false`, which every parameter struct enforces at the boundary through
/// `deny_unknown_fields` with an error that names the field. An enum
/// parameter's `$defs` entry is written into the parameter itself, with the
/// parameter's own description, so a caller reads its choices in place
/// rather than following a `$ref`.
///
/// # Arguments
///
/// * `schema` - The schema as derived.
#[must_use]
pub fn slim(mut schema: Map<String, Value>) -> Map<String, Value> {
    schema.remove("$schema");
    schema.remove("additionalProperties");
    let defs = match schema.remove("$defs") {
        Some(Value::Object(defs)) => defs,
        _ => Map::new(),
    };
    if let Some(Value::Object(props)) = schema.get_mut("properties") {
        for p in props.values_mut() {
            if let Value::Object(o) = p {
                slim_property(o, &defs);
            }
        }
    }
    if !defs.is_empty()
        && Value::Object(schema.clone())
            .to_string()
            .contains("\"$ref\"")
    {
        schema.insert("$defs".to_owned(), Value::Object(defs));
    }
    schema
}

/// Slims one parameter's schema in place ([`slim`]).
///
/// # Arguments
///
/// * `o` - The parameter's schema.
/// * `defs` - The schema's `$defs`, for an enum parameter's `$ref`.
fn slim_property(o: &mut Map<String, Value>, defs: &Map<String, Value>) {
    o.remove("format");
    o.remove("minimum");
    if let Some(Value::Array(any)) = o.get("anyOf") {
        let mut rest = any.iter().filter(|s| s.get("type") != Some(&"null".into()));
        if let (Some(Value::Object(only)), None) = (rest.next(), rest.next()) {
            let only = only.clone();
            o.remove("anyOf");
            o.extend(only);
        }
    }
    let inlined = o
        .get("$ref")
        .and_then(Value::as_str)
        .and_then(|r| r.strip_prefix("#/$defs/"))
        .and_then(|name| defs.get(name))
        .and_then(Value::as_object)
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
        Some(Value::Array(kinds)) => {
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

/// The tools the server keeps, each with why it is not in the catalog.
pub const SERVER_ONLY: &[(&str, &str)] = &[
    ("binary_info", "it lists the resources the MCP server holds"),
    (
        "decompile_batch",
        "with out it writes the C file or mod SDK through the MCP server's output root and exporters, and one tool takes both forms",
    ),
    ("fetch_pdb", "it reaches a symbol server over the network"),
    (
        "live_attach",
        "it reads another process through the OS (Windows)",
    ),
    (
        "live_detach",
        "it reads another process through the OS (Windows)",
    ),
    (
        "live_instances",
        "it reads another process through the OS (Windows)",
    ),
    (
        "live_modules",
        "it reads another process through the OS (Windows)",
    ),
    (
        "live_object",
        "it reads another process through the OS (Windows)",
    ),
    (
        "live_read",
        "it reads another process through the OS (Windows)",
    ),
    (
        "live_scan",
        "it reads another process through the OS (Windows)",
    ),
    (
        "live_watch",
        "it reads another process through the OS (Windows)",
    ),
    (
        "load_binary",
        "it reads a file a path names into the session",
    ),
    ("load_project", "it reads a project file into the session"),
    ("reload", "it restarts the MCP server's process"),
    (
        "save_project",
        "it writes a project file under the output root",
    ),
];

/// Returns the refusal a face without the MCP server answers a call of a
/// tool only the server runs: the tool by name and why ([`SERVER_ONLY`]).
///
/// # Arguments
///
/// * `name` - The tool's name, as the caller called it.
///
/// # Returns
///
/// `None` when the server keeps no tool of that name.
#[must_use]
pub fn server_only(name: &str) -> Option<Failure> {
    let (kept, why) = SERVER_ONLY.iter().find(|(kept, _)| *kept == name)?;
    Some(Failure::asked(format!("{kept} is not run here: {why}")))
}

/// Builds a catalog row whose schema, parser and handler read one
/// parameters type, the handler named as the tool; its hints are [`READS`]
/// unless given.
macro_rules! row {
    ($name:ident, $params:ident, $effects:expr, $description:literal) => {
        row!($name, $params, $effects, READS, $description)
    };
    ($name:ident, $params:ident, $effects:expr, $hints:expr, $description:literal) => {
        Tool {
            name: stringify!($name),
            description: $description,
            effects: $effects,
            hints: $hints,
            schema: schema::<params::$params>,
            run: |h, args| $name(h, &parse::<params::$params>(&args)?),
        }
    };
}

/// Every tool both faces list and run, in name order.
pub const TOOLS: &[Tool] = &[
    row!(
        annotations,
        AnnotationsParams,
        &[],
        "List the names, findings and open questions (comments opening with ?) added this session, paged. Use it to resume work; not for binary symbols (use symbols) or user types (use types)."
    ),
    row!(
        callgraph,
        CallgraphParams,
        &[],
        "Draw a function's call graph as mermaid: callees, or callers with callers=true; imports are leaves and a %% line counts nodes cut by max_nodes. Not for one path (use reaches) or a caller list (use xrefs)."
    ),
    row!(
        cfg,
        CfgParams,
        &[],
        "Draw a function's control-flow graph as mermaid: blocks and successor edges, 300 blocks a page, a %% line when cut. Not for reading logic (use decompile) or a block table (use function)."
    ),
    row!(
        class_layout,
        ClassLayoutParams,
        &[Effect::ChangesSession],
        EDITS,
        "Infer a C++ class's fields, methods and vftable from how its methods use the object: offset, width, reads, writes; unnamed slots hint names their vtable family agrees on. For a known layout use set_type. apply=Name saves it as a struct (dry run until dry_run=false)."
    ),
    row!(
        decompile,
        DecompileParams,
        &[],
        "Decompile one function to pseudo-C. Locals are local_N/arg_N (local_N: N hex bytes below frame base, x86 entry sp-word (rbp-N after push rbp; mov rbp,rsp), arm entry sp; higher N, lower address; local_mN: N bytes above); /* asm */: unmodeled code. Header: what was checked (proved vs lift: equal to lift, 1 emulator sample), `// warn:` what is wrong. Use function_summary first."
    ),
    row!(
        disassemble,
        DisassembleParams,
        &[],
        "Disassemble count instructions from any address as `va text` rows. Use it for a few instructions or code outside functions; for a whole function use disassemble_function. Fails if unmapped."
    ),
    row!(
        disassemble_function,
        DisassembleFunctionParams,
        &[],
        "Disassemble a whole function by blocks, with `L_<addr>:` labels and named call targets, CIL for .NET. Use it when exact instructions matter; for C use decompile, for a few instructions disassemble."
    ),
    row!(
        entropy,
        EntropyParams,
        &[],
        "Find packed, compressed or encrypted data: chunks at or above threshold bits/byte, as `off va len entropy` rows, at most 200, paged. To name the packer query borer://protection instead."
    ),
    row!(
        find_crypto_constants,
        CryptoParams,
        &[],
        "Find crypto constants and tables (AES, SHA, MD5, CRC-32, ChaCha, Blowfish, FNV, Base64) and hashed API names as `va section algorithm` rows, paged. Use it to locate crypto code, then xrefs a hit; not for strings (use strings)."
    ),
    row!(
        find_function_by_string,
        FindFunctionByStringParams,
        &[],
        "Find the functions whose strings contain a text, case-insensitively: a numbered legend, `entry name: 1 2` rows, and, on a miss, texts built at run time as `built_by written_at text` rows."
    ),
    row!(
        function,
        FunctionDetailParams,
        &[],
        "Show one function's raw facts: range, counts, callers, callees and block table (`start size term successors`), 300 blocks a page. Not for a readable triage (use function_summary)."
    ),
    row!(
        function_strings,
        FunctionParams,
        &[],
        "List the string literals one function references as `site string_va text` rows, at most 100. Not for finding a text's functions (use find_function_by_string)."
    ),
    row!(
        function_summary,
        FunctionParams,
        &[],
        "Triage one function in one call: shape, loops, jump tables, callers, callees, strings and data, then `# next:` lines. Use it before decompile; for the raw block table use function."
    ),
    row!(
        functions,
        FunctionsParams,
        &[],
        "List discovered functions as `entry size blocks instrs callers callees src name` rows, paged; filter on name or entry hex, sort=size for the largest. Not for imports (use symbols)."
    ),
    row!(
        hexdump,
        HexdumpParams,
        &[],
        "Hexdump raw bytes at an address as `address hex |ascii|` rows; a range past mapped bytes shows what is there. Not for typed values (use read), text (use strings) or a live process (live_read)."
    ),
    row!(
        query,
        QueryParams,
        &[Effect::ReadsFiles],
        "Read a borer:// resource (triage, taint, emulate, solve, grep...) for hosts without MCP resources; same answer as resources/read. Use it for analyses no tool has; borer://help lists them, !offset=N!limit=N pages."
    ),
    row!(
        reaches,
        ReachesParams,
        &[],
        "Find the shortest call chain from one function to another or to an import, or say none exists within depth. Not for the whole neighbourhood (use callgraph) or direct callers (use xrefs)."
    ),
    row!(
        read,
        ReadParams,
        &[],
        "Read typed values (kind) as `va value` rows, or a user type (type) one row per field, pointers named; stops at the first unmapped byte. Not for raw bytes (use hexdump) or a live process (live_read)."
    ),
    row!(
        script,
        ScriptParams,
        &[Effect::ReadsFiles, Effect::ChangesSession],
        Hints {
            idempotent: false,
            ..EDITS
        },
        "Run a sandboxed Rhai script on a snapshot of the program: query(uri) and rows(uri) read any resource. Use it when no single tool answers. Proposed names apply only with dry_run=false; a failed script applies nothing."
    ),
    row!(
        search,
        SearchParams,
        &[],
        "Search every byte of the file for hex (?? or 4? wildcards, 4096 bytes max), or text with kind=text, as `function: va ...` rows, paged. Not for listing strings (use strings)."
    ),
    row!(
        set_comment,
        SetCommentParams,
        &[Effect::ChangesSession],
        EDITS,
        "Comment an address in the session overlay, never the binary; a comment opening with ? is an open question. To name it use set_name. Dry run until dry_run=false; save_project keeps it."
    ),
    row!(
        set_name,
        SetNameParams,
        &[Effect::ChangesSession],
        EDITS,
        "Name a function or data global in the session overlay, never the binary; names=[addr=name,...] renames many, checked first. A taken name needs force=true. Dry run until dry_run=false."
    ),
    row!(
        set_type,
        SetTypeParams,
        &[Effect::ChangesSession],
        EDITS,
        "Define a struct, enum or typedef, name fields of a struct or class_layout class, or apply a type at an address so decompile names its fields; at a function, type sets the prototype. Checked first; dry run until dry_run=false."
    ),
    row!(
        strings,
        StringsParams,
        &[],
        "List printable ASCII and UTF-16LE strings as `va len enc text` rows, paged, skipping bytes of code. Not for the code using one (use find_function_by_string)."
    ),
    row!(
        symbols,
        SymbolsParams,
        &[],
        "List imports, exports, forwards, locals and data as demangled `kind addr name` rows by module, paged. Not for discovered code (use functions) or call sites (use xrefs)."
    ),
    row!(
        types,
        TypesParams,
        &[],
        "List user-defined types and where each is applied, paged. Not for defining one (use set_type) or names and comments (use annotations)."
    ),
    row!(
        xrefs,
        XrefsParams,
        &[],
        "List references to an address or name, one row per function, paged; an import lists calls through its slot, `Class+0x24` who touches that field. Not for call paths (use reaches)."
    ),
];

#[cfg(test)]
mod tests {
    use super::{SERVER_ONLY, TOOLS, params::QueryParams, parse, server_only};

    /// A call of a tool the server keeps is refused by name with why, and
    /// a catalog tool is not one.
    ///
    /// # Panics
    ///
    /// When a server tool is not refused, or a catalog tool is.
    #[test]
    fn a_server_tool_is_refused_by_name() {
        for (kept, why) in SERVER_ONLY {
            let refused = server_only(kept).expect("the server's");
            assert_eq!(refused.cause, super::Cause::Asked);
            assert_eq!(refused.message, format!("{kept} is not run here: {why}"));
        }
        assert!(TOOLS.iter().all(|t| server_only(t.name).is_none()));
    }

    /// The rows are named once each, in name order, and no tool is both the
    /// catalog's and the server's.
    ///
    /// # Panics
    ///
    /// When two rows share a name, the rows are out of order, or a name is
    /// in both tables.
    #[test]
    fn every_tool_is_named_once() {
        let names: Vec<&str> = TOOLS.iter().map(|t| t.name).collect();
        assert!(names.windows(2).all(|w| w[0] < w[1]), "{names:?}");
        assert!(
            SERVER_ONLY.iter().all(|(kept, _)| !names.contains(kept)),
            "{SERVER_ONLY:?}"
        );
    }

    /// Arguments that do not read are refused in the words the MCP SDK
    /// uses, naming what did not read.
    ///
    /// # Panics
    ///
    /// When a call without its URI reads, or the refusal says otherwise.
    #[test]
    fn arguments_that_do_not_read_are_refused() {
        let refused = parse::<QueryParams>(&serde_json::Map::new()).expect_err("no uri");
        assert_eq!(
            refused.message,
            "failed to deserialize parameters: missing field `uri`"
        );
    }

    /// Every schema the catalog gives has its keys sorted at every level.
    ///
    /// So it has whichever order the JSON map keeps: `cargo test -p
    /// borer-front --features serde_json/preserve_order` runs this with the
    /// insertion order the app's build keeps.
    ///
    /// # Panics
    ///
    /// When an object's keys come out of order.
    #[test]
    fn every_schema_lists_its_keys_in_order() {
        fn ordered(value: &serde_json::Value) -> bool {
            match value {
                serde_json::Value::Object(o) => {
                    o.keys().zip(o.keys().skip(1)).all(|(a, b)| a < b) && o.values().all(ordered)
                }
                serde_json::Value::Array(items) => items.iter().all(ordered),
                _ => true,
            }
        }
        for t in TOOLS {
            assert!(
                ordered(&serde_json::Value::Object((t.schema)())),
                "{}",
                t.name
            );
            assert!(
                ordered(&serde_json::Value::Object(t.input_schema())),
                "{}",
                t.name
            );
        }
    }

    /// An edit goes through the face's seam: a face that holds proposals
    /// returns the plan and leaves its names as they were.
    ///
    /// # Panics
    ///
    /// When the plan is not made, says nothing, or the names change.
    #[test]
    fn an_edit_is_planned_through_the_seam() {
        use std::sync::Arc;

        use borer_engine::analysis::Analysis;
        use borer_engine::analysis::edit::{Edit, Force};
        use borer_engine::answer::Need;
        use borer_engine::program::{Arch, Feature, Program, Section};

        use super::{Apply, Loaded, snapshot};
        let text = Section::mapped(".text", 0x1000, 0, 0x10, false, true);
        let program = Program::raw(vec![0xc3; 0x10], Arch::X86_64, 0, Some(0x1000), vec![text]);
        let analysis = Arc::new(Analysis::compute(&program));
        let plain = Loaded {
            program: Arc::new(program),
            analysis,
            overlay: Arc::default(),
        };
        let s = snapshot(&plain, Need::Code(Feature::Discover)).expect("a snapshot");
        let edits = [Edit::Name {
            at: 0x1000,
            name: "start".to_owned(),
        }];
        let (plan, _) = s
            .edit(&edits, Force::Refuse, Apply::Commit)
            .expect("planned");
        assert!(!plan.lines().is_empty());
        assert!(plain.overlay.names.is_empty());
    }

    /// Every edit tool, applied on a face that holds proposals, says the
    /// edit was proposed and not applied.
    ///
    /// It never says it was applied, it hands the face the plan, and it
    /// changes none of the names the face reads.
    ///
    /// # Panics
    ///
    /// When an answer reads as committed, the face keeps no plan, or a name
    /// lands.
    #[test]
    fn an_applied_edit_is_a_proposal_on_a_face_that_keeps_plans() {
        use std::cell::RefCell;
        use std::sync::Arc;

        use borer_engine::analysis::edit::{Edit, Force, Plan};
        use borer_engine::analysis::{Analysis, Overlay};
        use borer_engine::answer::Need;
        use borer_engine::program::{Arch, Program, Section};

        use super::{Apply, Edited, Failure, Held, Loaded, Snapshot, View, tool};

        /// The plain face, keeping each plan an edit tool hands it.
        struct Proposing {
            /// What it holds.
            loaded: Loaded,
            /// The plans kept, in the order they came.
            kept: RefCell<Vec<Plan>>,
        }
        impl Held for Proposing {
            fn view(&self, need: Need) -> Option<Result<View, String>> {
                self.loaded.view(need)
            }
            fn user_overlay(&self) -> Arc<Overlay> {
                self.loaded.user_overlay()
            }
            fn edit(
                &self,
                s: &Snapshot<'_>,
                edits: &[Edit],
                force: Force,
                apply: Apply,
            ) -> anyhow::Result<Edited> {
                let edited = self.loaded.edit(s, edits, force, apply)?;
                self.kept.borrow_mut().push(edited.0.clone());
                Ok(edited)
            }
            fn querier(&self) -> borer_engine::script::Query {
                self.loaded.querier()
            }
            fn read(&self, uri: &str) -> Result<String, Failure> {
                self.loaded.read(uri)
            }
        }
        let mut code = vec![0xc3; 0x10];
        // ASM: mov dword [rcx+0x24], 5; ret
        code[..8].copy_from_slice(&[0xc7, 0x41, 0x24, 0x05, 0x00, 0x00, 0x00, 0xc3]);
        let text = Section::mapped(".text", 0x1000, 0, 0x10, false, true);
        let program = Program::raw(code, Arch::X86_64, 0, Some(0x1000), vec![text]);
        let mut overlay = Overlay::default();
        overlay.names.insert(0x1000, "Foo::Set".to_owned());
        let face = Proposing {
            loaded: Loaded {
                analysis: Arc::new(Analysis::compute(&program)),
                program: Arc::new(program),
                overlay: Arc::new(overlay),
            },
            kept: RefCell::new(Vec::new()),
        };
        let calls = [
            (
                "set_name",
                serde_json::json!({"address": "0x1000", "name": "start"}),
            ),
            (
                "set_name",
                serde_json::json!({"names": ["0x1000=a", "0x1008=b"]}),
            ),
            (
                "set_comment",
                serde_json::json!({"address": "0x1000", "comment": "entry"}),
            ),
            (
                "set_type",
                serde_json::json!({"name": "S", "fields": ["0:a:u32"]}),
            ),
            (
                "set_type",
                serde_json::json!({"type": "struct D { int x; };"}),
            ),
            (
                "class_layout",
                serde_json::json!({"class": "Foo", "apply": "FooS"}),
            ),
            (
                "script",
                serde_json::json!({"code": "rename(0x1000, \"s\");"}),
            ),
        ];
        for (name, args) in calls {
            let t = tool(name).expect("a catalog tool");
            let mut args = args.as_object().cloned().unwrap_or_default();
            let dry = (t.run)(&face, args.clone()).expect("planned");
            args.insert("dry_run".to_owned(), false.into());
            let kept = face.kept.borrow().len();
            let applied = (t.run)(&face, args).expect("proposed");
            assert!(dry.contains("dry-run"), "{name}: {dry}");
            assert!(
                applied.contains("proposed, not applied: waits for the person to accept:"),
                "{name}: {applied}"
            );
            assert!(!applied.contains("# applied"), "{name}: {applied}");
            assert_eq!(face.kept.borrow().len(), kept + 1, "{name}");
        }
        let names =
            (tool("annotations").expect("a catalog tool").run)(&face, serde_json::Map::new());
        assert!(names.is_ok_and(|n| !n.contains("start")));
    }

    /// A face without the server's session answers what the engine
    /// answers and refuses a resource only the server has by name, with
    /// why, and sends the reader nowhere it cannot go.
    ///
    /// # Panics
    ///
    /// When the engine's answer is refused or a server resource answers.
    #[test]
    fn query_refuses_the_server_resources_by_name() {
        use std::sync::Arc;

        use borer_engine::analysis::Analysis;
        use borer_engine::program::{Arch, Program, Section};

        use super::{Cause, Loaded, ask};
        let text = Section::mapped(".text", 0x1000, 0, 0x10, false, true);
        let program = Program::raw(vec![0xc3; 0x10], Arch::X86_64, 0, Some(0x1000), vec![text]);
        let plain = Loaded {
            analysis: Arc::new(Analysis::compute(&program)),
            program: Arc::new(program),
            overlay: Arc::default(),
        };
        assert!(ask(&plain, "borer://disasm/0x1000").is_ok());
        for uri in ["borer://help", "borer://grep/main"] {
            let refused = ask(&plain, uri).expect_err("the server's");
            assert_eq!(refused.cause, Cause::Asked, "{uri}");
            assert!(refused.message.contains(" is not answered here: "), "{uri}");
            assert!(!refused.message.contains("borer://help lists"), "{uri}");
        }
        assert_eq!(
            ask(&plain, "borer://nope").expect_err("no such").cause,
            Cause::Missing
        );
    }
}
