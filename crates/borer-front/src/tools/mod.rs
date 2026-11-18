//! The tool catalog: the tools both faces list and run.
//!
//! The faces are the MCP server over stdio and the app's chat. Each tool has
//! its name, typed parameters, caps and defaults (in the parameters'
//! schema), description, effects and the handler that answers it over what a
//! front end holds ([`Held`]).
//!
//! The server builds its tool list, schemas and dispatch for these from
//! [`TOOLS`]; the app builds its model's tool list from the same rows
//! ([`Tool::input_schema`]) and runs a call with [`Tool::run`], so a tool
//! reads the same, takes the same arguments and answers the same bytes
//! either way. The tools that need what only the server has stay the
//! server's, each named in [`SERVER_ONLY`] with its reason.
//!
//! What every answer passes through on its way out is split by owner: the
//! byte cut ([`crate::budget::cut_to`]) is shared, one function for both faces at
//! each face's own budget; the `# since=` memory and the `# evidence:`
//! ledger belong to the server's session, keyed by its requests, and stay
//! there.

mod bytes;
mod code;
mod held;
pub mod params;

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
pub use held::{Body, Cause, Failure, Held, HeldExt, NO_BINARY, fault_text, guarded};
use params::DESERIALIZE_PREFIX;

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

/// Answers one call: what the front end holds and the call's arguments.
pub type Run = fn(&dyn Held, Map<String, Value>) -> Result<String, Failure>;

/// One tool both faces list and run.
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
    /// Its parameters' JSON schema as derived, before [`slim`].
    pub schema: fn() -> Map<String, Value>,
    /// Answers a call: parses the arguments into the typed parameters and
    /// runs the handler.
    pub run: Run,
}

impl Tool {
    /// Returns the parameters' schema as a caller reads it ([`slim`]).
    #[must_use]
    pub fn input_schema(&self) -> Map<String, Value> {
        slim((self.schema)())
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
/// A refusal starting with [`DESERIALIZE_PREFIX`] and saying what did not
/// read, as the MCP SDK words one.
pub fn parse<P: serde::de::DeserializeOwned>(args: Map<String, Value>) -> Result<P, Failure> {
    serde_json::from_value(Value::Object(args))
        .map_err(|e| Failure::asked(format!("{DESERIALIZE_PREFIX} {e}")))
}

/// Returns a parameters type's JSON schema as derived: JSON Schema 2020-12,
/// without the root's title and description (the type's name and rustdoc).
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
    object
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
    ("binary_info", "reads the resource catalog the server holds"),
    (
        "class_layout",
        "changes the session; moves with the edit tools",
    ),
    (
        "decompile_batch",
        "writes files under the server's output root",
    ),
    ("fetch_pdb", "reaches a symbol server over the network"),
    (
        "live_attach",
        "reads another process through the OS (Windows)",
    ),
    (
        "live_detach",
        "reads another process through the OS (Windows)",
    ),
    (
        "live_instances",
        "reads another process through the OS (Windows)",
    ),
    (
        "live_modules",
        "reads another process through the OS (Windows)",
    ),
    (
        "live_object",
        "reads another process through the OS (Windows)",
    ),
    (
        "live_read",
        "reads another process through the OS (Windows)",
    ),
    (
        "live_scan",
        "reads another process through the OS (Windows)",
    ),
    (
        "live_watch",
        "reads another process through the OS (Windows)",
    ),
    ("load_binary", "reads a file a path names into the session"),
    ("load_project", "reads a project file into the session"),
    ("reload", "restarts the server process"),
    (
        "save_project",
        "writes a project file under the output root",
    ),
    (
        "script",
        "applies its proposals to the session; moves with the edit tools",
    ),
    (
        "set_comment",
        "changes the session; moves with the edit tools",
    ),
    ("set_name", "changes the session; moves with the edit tools"),
    ("set_type", "changes the session; moves with the edit tools"),
];

/// Every tool both faces list and run, in name order.
pub const TOOLS: &[Tool] = &[
    Tool {
        name: "annotations",
        description: "List the names, findings and open questions (comments opening with ?) added this session, paged. Use it to resume work; not for binary symbols (use symbols) or user types (use types).",
        effects: &[],
        hints: READS,
        schema: schema::<params::AnnotationsParams>,
        run: |h, args| annotations(h, &parse(args)?),
    },
    Tool {
        name: "callgraph",
        description: "Draw a function's call graph as mermaid: callees, or callers with callers=true; imports are leaves and a %% line counts nodes cut by max_nodes. Not for one path (use reaches) or a caller list (use xrefs).",
        effects: &[],
        hints: READS,
        schema: schema::<params::CallgraphParams>,
        run: |h, args| callgraph(h, &parse(args)?),
    },
    Tool {
        name: "cfg",
        description: "Draw a function's control-flow graph as mermaid: blocks and successor edges, 300 blocks a page, a %% line when cut. Not for reading logic (use decompile) or a block table (use function).",
        effects: &[],
        hints: READS,
        schema: schema::<params::CfgParams>,
        run: |h, args| cfg(h, &parse(args)?),
    },
    Tool {
        name: "decompile",
        description: "Decompile one function to pseudo-C. Locals are local_N/arg_N (local_N: N hex bytes below frame base, x86 entry sp-word (rbp-N after push rbp; mov rbp,rsp), arm entry sp; higher N, lower address; local_mN: N bytes above); /* asm */: unmodeled code. Header: what was checked (proved vs lift: equal to lift, 1 emulator sample), `// warn:` what is wrong. Use function_summary first.",
        effects: &[],
        hints: READS,
        schema: schema::<params::DecompileParams>,
        run: |h, args| decompile(h, &parse(args)?),
    },
    Tool {
        name: "disassemble",
        description: "Disassemble count instructions from any address as `va text` rows. Use it for a few instructions or code outside functions; for a whole function use disassemble_function. Fails if unmapped.",
        effects: &[],
        hints: READS,
        schema: schema::<params::DisassembleParams>,
        run: |h, args| disassemble(h, &parse(args)?),
    },
    Tool {
        name: "disassemble_function",
        description: "Disassemble a whole function by blocks, with `L_<addr>:` labels and named call targets, CIL for .NET. Use it when exact instructions matter; for C use decompile, for a few instructions disassemble.",
        effects: &[],
        hints: READS,
        schema: schema::<params::DisassembleFunctionParams>,
        run: |h, args| disassemble_function(h, &parse(args)?),
    },
    Tool {
        name: "entropy",
        description: "Find packed, compressed or encrypted data: chunks at or above threshold bits/byte, as `off va len entropy` rows, at most 200, paged. To name the packer query borer://protection instead.",
        effects: &[],
        hints: READS,
        schema: schema::<params::EntropyParams>,
        run: |h, args| entropy(h, &parse(args)?),
    },
    Tool {
        name: "find_crypto_constants",
        description: "Find crypto constants and tables (AES, SHA, MD5, CRC-32, ChaCha, Blowfish, FNV, Base64) and hashed API names as `va section algorithm` rows, paged. Use it to locate crypto code, then xrefs a hit; not for strings (use strings).",
        effects: &[],
        hints: READS,
        schema: schema::<params::CryptoParams>,
        run: |h, args| find_crypto_constants(h, &parse(args)?),
    },
    Tool {
        name: "find_function_by_string",
        description: "Find the functions whose strings contain a text, case-insensitively: a numbered legend, `entry name: 1 2` rows, and, on a miss, texts built at run time as `built_by written_at text` rows.",
        effects: &[],
        hints: READS,
        schema: schema::<params::FindFunctionByStringParams>,
        run: |h, args| find_function_by_string(h, &parse(args)?),
    },
    Tool {
        name: "function",
        description: "Show one function's raw facts: range, counts, callers, callees and block table (`start size term successors`), 300 blocks a page. Not for a readable triage (use function_summary).",
        effects: &[],
        hints: READS,
        schema: schema::<params::FunctionDetailParams>,
        run: |h, args| function(h, &parse(args)?),
    },
    Tool {
        name: "function_strings",
        description: "List the string literals one function references as `site string_va text` rows, at most 100. Not for finding a text's functions (use find_function_by_string).",
        effects: &[],
        hints: READS,
        schema: schema::<params::FunctionParams>,
        run: |h, args| function_strings(h, &parse(args)?),
    },
    Tool {
        name: "function_summary",
        description: "Triage one function in one call: shape, loops, jump tables, callers, callees, strings and data, then `# next:` lines. Use it before decompile; for the raw block table use function.",
        effects: &[],
        hints: READS,
        schema: schema::<params::FunctionParams>,
        run: |h, args| function_summary(h, &parse(args)?),
    },
    Tool {
        name: "functions",
        description: "List discovered functions as `entry size blocks instrs callers callees src name` rows, paged; filter on name or entry hex, sort=size for the largest. Not for imports (use symbols).",
        effects: &[],
        hints: READS,
        schema: schema::<params::FunctionsParams>,
        run: |h, args| functions(h, &parse(args)?),
    },
    Tool {
        name: "hexdump",
        description: "Hexdump raw bytes at an address as `address hex |ascii|` rows; a range past mapped bytes shows what is there. Not for typed values (use read), text (use strings) or a live process (live_read).",
        effects: &[],
        hints: READS,
        schema: schema::<params::HexdumpParams>,
        run: |h, args| hexdump(h, &parse(args)?),
    },
    Tool {
        name: "query",
        description: "Read a borer:// resource (triage, taint, emulate, solve, grep...) for hosts without MCP resources; same answer as resources/read. Use it for analyses no tool has; borer://help lists them, !offset=N!limit=N pages.",
        effects: &[Effect::ReadsFiles],
        hints: READS,
        schema: schema::<params::QueryParams>,
        run: |h, args| query(h, &parse(args)?),
    },
    Tool {
        name: "reaches",
        description: "Find the shortest call chain from one function to another or to an import, or say none exists within depth. Not for the whole neighbourhood (use callgraph) or direct callers (use xrefs).",
        effects: &[],
        hints: READS,
        schema: schema::<params::ReachesParams>,
        run: |h, args| reaches(h, &parse(args)?),
    },
    Tool {
        name: "read",
        description: "Read typed values (kind) as `va value` rows, or a user type (type) one row per field, pointers named; stops at the first unmapped byte. Not for raw bytes (use hexdump) or a live process (live_read).",
        effects: &[],
        hints: READS,
        schema: schema::<params::ReadParams>,
        run: |h, args| read(h, &parse(args)?),
    },
    Tool {
        name: "search",
        description: "Search every byte of the file for a hex pattern with ?? wildcards, or text with kind=text, as `function: va ...` rows, paged. Not for listing strings (use strings).",
        effects: &[],
        hints: READS,
        schema: schema::<params::SearchParams>,
        run: |h, args| search(h, &parse(args)?),
    },
    Tool {
        name: "strings",
        description: "List printable ASCII and UTF-16LE strings as `va len enc text` rows, paged, skipping bytes of code. Not for the code using one (use find_function_by_string).",
        effects: &[],
        hints: READS,
        schema: schema::<params::StringsParams>,
        run: |h, args| strings(h, &parse(args)?),
    },
    Tool {
        name: "symbols",
        description: "List imports, exports, forwards, locals and data as demangled `kind addr name` rows by module, paged. Not for discovered code (use functions) or call sites (use xrefs).",
        effects: &[],
        hints: READS,
        schema: schema::<params::SymbolsParams>,
        run: |h, args| symbols(h, &parse(args)?),
    },
    Tool {
        name: "types",
        description: "List user-defined types and where each is applied, paged. Not for defining one (use set_type) or names and comments (use annotations).",
        effects: &[],
        hints: READS,
        schema: schema::<params::TypesParams>,
        run: |h, args| types(h, &parse(args)?),
    },
    Tool {
        name: "xrefs",
        description: "List references to an address or name, one row per function, paged; an import lists calls through its slot, `Class+0x24` who touches that field. Not for call paths (use reaches).",
        effects: &[],
        hints: READS,
        schema: schema::<params::XrefsParams>,
        run: |h, args| xrefs(h, &parse(args)?),
    },
];

#[cfg(test)]
mod tests {
    use super::{SERVER_ONLY, TOOLS, params::QueryParams, parse};

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
        let refused = parse::<QueryParams>(serde_json::Map::new()).expect_err("no uri");
        assert_eq!(
            refused.message,
            "failed to deserialize parameters: missing field `uri`"
        );
    }
}
