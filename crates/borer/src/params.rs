//! Tool and prompt parameters: what each MCP call accepts, as the JSON
//! schema an agent reads before it calls.

use borer_engine::analysis::render;
use borer_engine::program;
use rmcp::{ErrorData, schemars};

use crate::errors::err_params;

/// What `read` and `live_read` decode the bytes as.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default, serde::Deserialize, schemars::JsonSchema)]
#[serde(rename_all = "lowercase")]
#[schemars(transform = names_only)]
pub(crate) enum ReadKind {
    /// One unsigned byte.
    #[serde(alias = "byte")]
    U8,
    /// An unsigned 16-bit word.
    #[serde(alias = "word")]
    U16,
    /// An unsigned 32-bit word.
    #[serde(alias = "dword")]
    U32,
    /// An unsigned 64-bit word.
    #[default]
    #[serde(alias = "qword")]
    U64,
    /// A signed byte.
    I8,
    /// A signed 16-bit word.
    I16,
    /// A signed 32-bit word.
    #[serde(alias = "int")]
    I32,
    /// A signed 64-bit word.
    I64,
    /// A single-precision float.
    #[serde(alias = "float")]
    F32,
    /// A double-precision float.
    #[serde(alias = "double")]
    F64,
    /// A pointer of the image's width, with what it points at.
    #[serde(alias = "pointer")]
    Ptr,
    /// A NUL-terminated byte string.
    #[serde(alias = "str", alias = "string", alias = "ascii")]
    CStr,
    /// A NUL-terminated UTF-16 string.
    #[serde(alias = "utf16", alias = "wide")]
    WStr,
}

/// Folds a unit enum's schema, a `oneOf` of documented constants, into a
/// plain `enum` of its names.
///
/// A variant's rustdoc is for the code. In the schema it repeated what the
/// name already says (`u8`: "One unsigned byte."), once in every tool taking
/// the enum, and tools/list is read in full by every agent that connects.
/// A schema with any variant that is not a bare constant is left as it is.
///
/// # Arguments
///
/// * `schema` - The derived schema, rewritten in place.
fn names_only(schema: &mut schemars::Schema) {
    let Some(object) = schema.as_object_mut() else {
        return;
    };
    let Some(serde_json::Value::Array(variants)) = object.get("oneOf") else {
        return;
    };
    let names: Option<Vec<serde_json::Value>> =
        variants.iter().map(|v| v.get("const").cloned()).collect();
    if let Some(names) = names {
        object.remove("oneOf");
        object.insert("type".to_owned(), "string".into());
        object.insert("enum".to_owned(), serde_json::Value::Array(names));
    }
}

impl ReadKind {
    /// The canonical name, as the schema lists it.
    pub(crate) fn word(self) -> &'static str {
        match self {
            Self::U8 => "u8",
            Self::U16 => "u16",
            Self::U32 => "u32",
            Self::U64 => "u64",
            Self::I8 => "i8",
            Self::I16 => "i16",
            Self::I32 => "i32",
            Self::I64 => "i64",
            Self::F32 => "f32",
            Self::F64 => "f64",
            Self::Ptr => "ptr",
            Self::CStr => "cstr",
            Self::WStr => "wstr",
        }
    }
}

impl std::fmt::Display for ReadKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.word())
    }
}

impl From<ReadKind> for borer_engine::memory::Kind {
    fn from(k: ReadKind) -> Self {
        use borer_engine::memory::Kind;
        match k {
            ReadKind::U8 => Kind::U8,
            ReadKind::U16 => Kind::U16,
            ReadKind::U32 => Kind::U32,
            ReadKind::U64 => Kind::U64,
            ReadKind::I8 => Kind::I8,
            ReadKind::I16 => Kind::I16,
            ReadKind::I32 => Kind::I32,
            ReadKind::I64 => Kind::I64,
            ReadKind::F32 => Kind::F32,
            ReadKind::F64 => Kind::F64,
            ReadKind::Ptr => Kind::Ptr,
            ReadKind::CStr => Kind::CStr,
            ReadKind::WStr => Kind::WStr,
        }
    }
}

/// Which strings `strings` scans for.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default, serde::Deserialize, schemars::JsonSchema)]
#[serde(rename_all = "lowercase")]
#[schemars(transform = names_only)]
pub(crate) enum StringEncoding {
    /// Byte strings only.
    Ascii,
    /// UTF-16 strings only.
    Utf16,
    /// Both, in address order.
    #[default]
    Both,
}

impl StringEncoding {
    /// The canonical name, as the schema lists it.
    pub(crate) fn word(self) -> &'static str {
        match self {
            Self::Ascii => "ascii",
            Self::Utf16 => "utf16",
            Self::Both => "both",
        }
    }
}

impl std::fmt::Display for StringEncoding {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.word())
    }
}

/// Which symbols `symbols` lists.
#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Deserialize, schemars::JsonSchema)]
#[serde(rename_all = "lowercase")]
#[schemars(transform = names_only)]
pub(crate) enum SymbolKind {
    /// Imported functions and data.
    #[serde(alias = "imports")]
    Import,
    /// Exported functions and data.
    #[serde(alias = "exports")]
    Export,
    /// Local symbols the file names.
    #[serde(alias = "locals")]
    Local,
    /// Exports forwarded to another module (`NTDLL.RtlX`); the row names
    /// the target.
    #[serde(alias = "forwards", alias = "forwarder", alias = "forwarders")]
    Forward,
    /// Named data at an address (an applied PDB's data records).
    Data,
}

impl From<SymbolKind> for program::SymbolKind {
    fn from(k: SymbolKind) -> Self {
        match k {
            SymbolKind::Import => program::SymbolKind::Import,
            SymbolKind::Export => program::SymbolKind::Export,
            SymbolKind::Local => program::SymbolKind::Local,
            SymbolKind::Forward => program::SymbolKind::Forwarder,
            SymbolKind::Data => program::SymbolKind::Data,
        }
    }
}

/// How much of a function `decompile` returns.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default, serde::Deserialize, schemars::JsonSchema)]
#[serde(rename_all = "lowercase")]
pub(crate) enum Detail {
    /// The whole function.
    #[default]
    Full,
    /// The flow and the calls only.
    Skeleton,
}

/// What `search` looks for.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default, serde::Deserialize, schemars::JsonSchema)]
#[serde(rename_all = "lowercase")]
#[schemars(transform = names_only)]
pub(crate) enum SearchKind {
    /// Hex bytes with `??` wildcards.
    #[default]
    Bytes,
    /// A literal substring, ASCII or UTF-16.
    Text,
}

/// Parameters for `load_binary`.
#[derive(Debug, serde::Deserialize, schemars::JsonSchema)]
#[serde(deny_unknown_fields)]
pub(crate) struct LoadBinaryParams {
    /// Absolute path to the file.
    pub(crate) path: String,
    /// File offset to use as the entry instead of the header's.
    pub(crate) entry_file_offset: Option<u64>,
    /// Apply the companion PDB the debug record names (default true).
    pub(crate) pdb: Option<bool>,
    /// Raw code or a dump: map its bytes as this arch.
    pub(crate) arch: Option<RawArch>,
    /// With arch: the file's address (default 0).
    pub(crate) base: Option<String>,
    /// With arch: entry address (default first executable byte).
    pub(crate) entry: Option<String>,
    /// With arch, not base: VA@OFF:LEN[:rwx],... (max 256).
    pub(crate) regions: Option<String>,
}

/// A raw load's architecture.
///
/// Its schema carries no description of its own: the `arch` parameter's
/// says what it is, and tools/list is read in full by every agent.
#[derive(
    Debug, Clone, Copy, PartialEq, Eq, serde::Serialize, serde::Deserialize, schemars::JsonSchema,
)]
#[serde(rename_all = "lowercase")]
#[schemars(transform = names_only, description = "")]
pub(crate) enum RawArch {
    /// 32-bit x86.
    X86,
    /// x86-64.
    #[serde(alias = "x86-64", alias = "x86_64", alias = "amd64")]
    X64,
    /// AArch64.
    #[serde(alias = "aarch64")]
    Arm64,
}

impl From<RawArch> for program::Arch {
    fn from(a: RawArch) -> Self {
        match a {
            RawArch::X86 => program::Arch::X86,
            RawArch::X64 => program::Arch::X86_64,
            RawArch::Arm64 => program::Arch::Arm64,
        }
    }
}

/// Parameters for `fetch_pdb`.
#[derive(Debug, serde::Deserialize, schemars::JsonSchema)]
#[serde(deny_unknown_fields)]
pub(crate) struct FetchPdbParams {
    /// Preview only (default true); false fetches from `BORER_SYMBOL_SERVER` or Microsoft's.
    pub(crate) dry_run: Option<bool>,
}

/// Parameters for `disassemble`.
#[derive(Debug, serde::Deserialize, schemars::JsonSchema)]
#[serde(deny_unknown_fields)]
pub(crate) struct DisassembleParams {
    /// Address or a function/symbol name.
    pub(crate) address: String,
    /// Max instructions (default 32, max 256).
    pub(crate) count: Option<u32>,
    /// Add the raw-bytes column (default false).
    pub(crate) bytes: Option<bool>,
}

/// Parameters for `disassemble_function`.
#[derive(Debug, serde::Deserialize, schemars::JsonSchema)]
#[serde(deny_unknown_fields)]
pub(crate) struct DisassembleFunctionParams {
    /// Entry, any address inside it, or a name.
    pub(crate) address: String,
    /// Maximum instructions to return (default 400, max 2000).
    pub(crate) max_instrs: Option<u32>,
    /// Add the raw-bytes column (default false).
    pub(crate) bytes: Option<bool>,
}

/// Parameters for `read`.
#[derive(Debug, serde::Deserialize, schemars::JsonSchema)]
#[serde(deny_unknown_fields)]
pub(crate) struct ReadParams {
    /// Address (0x-hex or decimal), a name, or `off:<n>` for a file offset.
    pub(crate) address: String,
    /// What to decode the bytes as (default u64).
    pub(crate) kind: Option<ReadKind>,
    /// A user type instead of kind: `Rec`, `Rec[4]`, `char[16]`.
    pub(crate) r#type: Option<String>,
    /// Values to read (default 1, max 256).
    pub(crate) count: Option<u32>,
}

/// Parameters for `entropy`.
#[derive(Debug, serde::Deserialize, schemars::JsonSchema)]
#[serde(deny_unknown_fields)]
pub(crate) struct EntropyParams {
    /// Window size in bytes (default 1024, minimum 64).
    pub(crate) window: Option<u32>,
    /// Minimum bits per byte to report (default 7.2, max 8.0).
    pub(crate) threshold: Option<f64>,
    /// Regions to skip first (paging).
    pub(crate) offset: Option<u32>,
    /// Most regions listed (default 200, max 200).
    pub(crate) limit: Option<u32>,
}

/// Parameters for `find_function_by_string`.
#[derive(Debug, serde::Deserialize, schemars::JsonSchema)]
#[serde(deny_unknown_fields)]
pub(crate) struct FindFunctionByStringParams {
    /// Case-insensitive substring of the referenced string.
    #[serde(alias = "query")]
    pub(crate) filter: String,
    /// Function rows to skip first (paging).
    pub(crate) offset: Option<u32>,
    /// Max rows and legend strings (default 50, max 300).
    pub(crate) limit: Option<u32>,
}

/// Parameters for `hexdump`.
#[derive(Debug, serde::Deserialize, schemars::JsonSchema)]
#[serde(deny_unknown_fields)]
pub(crate) struct HexdumpParams {
    /// Address (0x-hex or decimal), a name, or `off:<n>` for a file offset.
    pub(crate) address: String,
    /// Number of bytes (default 64, max 4096).
    pub(crate) length: Option<u32>,
}

/// Parameters for `strings`.
#[derive(Debug, serde::Deserialize, schemars::JsonSchema)]
#[serde(deny_unknown_fields)]
pub(crate) struct StringsParams {
    /// Minimum length (default 5, min 4).
    pub(crate) min_length: Option<u32>,
    /// Case-insensitive substring filter.
    pub(crate) filter: Option<String>,
    /// Which strings to scan for (default both).
    pub(crate) encoding: Option<StringEncoding>,
    /// Matches to skip (paging).
    pub(crate) offset: Option<u32>,
    /// Max rows (default 200, max 500).
    pub(crate) limit: Option<u32>,
    /// Header only (default false).
    pub(crate) count_only: Option<bool>,
}

/// Parameters for `symbols`.
#[derive(Debug, serde::Deserialize, schemars::JsonSchema)]
#[serde(deny_unknown_fields)]
pub(crate) struct SymbolsParams {
    /// One kind of symbol only (default every kind); drops the kind column.
    pub(crate) kind: Option<SymbolKind>,
    /// Case-insensitive substring of the raw (module included) or demangled name.
    pub(crate) filter: Option<String>,
    /// Matches to skip (paging).
    pub(crate) offset: Option<u32>,
    /// Max rows (default 50, max 1000).
    pub(crate) limit: Option<u32>,
    /// Header only (default false).
    pub(crate) count_only: Option<bool>,
}

/// The order `functions` lists in.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default, serde::Deserialize, schemars::JsonSchema)]
#[serde(rename_all = "lowercase")]
pub(crate) enum FunctionSort {
    /// By entry address.
    #[default]
    Address,
    /// By size, the largest first.
    Size,
}

impl From<FunctionSort> for render::FunctionOrder {
    fn from(s: FunctionSort) -> Self {
        match s {
            FunctionSort::Address => render::FunctionOrder::Address,
            FunctionSort::Size => render::FunctionOrder::Size,
        }
    }
}

/// Parameters for `functions`.
#[derive(Debug, serde::Deserialize, schemars::JsonSchema)]
#[serde(deny_unknown_fields)]
pub(crate) struct FunctionsParams {
    /// Case-insensitive filter on name or entry hex; `thunk` or `funclet` lists what is otherwise left out.
    pub(crate) filter: Option<String>,
    /// `address` (default) or `size` for the largest first.
    pub(crate) sort: Option<FunctionSort>,
    /// Matches to skip (paging).
    pub(crate) offset: Option<u32>,
    /// Max rows (default 50, max 300).
    pub(crate) limit: Option<u32>,
    /// Header only (default false).
    pub(crate) count_only: Option<bool>,
}

/// Arguments for the `find_check` prompt.
#[derive(Debug, serde::Deserialize, schemars::JsonSchema)]
#[serde(deny_unknown_fields)]
pub(crate) struct FindCheckArgs {
    /// What is being validated: "serial", "license key", "password", "signature", ...
    pub(crate) what: String,
}

/// Arguments for the `explain_function` prompt.
#[derive(Debug, serde::Deserialize, schemars::JsonSchema)]
#[serde(deny_unknown_fields)]
pub(crate) struct ExplainFunctionArgs {
    /// Function entry (0x-hex, or bare decimal digits) or a name.
    pub(crate) address: String,
}

/// Parameters for `function_summary` and `function_strings`.
#[derive(Debug, serde::Deserialize, schemars::JsonSchema)]
#[serde(deny_unknown_fields)]
pub(crate) struct FunctionParams {
    /// Entry, any address inside it, or a name.
    pub(crate) address: String,
}

/// Parameters for `function`.
#[derive(Debug, serde::Deserialize, schemars::JsonSchema)]
#[serde(deny_unknown_fields)]
pub(crate) struct FunctionDetailParams {
    /// Entry, any address inside it, or a name.
    pub(crate) address: String,
    /// Blocks to skip first (300 a page).
    pub(crate) offset: Option<u32>,
}

/// Parameters for `xrefs`.
#[derive(Debug, serde::Deserialize, schemars::JsonSchema)]
#[serde(deny_unknown_fields)]
pub(crate) struct XrefsParams {
    /// Address or name (function, import, overlay name), or Class+offset.
    pub(crate) address: String,
    /// Groups to skip first (paging).
    pub(crate) offset: Option<u32>,
    /// Max groups (default 60, max 500).
    pub(crate) limit: Option<u32>,
    /// Header only (default false).
    pub(crate) count_only: Option<bool>,
}

/// Parameters for `class_layout`.
#[derive(Debug, serde::Deserialize, schemars::JsonSchema)]
#[serde(deny_unknown_fields)]
pub(crate) struct ClassLayoutParams {
    /// Class name or a method address.
    pub(crate) class: String,
    /// Struct name to define the layout as.
    pub(crate) apply: Option<String>,
    /// Preview only; false applies.
    pub(crate) dry_run: Option<bool>,
}

/// Parameters for `callgraph`.
#[derive(Debug, serde::Deserialize, schemars::JsonSchema)]
#[serde(deny_unknown_fields)]
pub(crate) struct CallgraphParams {
    /// Root function entry address.
    pub(crate) address: String,
    /// Maximum graph nodes (default 30, max 100).
    pub(crate) max_nodes: Option<u32>,
    /// What reaches it instead of what it calls.
    pub(crate) callers: Option<bool>,
}

/// Parameters for `reaches`.
#[derive(Debug, serde::Deserialize, schemars::JsonSchema)]
#[serde(deny_unknown_fields)]
pub(crate) struct ReachesParams {
    /// Function the call chain starts at.
    pub(crate) from: String,
    /// Target function, or an import by name or slot.
    pub(crate) to: String,
    /// Longest chain to follow (default 24, max 64).
    pub(crate) depth: Option<u32>,
}

/// Parameters for `find_crypto_constants`.
#[derive(Debug, serde::Deserialize, schemars::JsonSchema)]
#[serde(deny_unknown_fields)]
pub(crate) struct CryptoParams {
    /// Rows to skip (paging).
    pub(crate) offset: Option<u32>,
    /// Max rows (default 200, max 500).
    pub(crate) limit: Option<u32>,
}

/// Parameters for `cfg`.
#[derive(Debug, serde::Deserialize, schemars::JsonSchema)]
#[serde(deny_unknown_fields)]
pub(crate) struct CfgParams {
    /// Function entry or any address inside it.
    pub(crate) address: String,
    /// Blocks to skip, 300 a page.
    pub(crate) offset: Option<u32>,
}

/// Parameters for `decompile`.
#[derive(Debug, serde::Deserialize, schemars::JsonSchema)]
#[serde(deny_unknown_fields)]
pub(crate) struct DecompileParams {
    /// Function entry or any address inside it.
    pub(crate) address: String,
    /// `skeleton` for flow and calls only; `full` or absent for all of it.
    pub(crate) detail: Option<Detail>,
    /// Keep only lines containing this text, case-insensitively.
    pub(crate) filter: Option<String>,
    /// Skip this many lines of the answer.
    pub(crate) offset: Option<u32>,
    /// Return at most this many lines (default 300; more than the text has for all).
    pub(crate) limit: Option<u32>,
}

/// Parameters for `query`.
#[derive(Debug, serde::Deserialize, schemars::JsonSchema)]
#[serde(deny_unknown_fields)]
pub(crate) struct QueryParams {
    /// A borer:// resource URI.
    pub(crate) uri: String,
}

/// Parameters for `script`.
#[derive(Debug, serde::Deserialize, schemars::JsonSchema)]
#[serde(deny_unknown_fields)]
pub(crate) struct ScriptParams {
    /// Rhai source.
    pub(crate) code: String,
    /// Preview only (default true); false applies.
    pub(crate) dry_run: Option<bool>,
}

/// Parameters for `decompile_batch`.
#[derive(Debug, serde::Deserialize, schemars::JsonSchema)]
#[serde(deny_unknown_fields)]
pub(crate) struct DecompileBatchParams {
    /// Case-insensitive filter on function name or entry hex.
    pub(crate) filter: Option<String>,
    /// Maximum functions to decompile (default 10, max 50).
    pub(crate) max_functions: Option<u32>,
    /// A file under the output root, not with filter or a max: .c every function (over 4096 blocks: cut); .h, .ct, .rcnet the mod SDK as C++ header, Cheat Engine table, ReClass.NET.
    pub(crate) out: Option<String>,
    /// With out: also write library functions (default false).
    pub(crate) library: Option<bool>,
    /// With out: replace an existing file (default false).
    pub(crate) overwrite: Option<bool>,
}

/// Parameters for `search`.
#[derive(Debug, serde::Deserialize, schemars::JsonSchema)]
#[serde(deny_unknown_fields)]
pub(crate) struct SearchParams {
    /// Hex bytes with ?? wildcards (kind=bytes) or a literal substring (kind=text).
    pub(crate) query: String,
    /// What the query is (default bytes).
    pub(crate) kind: Option<SearchKind>,
    /// Hits to skip (default 0).
    pub(crate) offset: Option<usize>,
    /// Max hits (default 200, max 500).
    pub(crate) limit: Option<u32>,
    /// Header only (default false).
    pub(crate) count_only: Option<bool>,
}

/// Parameters for `set_name`.
#[derive(Debug, serde::Deserialize, schemars::JsonSchema)]
#[serde(deny_unknown_fields)]
pub(crate) struct SetNameParams {
    /// Function entry, any address inside it, or a data address.
    pub(crate) address: Option<String>,
    /// New name, an identifier (C++ `::<>~`, `@$?.` kept).
    pub(crate) name: Option<String>,
    /// Many at once instead: `address=name` each (max 500).
    pub(crate) names: Option<Vec<String>>,
    /// Take a name another address holds (default false).
    pub(crate) force: Option<bool>,
    /// Preview only (default true); false applies.
    pub(crate) dry_run: Option<bool>,
}

/// Parameters for `set_comment`.
#[derive(Debug, serde::Deserialize, schemars::JsonSchema)]
#[serde(deny_unknown_fields)]
pub(crate) struct SetCommentParams {
    /// Address the comment attaches to.
    pub(crate) address: String,
    /// Comment text.
    pub(crate) comment: String,
    /// Preview only (default true); false applies.
    pub(crate) dry_run: Option<bool>,
}

/// Parameters for `set_type`.
#[derive(Debug, serde::Deserialize, schemars::JsonSchema)]
#[serde(deny_unknown_fields)]
pub(crate) struct SetTypeParams {
    /// Struct, enum or typedef to define, or `var`'s new name.
    pub(crate) name: Option<String>,
    /// Struct fields, each `offset:name:type` (`0x1c:mp:u32`).
    pub(crate) fields: Option<Vec<String>>,
    /// Enum values, each `name:value` (`Run:1`).
    pub(crate) values: Option<Vec<String>>,
    /// Size past the last field, or an enum's width (4 or 8).
    pub(crate) size: Option<u64>,
    /// Data global to type, or a function for a prototype or `var`.
    pub(crate) address: Option<String>,
    /// Type to apply or typedef (`Player *`), a prototype, or alone C declarations.
    pub(crate) r#type: Option<String>,
    /// Function variable to name/type (`a1`, `local_58`).
    pub(crate) var: Option<String>,
    /// Preview only; false applies.
    pub(crate) dry_run: Option<bool>,
}

/// Parameters for `types`.
#[derive(Debug, serde::Deserialize, schemars::JsonSchema)]
#[serde(deny_unknown_fields)]
pub(crate) struct TypesParams {
    /// Substring filter on name or applied address.
    pub(crate) filter: Option<String>,
    /// Rows to skip first (paging).
    pub(crate) offset: Option<u32>,
    /// Max rows (default 50, max 500).
    pub(crate) limit: Option<u32>,
    /// Header only (default false).
    pub(crate) count_only: Option<bool>,
}

/// Parameters for `annotations`.
#[derive(Debug, Default, serde::Deserialize, schemars::JsonSchema)]
#[serde(deny_unknown_fields)]
pub(crate) struct AnnotationsParams {
    /// Case-insensitive substring of a row (address, kind or text).
    pub(crate) filter: Option<String>,
    /// Rows to skip first (paging).
    pub(crate) offset: Option<u32>,
    /// Max rows (default 200, max 1000).
    pub(crate) limit: Option<u32>,
    /// Header only (default false).
    pub(crate) count_only: Option<bool>,
}

/// Parameters for `save_project`.
#[derive(Debug, serde::Deserialize, schemars::JsonSchema)]
#[serde(deny_unknown_fields)]
pub(crate) struct SaveProjectParams {
    /// Output `.json` path, relative to the output root or absolute under it.
    pub(crate) path: String,
    /// Replace an existing file (default false).
    pub(crate) overwrite: Option<bool>,
}

/// Parameters for `load_project`.
#[derive(Debug, serde::Deserialize, schemars::JsonSchema)]
#[serde(deny_unknown_fields)]
pub(crate) struct LoadProjectParams {
    /// Project JSON path.
    pub(crate) path: String,
    /// Load a project saved for another binary anyway (default false).
    pub(crate) force: Option<bool>,
}

/// Parameters for `live_attach`.
#[derive(Debug, serde::Deserialize, schemars::JsonSchema)]
#[serde(deny_unknown_fields)]
pub(crate) struct LiveAttachParams {
    /// Executable name or pid.
    pub(crate) process: String,
}

/// Parameters for `live_read`.
#[derive(Debug, serde::Deserialize, schemars::JsonSchema)]
#[serde(deny_unknown_fields)]
pub(crate) struct LiveReadParams {
    /// Live or static address, or a name; `live:0x..` is never rebased.
    pub(crate) address: String,
    /// What to decode the bytes as (default u64).
    pub(crate) kind: Option<ReadKind>,
    /// Values (default 1, max 256).
    pub(crate) count: Option<u32>,
}

/// Parameters for `live_object`.
#[derive(Debug, serde::Deserialize, schemars::JsonSchema)]
#[serde(deny_unknown_fields)]
pub(crate) struct LiveObjectParams {
    /// Object address: live, static, or a name.
    pub(crate) address: String,
    /// Class; default: the one its vtable names.
    pub(crate) class: Option<String>,
}

/// Parameters for `live_instances`.
#[derive(Debug, serde::Deserialize, schemars::JsonSchema)]
#[serde(deny_unknown_fields)]
pub(crate) struct LiveInstancesParams {
    /// Class name.
    pub(crate) class: String,
    /// Instances to skip.
    pub(crate) offset: Option<u32>,
    /// Max instances (default 64, max 512).
    pub(crate) limit: Option<u32>,
    /// Header line only.
    pub(crate) count_only: Option<bool>,
}

/// Parameters for `live_modules`.
#[derive(Debug, serde::Deserialize, schemars::JsonSchema)]
#[serde(deny_unknown_fields)]
pub(crate) struct LiveModulesParams {
    /// Substring of name or path.
    pub(crate) filter: Option<String>,
    /// Rows to skip.
    pub(crate) offset: Option<u32>,
    /// Max rows (default 50, max 500).
    pub(crate) limit: Option<u32>,
    /// Header line only.
    pub(crate) count_only: Option<bool>,
}

/// Parameters for `live_watch`.
#[derive(Debug, serde::Deserialize, schemars::JsonSchema)]
#[serde(deny_unknown_fields)]
pub(crate) struct LiveWatchParams {
    /// Watch name.
    pub(crate) name: String,
    /// Address to start watching; omit to diff.
    pub(crate) address: Option<String>,
    /// Bytes (default: the class's size, else 256; max 65536).
    pub(crate) length: Option<u32>,
    /// Class naming the fields (default: from the vtable).
    pub(crate) class: Option<String>,
}

/// What `live_scan` looks for.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default, serde::Deserialize, schemars::JsonSchema)]
#[serde(rename_all = "lowercase")]
#[schemars(transform = names_only)]
pub(crate) enum ScanKind {
    /// One unsigned byte.
    U8,
    /// An unsigned 16-bit word.
    U16,
    /// An unsigned 32-bit word.
    #[default]
    U32,
    /// An unsigned 64-bit word.
    U64,
    /// A signed byte.
    I8,
    /// A signed 16-bit word.
    I16,
    /// A signed 32-bit word.
    I32,
    /// A signed 64-bit word.
    I64,
    /// A single-precision float.
    F32,
    /// A double-precision float.
    F64,
    /// A UTF-8 string, no terminator.
    String,
    /// A UTF-16LE string, no terminator.
    Wstring,
    /// Hex bytes with `??` wildcards.
    #[serde(alias = "aob")]
    Bytes,
}

impl ScanKind {
    /// The engine kind values of this scan read as; `None` for bytes.
    pub(crate) fn kind(self) -> Option<borer_engine::memory::Kind> {
        use borer_engine::memory::Kind;
        Some(match self {
            Self::U8 => Kind::U8,
            Self::U16 => Kind::U16,
            Self::U32 => Kind::U32,
            Self::U64 => Kind::U64,
            Self::I8 => Kind::I8,
            Self::I16 => Kind::I16,
            Self::I32 => Kind::I32,
            Self::I64 => Kind::I64,
            Self::F32 => Kind::F32,
            Self::F64 => Kind::F64,
            Self::String => Kind::CStr,
            Self::Wstring => Kind::WStr,
            Self::Bytes => return None,
        })
    }
}

/// How a next `live_scan` narrows a result set.
#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Deserialize, schemars::JsonSchema)]
#[serde(rename_all = "lowercase")]
#[schemars(transform = names_only)]
pub(crate) enum ScanCompare {
    /// The bytes differ from the last scan.
    Changed,
    /// The bytes are the same as at the last scan.
    Unchanged,
    /// The number is larger than at the last scan.
    Increased,
    /// The number is smaller than at the last scan.
    Decreased,
    /// The value now equals `value`.
    Equal,
}

/// Where a first `live_scan` reads.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default, serde::Deserialize, schemars::JsonSchema)]
#[serde(rename_all = "lowercase")]
#[schemars(transform = names_only)]
pub(crate) enum ScanScope {
    /// Every readable region.
    #[default]
    All,
    /// The process's main module.
    Main,
    /// The module `module` names.
    Module,
    /// Writable memory no module maps: heaps, stacks.
    Heap,
}

/// Parameters for `live_scan`.
#[derive(Debug, serde::Deserialize, schemars::JsonSchema)]
#[serde(deny_unknown_fields)]
pub(crate) struct LiveScanParams {
    /// Result set name; a first scan replaces a set of that name.
    pub(crate) name: String,
    /// Number, text, or hex bytes (?? wildcard); with compare=equal, the new value.
    pub(crate) value: Option<String>,
    /// Value type (default u32); a next scan keeps the set's.
    pub(crate) kind: Option<ScanKind>,
    /// Float tolerance (default: half a unit of the last digit given).
    pub(crate) tolerance: Option<f64>,
    /// Narrow the named set instead of scanning anew.
    pub(crate) compare: Option<ScanCompare>,
    /// Where a first scan reads (default all).
    pub(crate) scope: Option<ScanScope>,
    /// Module name, for scope=module.
    pub(crate) module: Option<String>,
    /// Hits to skip.
    pub(crate) offset: Option<u32>,
    /// Max rows (default 50, max 500).
    pub(crate) limit: Option<u32>,
    /// Header line only.
    pub(crate) count_only: Option<bool>,
}

/// Widens a count parameter to the index type.
///
/// A `u32` fits a 32-bit or wider `usize`, so nothing is lost on any
/// target borer builds for; the saturation only states the rule.
///
/// # Arguments
///
/// * `n` - The parameter as given.
pub(crate) fn to_usize(n: u32) -> usize {
    usize::try_from(n).unwrap_or(usize::MAX)
}

/// A count parameter the cap cut: its name, what was asked, and the cap.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct Capped {
    /// The parameter's name (`limit`, `count`, ...).
    what: &'static str,
    /// The value the caller passed, above `max`.
    asked: u32,
    /// The cap the value was cut to.
    max: usize,
}

/// A count parameter as read: the value in force, and the cut when the cap
/// made one.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct Count {
    /// The value in force, at or under the cap.
    pub(crate) n: usize,
    /// What the cap cut, `None` when the value was taken as asked.
    pub(crate) capped: Option<Capped>,
}

impl Count {
    /// Puts the line saying what the cap cut ahead of an answer, so a
    /// caller who asked for more learns it got the cap and not everything;
    /// an answer within the cap is returned as it is.
    ///
    /// # Arguments
    ///
    /// * `text` - The answer.
    pub(crate) fn noted(self, text: String) -> String {
        self.noted_with("#", text)
    }

    /// [`Count::noted`] with the line opened by `mark`: `%%` ahead of a
    /// mermaid graph, where a `#` line does not parse.
    ///
    /// # Arguments
    ///
    /// * `mark` - What opens a comment line in the answer's language.
    /// * `text` - The answer.
    pub(crate) fn noted_with(self, mark: &str, text: String) -> String {
        match self.capped {
            Some(Capped { what, asked, max }) => {
                format!("{mark} {what} {asked} capped at {max}\n{text}")
            }
            None => text,
        }
    }
}

/// Reads a count parameter: the default when absent, an error at zero, the
/// cap above it.
///
/// A zero count would answer nothing and read as a failure of the tool
/// rather than of the call, so it is refused; a value above the cap is what
/// the cap is for, and [`Count::noted`] says so in the answer, where a
/// silent cut read as the whole of what there was.
///
/// # Arguments
///
/// * `v` - The parameter as given.
/// * `default` - The value when the parameter is absent.
/// * `max` - The cap.
/// * `what` - The parameter's name, for the message and the note.
///
/// # Errors
///
/// When the parameter is zero.
pub(crate) fn count_param(
    v: Option<u32>,
    default: usize,
    max: usize,
    what: &'static str,
) -> Result<Count, ErrorData> {
    match v {
        None => Ok(Count {
            n: default,
            capped: None,
        }),
        Some(0) => Err(err_params(format!("{what} must be at least 1"))),
        Some(asked) => Ok(Count {
            n: to_usize(asked).min(max),
            capped: (to_usize(asked) > max).then_some(Capped { what, asked, max }),
        }),
    }
}

/// One page of a listing: where it starts, how many rows it holds, and
/// whether only the header is wanted.
///
/// Built once at the boundary from the three paging parameters every list
/// tool takes, so a handler reads typed fields rather than defaulting each
/// `Option` where it is used.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct Page {
    /// Matches to skip first.
    pub(crate) offset: usize,
    /// Most rows shown, at or under the tool's cap, with the cut when the
    /// cap made one.
    pub(crate) limit: Count,
    /// Header line only.
    pub(crate) count_only: bool,
}

impl Page {
    /// Reads the paging parameters as given.
    ///
    /// # Arguments
    ///
    /// * `offset` - Matches to skip; absent skips none.
    /// * `limit` - Most rows; absent is `default`, above `max` is `max`
    ///   and noted ([`Count::noted`]).
    /// * `count_only` - Header only; absent is false.
    /// * `default` - The tool's default row count.
    /// * `max` - The tool's cap.
    ///
    /// # Errors
    ///
    /// When `limit` is zero.
    pub(crate) fn new(
        offset: Option<u32>,
        limit: Option<u32>,
        count_only: Option<bool>,
        default: usize,
        max: usize,
    ) -> Result<Page, ErrorData> {
        Ok(Page {
            offset: to_usize(offset.unwrap_or(0)),
            limit: count_param(limit, default, max, "limit")?,
            count_only: count_only.unwrap_or(false),
        })
    }
}

/// A case-insensitive substring filter, lowered once at the boundary.
///
/// Every list tool narrows by one: absent keeps every row, present keeps
/// the rows whose text contains it in any case.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub(crate) struct Filter(Option<String>);

impl Filter {
    /// Lowers the filter as given.
    ///
    /// # Arguments
    ///
    /// * `text` - The filter parameter; `None` keeps everything.
    pub(crate) fn new(text: Option<&str>) -> Filter {
        Filter(text.map(str::to_lowercase))
    }

    /// Whether a row passes: its text contains the filter in any case, or
    /// there is no filter.
    ///
    /// # Arguments
    ///
    /// * `text` - The row's text as printed.
    pub(crate) fn accepts(&self, text: &str) -> bool {
        self.0
            .as_ref()
            .is_none_or(|f| text.to_lowercase().contains(f.as_str()))
    }

    /// The lowered filter, `None` when there is none.
    pub(crate) fn needle(&self) -> Option<&str> {
        self.0.as_deref()
    }
}

/// Which annotation a call carries, for the message that refuses one.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Annotation {
    /// A name set by `set_name`.
    Name,
    /// A comment set by `set_comment`.
    Comment,
    /// A type applied by `set_type`.
    Type,
}

impl std::fmt::Display for Annotation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            Self::Name => "name",
            Self::Comment => "comment",
            Self::Type => "type",
        })
    }
}

/// Refuses a name or comment the line-oriented listings could not show.
///
/// Every place an annotation is printed is one line of a table, so a
/// control character would break the table for every reader after it, and
/// an empty name would name nothing. A name is the caller's to retry, so
/// this refuses where [`borer_engine::text::one_line`] escapes: that one
/// takes names out of the file, which cannot be handed back for a second
/// try, and both go by the same rule about what a row can hold.
///
/// # Arguments
///
/// * `text` - The annotation as given.
/// * `what` - Which annotation it is, for the message.
///
/// # Errors
///
/// When the text is empty, blank, longer than a row can show, or holds
/// anything that would end its line or move what is printed around it.
pub(crate) fn must_fit_a_row(text: &str, what: Annotation) -> Result<(), ErrorData> {
    if text.trim().is_empty() {
        return Err(err_params(format!("the {what} is empty")));
    }
    if text.chars().any(char::is_control) {
        return Err(err_params(format!(
            "the {what} holds a control character; annotations are one line each"
        )));
    }
    let width = text.chars().count();
    if width > borer_engine::text::OUTSIDE_MAX {
        return Err(err_params(format!(
            "the {what} is {width} characters; {} is the most a listing row shows",
            borer_engine::text::OUTSIDE_MAX
        )));
    }
    if borer_engine::text::one_line(text) != text {
        return Err(err_params(format!(
            "the {what} holds text that reorders what is printed around it"
        )));
    }
    Ok(())
}

/// Punctuation a name may hold besides letters and digits: C++ scopes,
/// templates and destructors (`::`, `<>`, `~`), MSVC and Itanium mangling
/// (`?`, `@`, `$`), ELF's split parts (`foo.cold`) and `_`.
const NAME_PUNCTUATION: &str = "_:<>~?@$.";

/// Refuses a name the pseudo-C or a later lookup could not carry.
///
/// A name is printed where C expects an identifier and is looked up as
/// one, so a space, a parenthesis or a leading digit would break both.
///
/// # Arguments
///
/// * `name` - The name asked for.
///
/// # Errors
///
/// When the name opens with a digit or holds a character no identifier
/// or mangled name has; the message names the character.
pub(crate) fn must_be_a_name(name: &str) -> Result<(), ErrorData> {
    if name.starts_with(|c: char| c.is_ascii_digit()) {
        return Err(err_params(format!(
            "{} opens with a digit; a name must not, or it reads as a number",
            borer_engine::text::quoted(name)
        )));
    }
    match name
        .chars()
        .find(|&c| !c.is_alphanumeric() && !NAME_PUNCTUATION.contains(c))
    {
        Some(c) => Err(err_params(format!(
            "{} holds {c:?}; a name is letters, digits and {NAME_PUNCTUATION}",
            borer_engine::text::quoted(name)
        ))),
        None => Ok(()),
    }
}

/// Refuses an annotation at an address no section maps.
///
/// Nothing borer lists lives outside the image, so a name or comment there
/// would sit in the overlay and the project file and never be shown; `0x1`
/// is a typo, not a place. Both annotating tools refuse it alike.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `va` - The address the annotation is for.
/// * `what` - Which annotation it is, for the message.
///
/// # Errors
///
/// When no section contains `va`, listing the sections that exist.
pub(crate) fn must_be_in_a_section(
    program: &program::Program,
    va: u64,
    what: Annotation,
) -> Result<(), String> {
    if program.section_at(va).is_some() {
        return Ok(());
    }
    Err(format!(
        "{va:#x} is in no section, so nothing there can take a {what}; sections: {}",
        program.section_list()
    ))
}

/// Returns the stack word and the callee-owned home space above the
/// return address, in bytes.
///
/// The decompiled text numbers a function's slots by them: 32 bytes of
/// home space under the Microsoft x64 convention, none elsewhere.
///
/// # Arguments
///
/// * `p` - The loaded program.
pub(crate) fn frame_words(p: &program::Program) -> (i64, i64) {
    let windows = !matches!(
        p.format,
        program::BinaryFormat::Elf | program::BinaryFormat::MachO
    );
    match (p.is_64, windows) {
        (true, true) => (8, 32),
        (true, false) => (8, 0),
        (false, _) => (4, 0),
    }
}

/// Reads what `set_type` states of a function's variable: which variable
/// `var` names, and the name and type it takes.
///
/// `var` is the name the text shows (`a1`, `local_58`) or one stated
/// before, the variable's or the prototype's parameter's; `name` is the
/// new name and `type` an optional C type.
///
/// # Arguments
///
/// * `p` - The loaded program, for its word.
/// * `o` - The overlay.
/// * `entry` - The function.
/// * `var` - The variable.
/// * `name` - Its new name.
/// * `ty` - Its type, if one is stated.
///
/// # Errors
///
/// When `var` names no parameter or slot, `name` is missing or refused,
/// the type does not parse, another variable of the function already has
/// the name, or the overlay holds as many variables as it can.
pub(crate) fn plan_var(
    p: &program::Program,
    o: &borer_engine::analysis::Overlay,
    entry: u64,
    var: &str,
    name: Option<&str>,
    ty: Option<&str>,
) -> Result<
    (
        borer_engine::analysis::protos::VarKey,
        borer_engine::analysis::protos::Var,
    ),
    String,
> {
    use borer_engine::analysis::protos::{VARS_MAX, Var, VarKey};
    let (stack, shadow) = frame_words(p);
    let stated = o.vars.get(&entry);
    let key = stated
        .and_then(|vs| vs.iter().find(|(_, v)| v.name == var).map(|(k, _)| *k))
        .or_else(|| {
            let i = o
                .prototypes
                .get(&entry)?
                .params
                .iter()
                .position(|q| q.name == var)?;
            u8::try_from(i).ok().map(VarKey::Param)
        })
        .map_or_else(|| VarKey::parse(var, stack).map_err(|e| e.to_string()), Ok)?;
    let name = name.ok_or("naming a variable needs `name`, its new name (`type` is optional)")?;
    let decl = ty.map_or_else(|| name.to_owned(), |t| format!("{t} {name}"));
    let var = Var::parse(&decl).map_err(|e| e.to_string())?;
    if let Some((other, _)) =
        stated.and_then(|vs| vs.iter().find(|(k, v)| v.name == var.name && **k != key))
    {
        return Err(format!(
            "{} already names {} of this function",
            var.name,
            other.spell(stack, shadow)
        ));
    }
    let held: usize = o.vars.values().map(std::collections::BTreeMap::len).sum();
    if held >= VARS_MAX && !stated.is_some_and(|vs| vs.contains_key(&key)) {
        return Err(format!(
            "the overlay states {held} variables, the most it holds"
        ));
    }
    Ok((key, var))
}

/// What the parameter parser starts a refused argument's message with.
pub(crate) const DESERIALIZE_PREFIX: &str = "failed to deserialize parameters:";

/// Names the argument a tool's input schema does not admit.
///
/// serde words a wrong value without the field it was in (`invalid type:
/// string "5", expected u32`), and a call with five arguments leaves the
/// caller to guess which; the schema the tool list publishes says what
/// each one takes, so the first argument it refuses is the one named.
///
/// # Arguments
///
/// * `schema` - The tool's input schema as generated: `properties`, each
///   with its `type` and, for a count, its `format` and `minimum`, and the
///   `required` list.
/// * `args` - The arguments the call passed.
///
/// # Returns
///
/// The first refused argument's name, or `None` when the schema admits
/// every argument (the message then names its own culprit, an unknown
/// field or a missing one).
pub(crate) fn misfit(
    schema: &serde_json::Map<String, serde_json::Value>,
    args: &serde_json::Map<String, serde_json::Value>,
) -> Option<String> {
    use serde_json::Value;
    let props = schema.get("properties")?.as_object()?;
    let required: Vec<&str> = schema
        .get("required")
        .and_then(Value::as_array)
        .map(|r| r.iter().filter_map(Value::as_str).collect())
        .unwrap_or_default();
    args.iter()
        .find(|(key, value)| {
            props
                .get(key.as_str())
                .and_then(Value::as_object)
                .is_some_and(|prop| !admits(prop, value, required.contains(&key.as_str())))
        })
        .map(|(key, _)| key.clone())
}

/// Whether one property of a schema admits a value.
///
/// # Arguments
///
/// * `prop` - The property's schema.
/// * `value` - The value passed.
/// * `required` - The property must be present, so null is no value for
///   it.
fn admits(
    prop: &serde_json::Map<String, serde_json::Value>,
    value: &serde_json::Value,
    required: bool,
) -> bool {
    use serde_json::Value;
    if value.is_null() {
        return !required;
    }
    let kinds: Vec<&str> = match prop.get("type") {
        Some(Value::String(kind)) => vec![kind.as_str()],
        Some(Value::Array(kinds)) => kinds.iter().filter_map(Value::as_str).collect(),
        Some(_) | None => return true,
    };
    let typed = kinds.iter().any(|kind| match *kind {
        "integer" => value.is_u64() || value.is_i64(),
        "number" => value.is_number(),
        "boolean" => value.is_boolean(),
        "string" => value.is_string(),
        "array" => value.is_array(),
        "object" => value.is_object(),
        _ => false,
    });
    let above_minimum = prop
        .get("minimum")
        .and_then(Value::as_f64)
        .is_none_or(|min| value.as_f64().is_none_or(|v| v >= min));
    let fits_format = match prop.get("format").and_then(Value::as_str) {
        Some("uint32") => value.as_u64().is_some_and(|n| u32::try_from(n).is_ok()),
        Some(_) | None => true,
    };
    typed && above_minimum && fits_format
}

/// Parses a field offset: `0x10`, `16` or `-0x8`.
///
/// Hex takes its `0x`, as an address does: an offset is read in a context
/// full of decimal counts, and reading bare digits as hex turned `16` into a
/// guess and `abc` into `0xabc` without a word.
///
/// # Arguments
///
/// * `text` - The offset as typed: an optional minus sign, then `0x` and hex
///   digits or decimal digits alone.
///
/// # Errors
///
/// When the text is not one of those forms, or the magnitude does not fit
/// a signed displacement.
pub(crate) fn parse_field_offset(text: &str) -> anyhow::Result<i64> {
    use anyhow::Context as _;
    let (negative, digits) = text.strip_prefix('-').map_or((false, text), |d| (true, d));
    let (radix, digits) = match digits
        .strip_prefix("0x")
        .or_else(|| digits.strip_prefix("0X"))
    {
        Some(hex) => (16, hex),
        None => (10, digits),
    };
    let magnitude = Some(digits)
        .filter(|d| !d.is_empty() && d.chars().all(|c| c.is_digit(radix)))
        .and_then(|d| u64::from_str_radix(d, radix).ok())
        .with_context(|| format!("bad offset {}", borer_engine::text::quoted(text)))?;
    let value = i64::try_from(magnitude)
        .with_context(|| format!("offset {text} does not fit a signed displacement"))?;
    Ok(if negative { -value } else { value })
}

#[cfg(test)]
mod tests {
    use super::{
        Annotation, Filter, Page, SymbolKind, count_param, misfit, must_be_in_a_section,
        must_fit_a_row,
    };

    /// A symbol kind spelled in the plural, as an agent asks for a list,
    /// reads as the kind.
    ///
    /// # Panics
    ///
    /// When `imports` or `exports` is refused or read as another kind.
    #[test]
    fn a_plural_symbol_kind_reads_as_the_kind() {
        let kind = |word: &str| serde_json::from_value::<SymbolKind>(word.into()).ok();
        assert_eq!(kind("imports"), Some(SymbolKind::Import));
        assert_eq!(kind("exports"), Some(SymbolKind::Export));
        assert_eq!(kind("locals"), Some(SymbolKind::Local));
        assert_eq!(kind("forwarders"), Some(SymbolKind::Forward));
        assert_eq!(kind("export"), Some(SymbolKind::Export));
    }

    /// A refused argument is named from the tool's schema: a string where a
    /// count goes, a negative count, a count past `u32`, null for a required
    /// field; a value the schema admits names nothing.
    ///
    /// # Panics
    ///
    /// When the wrong argument, or none, is named.
    #[test]
    fn a_refused_argument_is_named_from_the_schema() {
        let schema = serde_json::json!({
            "properties": {
                "address": {"type": "string"},
                "offset": {"type": ["integer", "null"], "format": "uint32", "minimum": 0},
                "count_only": {"type": ["boolean", "null"]}
            },
            "required": ["address"]
        });
        let schema = schema.as_object().expect("an object");
        let named = |args: serde_json::Value| misfit(schema, args.as_object().expect("an object"));
        assert_eq!(
            named(serde_json::json!({"address": "f", "offset": "5"})).as_deref(),
            Some("offset")
        );
        assert_eq!(
            named(serde_json::json!({"address": "f", "offset": -5})).as_deref(),
            Some("offset")
        );
        assert_eq!(
            named(serde_json::json!({"address": "f", "offset": 5.5})).as_deref(),
            Some("offset")
        );
        assert_eq!(
            named(serde_json::json!({"address": "f", "offset": 4_294_967_296_u64})).as_deref(),
            Some("offset")
        );
        assert_eq!(
            named(serde_json::json!({"address": null})).as_deref(),
            Some("address")
        );
        assert_eq!(
            named(serde_json::json!({"address": "f", "count_only": "yes"})).as_deref(),
            Some("count_only")
        );
        assert_eq!(
            named(serde_json::json!({"address": "f", "offset": 5, "count_only": null})),
            None
        );
    }

    /// An annotation that a listing row could not show is refused.
    ///
    /// A name the caller passes is theirs to retry, so this refuses where the
    /// engine escapes a name it read out of a binary. What both go by is the
    /// same: one record to a line, and a bounded amount of it. An ordinary
    /// non-ASCII name stays allowed; a right-to-left override, which prints
    /// the rest of the row backwards without showing anything, does not.
    ///
    /// # Panics
    ///
    /// When text that would break a row is accepted, or an ordinary name is
    /// refused.
    #[test]
    fn an_annotation_that_breaks_a_row_is_refused() {
        assert!(must_fit_a_row("parse_header", Annotation::Name).is_ok());
        assert!(must_fit_a_row("lire_entête", Annotation::Name).is_ok());

        assert!(must_fit_a_row("", Annotation::Name).is_err());
        assert!(must_fit_a_row("   ", Annotation::Name).is_err());
        assert!(must_fit_a_row("two\nlines", Annotation::Name).is_err());
        assert!(must_fit_a_row("txet\u{202e}", Annotation::Name).is_err());

        let max = borer_engine::text::OUTSIDE_MAX;
        assert!(must_fit_a_row(&"a".repeat(max), Annotation::Name).is_ok());
        assert!(must_fit_a_row(&"a".repeat(max + 1), Annotation::Name).is_err());
    }

    /// A page defaults, caps and refuses zero the way every list tool does;
    /// a filter matches in any case and absent keeps everything.
    ///
    /// # Panics
    ///
    /// When a page or a filter reads differently from the parameters.
    #[test]
    fn a_page_and_a_filter_read_the_parameters() {
        let page = Page::new(None, None, None, 50, 300).expect("defaults");
        assert_eq!((page.offset, page.limit.n, page.count_only), (0, 50, false));
        let page = Page::new(Some(7), Some(9_000), Some(true), 50, 300).expect("caps");
        assert_eq!((page.offset, page.limit.n, page.count_only), (7, 300, true));
        let zero = Page::new(None, Some(0), None, 50, 300).expect_err("refused");
        assert_eq!(zero.message, "limit must be at least 1");

        let filter = Filter::new(Some("ThUnK"));
        assert!(filter.accepts("entry_THUNK"));
        assert!(!filter.accepts("main"));
        assert_eq!(filter.needle(), Some("thunk"));
        assert!(Filter::new(None).accepts("anything"));
    }

    /// A count the cap cut says so ahead of the answer, naming the
    /// parameter, what was asked and the cap; one at or under the cap, or
    /// absent, leaves the answer as it was.
    ///
    /// # Panics
    ///
    /// When a cut goes unsaid or an uncut count is noted.
    #[test]
    fn a_count_the_cap_cut_says_so() {
        let cut = count_param(Some(99_999), 50, 300, "limit").expect("caps");
        assert_eq!(cut.n, 300);
        assert_eq!(
            cut.noted("# 300 rows\n".to_owned()),
            "# limit 99999 capped at 300\n# 300 rows\n"
        );
        for whole in [
            count_param(Some(300), 50, 300, "limit"),
            count_param(Some(7), 50, 300, "limit"),
            count_param(None, 50, 300, "limit"),
        ] {
            let whole = whole.expect("in range");
            assert_eq!(whole.capped, None);
            assert_eq!(whole.noted("# rows\n".to_owned()), "# rows\n");
        }
        let page = Page::new(None, Some(1_000), None, 200, 500).expect("caps");
        assert_eq!(
            page.limit.noted(String::new()),
            "# limit 1000 capped at 500\n"
        );
        let zero = count_param(Some(0), 32, 256, "count").expect_err("refused");
        assert_eq!(zero.message, "count must be at least 1");
    }

    /// An annotation for an address no section holds is refused, naming
    /// the address and the sections there are; one inside a section passes.
    ///
    /// # Panics
    ///
    /// When an address outside the image is accepted or one inside refused.
    #[test]
    fn an_annotation_outside_every_section_is_refused() {
        use borer_engine::program::{Arch, Program, Section};
        let text = Section::mapped(".text", 0x1000, 0, 0x100, false, true);
        let p = Program::raw(vec![0xc3; 0x100], Arch::X86_64, 0, Some(0x1000), vec![text]);
        assert_eq!(
            must_be_in_a_section(&p, 0x1010, Annotation::Comment),
            Ok(())
        );
        let name = must_be_in_a_section(&p, 0x1, Annotation::Name).expect_err("refused");
        let comment = must_be_in_a_section(&p, 0x1, Annotation::Comment).expect_err("refused");
        assert!(
            name.starts_with("0x1 is in no section, so nothing there can take a name; sections: "),
            "{name}"
        );
        assert_eq!(comment, name.replace("a name", "a comment"));
    }

    /// A field offset is hex with its `0x` and decimal without, as an
    /// address is; anything else is refused by name rather than guessed.
    ///
    /// # Panics
    ///
    /// When a form reads as another number, or a guess is accepted.
    #[test]
    fn a_field_offset_is_hex_with_0x_and_decimal_without() {
        let parse = |t: &str| super::parse_field_offset(t).map_err(|e| e.to_string());
        assert_eq!(parse("0x10"), Ok(16));
        assert_eq!(parse("0X1f"), Ok(31));
        assert_eq!(parse("16"), Ok(16));
        assert_eq!(parse("-0x8"), Ok(-8));
        assert_eq!(parse("-8"), Ok(-8));
        assert_eq!(parse("abc"), Err("bad offset 'abc'".to_owned()));
        for guess in ["1f", "", "-", "0x", "+5", "0x+5", "--8", "0x1g"] {
            assert!(
                parse(guess).is_err_and(|e| e.starts_with("bad offset ")),
                "{guess:?} was read"
            );
        }
        assert!(parse("0xffffffffffffffff").is_err_and(|e| e.contains("signed displacement")));
    }
}
