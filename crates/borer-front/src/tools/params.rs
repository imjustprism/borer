//! What each catalog tool accepts, as the JSON schema a caller reads before
//! it calls, and the paging every list tool reads its parameters into.

use borer_engine::analysis::render;
use borer_engine::program;

use super::Failure;

/// What `read` and `live_read` decode the bytes as.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default, serde::Deserialize, schemars::JsonSchema)]
#[serde(rename_all = "lowercase")]
#[schemars(transform = names_only)]
pub enum ReadKind {
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
pub fn names_only(schema: &mut schemars::Schema) {
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
    pub fn word(self) -> &'static str {
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
pub enum StringEncoding {
    /// Byte strings only.
    Ascii,
    /// UTF-16 strings only.
    Utf16,
    /// Both, in address order.
    #[default]
    Both,
}

impl From<StringEncoding> for borer_engine::strings::walk::StringEncoding {
    fn from(e: StringEncoding) -> Self {
        match e {
            StringEncoding::Ascii => Self::Ascii,
            StringEncoding::Utf16 => Self::Utf16,
            StringEncoding::Both => Self::Both,
        }
    }
}

/// Which symbols `symbols` lists.
#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Deserialize, schemars::JsonSchema)]
#[serde(rename_all = "lowercase")]
#[schemars(transform = names_only)]
pub enum SymbolKind {
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
pub enum Detail {
    /// The whole function.
    #[default]
    Full,
    /// The flow and the calls only.
    Skeleton,
}

impl From<Detail> for borer_engine::analysis::decompile::Detail {
    fn from(d: Detail) -> Self {
        match d {
            Detail::Full => Self::Full,
            Detail::Skeleton => Self::Skeleton,
        }
    }
}

/// What `search` looks for.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default, serde::Deserialize, schemars::JsonSchema)]
#[serde(rename_all = "lowercase")]
#[schemars(transform = names_only)]
pub enum SearchKind {
    /// Hex bytes with `??` wildcards.
    #[default]
    Bytes,
    /// A literal substring, ASCII or UTF-16.
    Text,
}

/// Parameters for `disassemble`.
#[derive(Debug, serde::Deserialize, schemars::JsonSchema)]
#[serde(deny_unknown_fields)]
pub struct DisassembleParams {
    /// Address or a function/symbol name.
    pub address: String,
    /// Max instructions (default 32, max 256).
    pub count: Option<u32>,
    /// Add the raw-bytes column (default false).
    pub bytes: Option<bool>,
}

/// Parameters for `disassemble_function`.
#[derive(Debug, serde::Deserialize, schemars::JsonSchema)]
#[serde(deny_unknown_fields)]
pub struct DisassembleFunctionParams {
    /// Entry, any address inside it, or a name.
    pub address: String,
    /// Maximum instructions to return (default 400, max 2000).
    pub max_instrs: Option<u32>,
    /// Add the raw-bytes column (default false).
    pub bytes: Option<bool>,
}

/// Parameters for `read`.
#[derive(Debug, serde::Deserialize, schemars::JsonSchema)]
#[serde(deny_unknown_fields)]
pub struct ReadParams {
    /// Address (0x-hex or decimal), a name, or `off:<n>` for a file offset.
    pub address: String,
    /// What to decode the bytes as (default u64).
    pub kind: Option<ReadKind>,
    /// A user type instead of kind: `Rec`, `Rec[4]`, `char[16]`.
    pub r#type: Option<String>,
    /// Values to read (default 1, max 256).
    pub count: Option<u32>,
}

/// Parameters for `entropy`.
#[derive(Debug, serde::Deserialize, schemars::JsonSchema)]
#[serde(deny_unknown_fields)]
pub struct EntropyParams {
    /// Window size in bytes (default 1024, minimum 64).
    pub window: Option<u32>,
    /// Minimum bits per byte to report (default 7.2, max 8.0).
    pub threshold: Option<f64>,
    /// Regions to skip first (paging).
    pub offset: Option<u32>,
    /// Most regions listed (default 200, max 200).
    pub limit: Option<u32>,
}

/// Parameters for `find_function_by_string`.
#[derive(Debug, Default, serde::Deserialize, schemars::JsonSchema)]
#[serde(deny_unknown_fields)]
pub struct FindFunctionByStringParams {
    /// A string under 4 printable characters must equal it.
    #[serde(alias = "query")]
    pub filter: String,
    /// Rows to skip (paging).
    pub offset: Option<u32>,
    /// Max rows per table, and legend strings (default 50, max 300).
    pub limit: Option<u32>,
}

/// Parameters for `hexdump`.
#[derive(Debug, serde::Deserialize, schemars::JsonSchema)]
#[serde(deny_unknown_fields)]
pub struct HexdumpParams {
    /// Address (0x-hex or decimal), a name, or `off:<n>` for a file offset.
    pub address: String,
    /// Number of bytes (default 64, max 4096).
    pub length: Option<u32>,
}

/// Parameters for `strings`.
#[derive(Debug, Default, serde::Deserialize, schemars::JsonSchema)]
#[serde(deny_unknown_fields)]
pub struct StringsParams {
    /// Minimum length (default 5, min 4).
    pub min_length: Option<u32>,
    /// Case-insensitive substring filter.
    pub filter: Option<String>,
    /// Which strings to scan for (default both).
    pub encoding: Option<StringEncoding>,
    /// Matches to skip (paging).
    pub offset: Option<u32>,
    /// Max rows (default 200, max 500).
    pub limit: Option<u32>,
    /// Header only (default false).
    pub count_only: Option<bool>,
}

/// Parameters for `symbols`.
#[derive(Debug, Default, serde::Deserialize, schemars::JsonSchema)]
#[serde(deny_unknown_fields)]
pub struct SymbolsParams {
    /// One kind of symbol only (default every kind); drops the kind column.
    pub kind: Option<SymbolKind>,
    /// Case-insensitive substring of the raw (module included) or demangled name.
    pub filter: Option<String>,
    /// Matches to skip (paging).
    pub offset: Option<u32>,
    /// Max rows (default 50, max 1000).
    pub limit: Option<u32>,
    /// Header only (default false).
    pub count_only: Option<bool>,
}

/// The order `functions` lists in.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default, serde::Deserialize, schemars::JsonSchema)]
#[serde(rename_all = "lowercase")]
pub enum FunctionSort {
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
#[derive(Debug, Default, serde::Deserialize, schemars::JsonSchema)]
#[serde(deny_unknown_fields)]
pub struct FunctionsParams {
    /// Case-insensitive filter on name or entry hex; `thunk` or `funclet` lists what is otherwise left out.
    pub filter: Option<String>,
    /// `address` (default) or `size` for the largest first.
    pub sort: Option<FunctionSort>,
    /// Matches to skip (paging).
    pub offset: Option<u32>,
    /// Max rows (default 50, max 300).
    pub limit: Option<u32>,
    /// Header only (default false).
    pub count_only: Option<bool>,
}

/// Parameters for `function_summary` and `function_strings`.
#[derive(Debug, serde::Deserialize, schemars::JsonSchema)]
#[serde(deny_unknown_fields)]
pub struct FunctionParams {
    /// Entry, any address inside it, or a name.
    pub address: String,
}

/// Parameters for `function`.
#[derive(Debug, serde::Deserialize, schemars::JsonSchema)]
#[serde(deny_unknown_fields)]
pub struct FunctionDetailParams {
    /// Entry, any address inside it, or a name.
    pub address: String,
    /// Blocks to skip first (300 a page).
    pub offset: Option<u32>,
}

/// Parameters for `xrefs`.
#[derive(Debug, Default, serde::Deserialize, schemars::JsonSchema)]
#[serde(deny_unknown_fields)]
pub struct XrefsParams {
    /// Address or name (function, import, overlay name), or Class+offset.
    pub address: String,
    /// Groups to skip first (paging).
    pub offset: Option<u32>,
    /// Max groups (default 60, max 500).
    pub limit: Option<u32>,
    /// Header only (default false).
    pub count_only: Option<bool>,
}

/// Parameters for `callgraph`.
#[derive(Debug, serde::Deserialize, schemars::JsonSchema)]
#[serde(deny_unknown_fields)]
pub struct CallgraphParams {
    /// Root function entry address.
    pub address: String,
    /// Maximum graph nodes (default 30, max 100).
    pub max_nodes: Option<u32>,
    /// What reaches it instead of what it calls.
    pub callers: Option<bool>,
}

/// Parameters for `reaches`.
#[derive(Debug, serde::Deserialize, schemars::JsonSchema)]
#[serde(deny_unknown_fields)]
pub struct ReachesParams {
    /// Function the call chain starts at.
    pub from: String,
    /// Target function, or an import by name or slot.
    pub to: String,
    /// Longest chain to follow (default 24, max 64).
    pub depth: Option<u32>,
}

/// Parameters for `find_crypto_constants`.
#[derive(Debug, serde::Deserialize, schemars::JsonSchema)]
#[serde(deny_unknown_fields)]
pub struct CryptoParams {
    /// Rows to skip (paging).
    pub offset: Option<u32>,
    /// Max rows (default 200, max 500).
    pub limit: Option<u32>,
}

/// Parameters for `cfg`.
#[derive(Debug, serde::Deserialize, schemars::JsonSchema)]
#[serde(deny_unknown_fields)]
pub struct CfgParams {
    /// Function entry or any address inside it.
    pub address: String,
    /// Blocks to skip, 300 a page.
    pub offset: Option<u32>,
}

/// Parameters for `decompile`.
#[derive(Debug, Default, serde::Deserialize, schemars::JsonSchema)]
#[serde(deny_unknown_fields)]
pub struct DecompileParams {
    /// Function entry or any address inside it.
    pub address: String,
    /// `skeleton` for flow and calls only; `full` or absent for all of it.
    pub detail: Option<Detail>,
    /// Keep only lines containing this text, case-insensitively.
    pub filter: Option<String>,
    /// Skip this many lines of the answer.
    pub offset: Option<u32>,
    /// Return at most this many lines (default 300; more than the text has for all).
    pub limit: Option<u32>,
}

/// Parameters for `query`.
#[derive(Debug, serde::Deserialize, schemars::JsonSchema)]
#[serde(deny_unknown_fields)]
pub struct QueryParams {
    /// A borer:// resource URI.
    pub uri: String,
}

/// Parameters for `search`.
#[derive(Debug, Default, serde::Deserialize, schemars::JsonSchema)]
#[serde(deny_unknown_fields)]
pub struct SearchParams {
    /// Hex bytes with ?? wildcards (kind=bytes) or a literal substring (kind=text).
    pub query: String,
    /// What the query is (default bytes).
    pub kind: Option<SearchKind>,
    /// Hits to skip (default 0).
    pub offset: Option<usize>,
    /// Max hits (default 200, max 500).
    pub limit: Option<u32>,
    /// Header only (default false).
    pub count_only: Option<bool>,
}

/// Parameters for `types`.
#[derive(Debug, Default, serde::Deserialize, schemars::JsonSchema)]
#[serde(deny_unknown_fields)]
pub struct TypesParams {
    /// Substring filter on name or applied address.
    pub filter: Option<String>,
    /// Rows to skip first (paging).
    pub offset: Option<u32>,
    /// Max rows (default 50, max 500).
    pub limit: Option<u32>,
    /// Header only (default false).
    pub count_only: Option<bool>,
}

/// Parameters for `annotations`.
#[derive(Debug, Default, serde::Deserialize, schemars::JsonSchema)]
#[serde(deny_unknown_fields)]
pub struct AnnotationsParams {
    /// Case-insensitive substring of a row (address, kind or text).
    pub filter: Option<String>,
    /// Rows to skip first (paging).
    pub offset: Option<u32>,
    /// Max rows (default 200, max 1000).
    pub limit: Option<u32>,
    /// Header only (default false).
    pub count_only: Option<bool>,
}

/// Widens a count parameter to the index type.
///
/// A `u32` fits a 32-bit or wider `usize`, so nothing is lost on any
/// target borer builds for; the saturation only states the rule.
///
/// # Arguments
///
/// * `n` - The parameter as given.
pub fn to_usize(n: u32) -> usize {
    usize::try_from(n).unwrap_or(usize::MAX)
}

/// A count parameter the cap cut: its name, what was asked, and the cap.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Capped {
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
pub struct Count {
    /// The value in force, at or under the cap.
    pub n: usize,
    /// What the cap cut, `None` when the value was taken as asked.
    pub capped: Option<Capped>,
}

impl Count {
    /// Puts the line saying what the cap cut ahead of an answer, so a
    /// caller who asked for more learns it got the cap and not everything;
    /// an answer within the cap is returned as it is.
    ///
    /// # Arguments
    ///
    /// * `text` - The answer.
    pub fn noted(self, text: String) -> String {
        self.noted_with("#", text)
    }

    /// [`Count::noted`] with the line opened by `mark`: `%%` ahead of a
    /// mermaid graph, where a `#` line does not parse.
    ///
    /// # Arguments
    ///
    /// * `mark` - What opens a comment line in the answer's language.
    /// * `text` - The answer.
    pub fn noted_with(self, mark: &str, text: String) -> String {
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
pub fn count_param(
    v: Option<u32>,
    default: usize,
    max: usize,
    what: &'static str,
) -> Result<Count, Failure> {
    match v {
        None => Ok(Count {
            n: default,
            capped: None,
        }),
        Some(0) => Err(Failure::asked(format!("{what} must be at least 1"))),
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
pub struct Page {
    /// Matches to skip first.
    pub offset: usize,
    /// Most rows shown, at or under the tool's cap, with the cut when the
    /// cap made one.
    pub limit: Count,
    /// Header line only.
    pub count_only: bool,
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
    pub fn new(
        offset: Option<u32>,
        limit: Option<u32>,
        count_only: Option<bool>,
        default: usize,
        max: usize,
    ) -> Result<Page, Failure> {
        Ok(Page {
            offset: to_usize(offset.unwrap_or(0)),
            limit: count_param(limit, default, max, "limit")?,
            count_only: count_only.unwrap_or(false),
        })
    }
}

/// What the parameter parser starts a refused argument's message with.
pub const DESERIALIZE_PREFIX: &str = "failed to deserialize parameters:";

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
#[must_use]
pub fn misfit(
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
