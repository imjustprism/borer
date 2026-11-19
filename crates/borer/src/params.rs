//! Tool and prompt parameters: what each MCP call accepts, as the JSON
//! schema an agent reads before it calls.

pub(crate) use borer_engine::analysis::settable::{Annotation, must_be_in_a_section};
use borer_engine::program;
use rmcp::schemars;

pub(crate) use borer_engine::analysis::fieldrefs::{parse_field_offset, parse_unsigned};
pub(crate) use borer_engine::text::Filter;
pub(crate) use borer_front::tools::params::*;

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

/// Parameters for `decompile_batch`.
#[derive(Debug, serde::Deserialize, schemars::JsonSchema)]
#[serde(deny_unknown_fields)]
pub(crate) struct DecompileBatchParams {
    /// Filter on name or entry hex, as `functions` reads it.
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
    /// Address or name; `live:0x..` is not rebased.
    pub(crate) address: String,
    /// Default u64.
    pub(crate) kind: Option<ReadKind>,
    /// Values (default 1, max 256).
    pub(crate) count: Option<u32>,
}

/// Parameters for `live_object`.
#[derive(Debug, serde::Deserialize, schemars::JsonSchema)]
#[serde(deny_unknown_fields)]
pub(crate) struct LiveObjectParams {
    /// Address or name.
    pub(crate) address: String,
    /// Default: by its vtable.
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
    /// Start a watch here; omit to diff.
    pub(crate) address: Option<String>,
    /// Bytes (default: class size or 256; max 65536).
    pub(crate) length: Option<u32>,
    /// Default: by its vtable.
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
    /// No set: the pointer chains to the address `value` names.
    Path,
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
    /// Result set name.
    pub(crate) name: String,
    /// compare=equal: the new value; path: address[,depth=1..6][,max_offset=n].
    pub(crate) value: Option<String>,
    /// Default u32; bytes: hex, ?? wildcard.
    pub(crate) kind: Option<ScanKind>,
    /// Float range (default: half the last digit).
    pub(crate) tolerance: Option<f64>,
    /// Narrow set `name`.
    pub(crate) compare: Option<ScanCompare>,
    /// Default all.
    pub(crate) scope: Option<ScanScope>,
    /// For scope=module or compare=path.
    pub(crate) module: Option<String>,
    /// Hits to skip.
    pub(crate) offset: Option<u32>,
    /// Max rows (default 50, max 500; path 20, 200).
    pub(crate) limit: Option<u32>,
    /// Header line only.
    pub(crate) count_only: Option<bool>,
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

    /// An annotation in a section the file holds no bytes for is in the
    /// image, so it passes.
    ///
    /// # Panics
    ///
    /// When an address in `.bss` is refused as in no section.
    #[test]
    fn an_annotation_in_a_section_without_file_bytes_passes() {
        use borer_engine::program::{Arch, Program, Section};
        let mut bss = Section::mapped(".bss", 0x2000, 0, 0x100, true, false);
        bss.file_size = 0;
        let p = Program::raw(vec![0xc3; 0x10], Arch::X86_64, 0, None, vec![bss]);
        assert_eq!(must_be_in_a_section(&p, 0x2010, Annotation::Name), Ok(()));
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

    /// `set_type` names and types the stack slot the text shows by a name,
    /// on arm64, ARM32 and RISC-V as on x86, and says so by that name.
    ///
    /// The server worked the slot out from the file's format and width, by
    /// x86's rule: on arm64 `arg_8` named the slot the text calls `arg_10`,
    /// so the text kept `arg_8`, and the answer said `home_8`.
    ///
    /// # Panics
    ///
    /// When an answer spells another name, or a text keeps the old one or
    /// does not declare the slot of the stated type.
    #[test]
    fn set_type_names_the_slot_the_text_shows() {
        use crate::params::{DecompileParams, SetTypeParams};
        use borer_engine::program::Arch;
        use rmcp::handler::server::wrapper::Parameters;
        let words = |ws: &[u32]| -> Vec<u8> { ws.iter().flat_map(|w| w.to_le_bytes()).collect() };
        let cases = [
            (
                Arch::X86_64,
                vec![
                    0x48, 0x8b, 0x44, 0x24, 0x08, // ASM: mov rax, [rsp+8]
                    0xc3, // ASM: ret
                ],
                "home_0",
                "int64_t",
            ),
            (
                Arch::Arm64,
                words(&[
                    0xf940_07e0, // ASM: ldr x0, [sp, #8]
                    0xd65f_03c0, // ASM: ret
                ]),
                "arg_8",
                "int64_t",
            ),
            (
                Arch::Arm,
                words(&[
                    0xe59d_0006, // ASM: ldr r0, [sp, #6]
                    0xe12f_ff1e, // ASM: bx lr
                ]),
                "arg_6",
                "int32_t",
            ),
            (
                Arch::RiscV64,
                words(&[
                    0x0081_3503, // ASM: ld a0, 8(sp)
                    0x0000_8067, // ASM: ret
                ]),
                "arg_8",
                "int64_t",
            ),
            (
                Arch::RiscV32,
                words(&[
                    0x0041_2503, // ASM: lw a0, 4(sp)
                    0x0000_8067, // ASM: ret
                ]),
                "arg_4",
                "int32_t",
            ),
        ];
        for (arch, code, shown, ty) in cases {
            let server = crate::testing::code_server(arch, &code);
            let said = server
                .set_type(Parameters(SetTypeParams {
                    name: Some("kept".to_owned()),
                    fields: None,
                    values: None,
                    size: None,
                    address: Some("0x1000".to_owned()),
                    r#type: Some(ty.to_owned()),
                    var: Some(shown.to_owned()),
                    dry_run: Some(false),
                    ..SetTypeParams::default()
                }))
                .unwrap_or_else(|e| e.message.into_owned());
            assert_eq!(
                said,
                format!("named {shown} of sub_1000 (0x1000) {ty} kept"),
                "{arch:?}"
            );
            let text = borer_front::tools::decompile(
                &server,
                &DecompileParams {
                    address: "0x1000".to_owned(),
                    detail: None,
                    filter: None,
                    offset: None,
                    limit: None,
                },
            )
            .map_err(crate::errors::failed)
            .unwrap_or_else(|e| e.message.into_owned());
            assert!(
                text.contains(&format!("\n{ty} kept;\n")) && !text.contains(shown),
                "{arch:?}: {text}"
            );
        }
    }
}
