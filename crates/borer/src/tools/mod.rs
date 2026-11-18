//! The tool handlers the server keeps, and the router of the catalog's tools.
//!
//! The server's own are one module per area, each with its own router; the
//! catalog's come from [`borer_front::tools::TOOLS`]. `main.rs` sums them
//! into the one the server answers by.

pub(crate) mod annotate;
pub(crate) mod bytes;
pub(crate) mod decompile;
pub(crate) mod functions;
pub(crate) mod live;
pub(crate) mod livescan;
pub(crate) mod load;
pub(crate) mod query;
pub(crate) mod search;

use std::sync::Arc;

use rmcp::handler::server::router::tool::{ToolRoute, ToolRouter};
use rmcp::handler::server::tool::ToolCallContext;
use rmcp::model::{CallToolResult, ContentBlock, Tool, ToolAnnotations};

use crate::BorerServer;
use crate::errors::failed;
use crate::safety::effects;

/// Returns the router of the catalog's tools, each listed as its row says
/// and answered by its handler over the server's state.
///
/// A row's definition is what the `#[tool]` attribute made of it: its name,
/// description and parameters' schema as derived, its four hints and, when
/// it touches more than the program, its effects in `_meta`. A call parses
/// its arguments and runs the handler; a failure answers as a server tool's
/// does ([`failed`]).
pub(crate) fn catalog() -> ToolRouter<BorerServer> {
    borer_front::tools::TOOLS
        .iter()
        .fold(ToolRouter::new(), |router, t| {
            let hints = t.hints;
            let mut attr =
                Tool::new_with_raw(t.name, Some(t.description.into()), Arc::new((t.schema)()))
                    .with_annotations(ToolAnnotations::from_raw(
                        None,
                        Some(hints.read_only),
                        Some(hints.destructive),
                        Some(hints.idempotent),
                        Some(hints.open_world),
                    ));
            if !t.effects.is_empty() {
                attr = attr.with_meta(effects(t.effects));
            }
            router.with_route(ToolRoute::new_dyn(
                attr,
                move |call: ToolCallContext<'_, BorerServer>| {
                    let answer = (t.run)(call.service, call.arguments.unwrap_or_default())
                        .map(|text| CallToolResult::success(vec![ContentBlock::text(text)]).into())
                        .map_err(failed);
                    Box::pin(std::future::ready(answer))
                },
            ))
        })
}

#[cfg(test)]
mod tests {
    use borer_front::tools::{SERVER_ONLY, TOOLS};
    use rmcp::handler::server::common::schema_for_input;

    use crate::params::{
        AnnotationsParams, CallgraphParams, CfgParams, CryptoParams, DecompileParams,
        DisassembleFunctionParams, DisassembleParams, EntropyParams, FindFunctionByStringParams,
        FunctionDetailParams, FunctionParams, FunctionsParams, HexdumpParams, QueryParams,
        ReachesParams, ReadParams, SearchParams, StringsParams, SymbolsParams, TypesParams,
        XrefsParams,
    };

    /// The tool list the app builds from the catalog is the MCP server's,
    /// tool for tool.
    ///
    /// Every catalog row is a listed tool with the same description, hints
    /// and slimmed schema, its schema derived as the MCP SDK derives its
    /// parameters' (`schema_for_input`); every other listed tool is one the
    /// server keeps for a stated reason, and every such tool is listed (the
    /// live tools on Windows only).
    ///
    /// # Panics
    ///
    /// When a row and its listing differ, or a tool is in neither table.
    #[test]
    fn the_catalog_lists_as_the_server_lists() {
        let router = crate::BorerServer::tool_router();
        for t in TOOLS {
            let listed = crate::slim_tool(router.get(t.name).cloned().expect("listed"));
            assert_eq!(
                listed.description.as_deref(),
                Some(t.description),
                "{}",
                t.name
            );
            assert_eq!(*listed.input_schema, t.input_schema(), "{}", t.name);
            let hints = listed.annotations.expect("annotated");
            assert_eq!(hints.read_only_hint, Some(t.hints.read_only), "{}", t.name);
            assert_eq!(
                hints.open_world_hint,
                Some(t.hints.open_world),
                "{}",
                t.name
            );
        }
        let derived = [
            ("annotations", schema_for_input::<AnnotationsParams>()),
            ("callgraph", schema_for_input::<CallgraphParams>()),
            ("cfg", schema_for_input::<CfgParams>()),
            ("decompile", schema_for_input::<DecompileParams>()),
            ("disassemble", schema_for_input::<DisassembleParams>()),
            (
                "disassemble_function",
                schema_for_input::<DisassembleFunctionParams>(),
            ),
            ("entropy", schema_for_input::<EntropyParams>()),
            ("find_crypto_constants", schema_for_input::<CryptoParams>()),
            (
                "find_function_by_string",
                schema_for_input::<FindFunctionByStringParams>(),
            ),
            ("function", schema_for_input::<FunctionDetailParams>()),
            ("function_strings", schema_for_input::<FunctionParams>()),
            ("function_summary", schema_for_input::<FunctionParams>()),
            ("functions", schema_for_input::<FunctionsParams>()),
            ("hexdump", schema_for_input::<HexdumpParams>()),
            ("query", schema_for_input::<QueryParams>()),
            ("reaches", schema_for_input::<ReachesParams>()),
            ("read", schema_for_input::<ReadParams>()),
            ("search", schema_for_input::<SearchParams>()),
            ("strings", schema_for_input::<StringsParams>()),
            ("symbols", schema_for_input::<SymbolsParams>()),
            ("types", schema_for_input::<TypesParams>()),
            ("xrefs", schema_for_input::<XrefsParams>()),
        ];
        assert_eq!(derived.len(), TOOLS.len());
        for (name, schema) in derived {
            let row = borer_front::tools::tool(name).expect("a catalog row");
            assert_eq!(Ok((row.schema)()), schema.map(|s| (*s).clone()), "{name}");
        }
        let kept: Vec<&str> = SERVER_ONLY
            .iter()
            .map(|(name, _)| *name)
            .filter(|name| cfg!(windows) || !name.starts_with("live_"))
            .collect();
        let mut both: Vec<&str> = TOOLS.iter().map(|t| t.name).chain(kept).collect();
        both.sort_unstable();
        let listed: Vec<String> = router
            .list_all()
            .into_iter()
            .map(|t| t.name.into_owned())
            .collect();
        assert_eq!(listed, both);
    }

    /// Every catalog tool answers the same bytes through the plainest front
    /// end as through the server.
    ///
    /// The plainest front end is [`borer_front::tools::Loaded`], over the
    /// server's program, analysis and names; the bytes are answers, refusals
    /// and the field a bad argument names. The server's `query` adds its session's lines,
    /// left out here.
    ///
    /// # Panics
    ///
    /// When a tool answers otherwise on the two faces.
    #[test]
    fn every_catalog_tool_answers_alike_through_a_plain_front_end() {
        use borer_engine::program::Arch;
        let code = [
            0x48, 0x8d, 0x41, 0x01, // ASM: lea rax, [rcx+1]
            0xe8, 0x01, 0x00, 0x00, 0x00, // ASM: call 0x100a
            0xc3, // ASM: ret
            0x31, 0xc0, // ASM: xor eax, eax
            0xc3, // ASM: ret
        ];
        let calls = [
            ("annotations", serde_json::json!({})),
            ("callgraph", serde_json::json!({"address": "0x1000"})),
            ("cfg", serde_json::json!({"address": "0x1000"})),
            ("decompile", serde_json::json!({"address": "0x1000"})),
            (
                "disassemble",
                serde_json::json!({"address": "0x1000", "count": 4}),
            ),
            (
                "disassemble_function",
                serde_json::json!({"address": "sub_1000"}),
            ),
            ("entropy", serde_json::json!({"window": 64})),
            ("find_crypto_constants", serde_json::json!({})),
            (
                "find_function_by_string",
                serde_json::json!({"filter": "x"}),
            ),
            ("function", serde_json::json!({"address": "0x1000"})),
            ("function_strings", serde_json::json!({"address": "0x1000"})),
            ("function_summary", serde_json::json!({"address": "0x1000"})),
            ("functions", serde_json::json!({})),
            ("functions", serde_json::json!({"limit": "x"})),
            (
                "hexdump",
                serde_json::json!({"address": "0x1000", "length": 16}),
            ),
            ("query", serde_json::json!({"uri": "borer://disasm/0x1000"})),
            (
                "reaches",
                serde_json::json!({"from": "0x1000", "to": "0x100a"}),
            ),
            (
                "read",
                serde_json::json!({"address": "sub_1000", "count": 2}),
            ),
            ("search", serde_json::json!({"query": "c3"})),
            ("strings", serde_json::json!({})),
            ("symbols", serde_json::json!({})),
            ("types", serde_json::json!({})),
            ("xrefs", serde_json::json!({"address": "0x100a"})),
            ("xrefs", serde_json::json!({"address": "nosuch"})),
        ];
        let session = |text: String| {
            text.lines()
                .filter(|l| !l.starts_with("# since=") && !l.starts_with("# evidence:"))
                .collect::<Vec<_>>()
                .join("\n")
        };
        for server in [
            crate::testing::raw_server(),
            crate::testing::code_server(Arch::X86_64, &code),
        ] {
            let plain = borer_front::tools::Loaded {
                program: server.loaded().expect("loaded"),
                analysis: server.analysis_or_empty(),
                overlay: server.overlay_plain(),
            };
            let mut reached: Vec<&str> = Vec::new();
            for (name, args) in &calls {
                let t = borer_front::tools::tool(name).expect("a catalog tool");
                let args = args.as_object().cloned().unwrap_or_default();
                let served = (t.run)(&server, args.clone()).map(session);
                let plainly = (t.run)(&plain, args).map(session);
                assert_eq!(served, plainly, "{name}");
                reached.push(name);
            }
            assert!(TOOLS.iter().all(|t| reached.contains(&t.name)));
        }
    }
}
