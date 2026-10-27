//! The tools that describe functions and how they connect: summaries,
//! listings, cross-references, class layouts, the call graph and the CFG.

use borer_engine::analysis::{Analysis, Overlay, parse_addr, render, resolve};
use borer_engine::program::{Feature, Program};
use rmcp::handler::server::wrapper::Parameters;
use rmcp::{ErrorData, tool, tool_router};

use crate::BorerServer;
use crate::params::{
    CallgraphParams, CfgParams, ClassLayoutParams, FunctionDetailParams, FunctionParams,
    FunctionsParams, Page, ReachesParams, XrefsParams, count_param, to_usize,
};
use crate::safety::{Effect, effects};
use crate::state::write_lock;

impl BorerServer {
    /// Answers a recovered layout's plan: what it would define and state,
    /// or, applied, what it did.
    ///
    /// The struct and the prototypes are written to the overlay unless
    /// `dry`, as `class_layout` and `borer://layout/...,apply=<Name>` do.
    ///
    /// # Arguments
    ///
    /// * `plan` - The plan ([`borer_engine::analysis::apply`]).
    /// * `a` - The analysis, to name the functions.
    /// * `o` - The overlay the plan was made under.
    /// * `dry` - Say what would be done and write nothing.
    ///
    /// # Returns
    ///
    /// A line saying what was (or would be) done, then the plan's lines.
    pub(crate) fn answer_plan(
        &self,
        plan: borer_engine::analysis::apply::Plan,
        a: &Analysis,
        o: &Overlay,
        dry: bool,
    ) -> String {
        let head = format!(
            "{} struct {} and {} {} prototype(s); decompile then names the fields:\n",
            if dry {
                "dry-run: would define"
            } else {
                "defined"
            },
            plan.name,
            if dry { "state" } else { "stated" },
            plan.prototypes.len()
        );
        let mut out = head;
        for line in plan.describe(a, o) {
            out.push_str(&line);
            out.push('\n');
        }
        if dry {
            out.push_str("pass dry_run=false to apply.\n");
            return out;
        }
        let before = self.overlay_plain();
        plan.apply(&mut write_lock(&self.overlay));
        self.names_changed(&before);
        out
    }
}

#[tool_router(router = function_tools, vis = "pub(crate)")]
impl BorerServer {
    /// Returns the one-call triage of a function.
    ///
    /// # Arguments
    ///
    /// * `FunctionParams` - Destructured tool parameters (see its field docs).
    ///
    /// # Errors
    ///
    /// When no binary is loaded or the address is not inside a discovered function.
    #[tool(
        description = "Triage one function in one call: shape, loops, jump tables, callers, callees, strings and data, then `# next:` lines. Use it before decompile; for the raw block table use function.",
        annotations(
            read_only_hint = true,
            destructive_hint = false,
            idempotent_hint = true,
            open_world_hint = false
        )
    )]
    pub(crate) fn function_summary(
        &self,
        Parameters(FunctionParams { address }): Parameters<FunctionParams>,
    ) -> Result<String, ErrorData> {
        self.with_program(|p| {
            let a = self.ensure_analysis()?;
            let entry = self.function_entry(p, &a, &address)?;
            render::function_summary(p, &a, &self.overlay(), entry)
                .ok_or_else(|| format!("no function at {entry:#x}"))
        })
    }

    /// Lists the string literals a function references.
    ///
    /// # Arguments
    ///
    /// * `FunctionParams` - Destructured tool parameters (see its field docs).
    ///
    /// # Errors
    ///
    /// When no binary is loaded or the address is not inside a discovered function.
    #[tool(
        description = "List the string literals one function references as `site string_va text` rows, at most 100. Not for finding a text's functions (use find_function_by_string).",
        annotations(
            read_only_hint = true,
            destructive_hint = false,
            idempotent_hint = true,
            open_world_hint = false
        )
    )]
    pub(crate) fn function_strings(
        &self,
        Parameters(FunctionParams { address }): Parameters<FunctionParams>,
    ) -> Result<String, ErrorData> {
        self.with_analysis(Feature::Discover, |p, a, o| {
            let entry = self.function_entry(p, a, &address)?;
            render::function_strings_tsv(p, a, o, entry)
                .ok_or_else(|| format!("no function at {entry:#x}"))
        })
    }

    /// Lists discovered functions with filtering and paging.
    ///
    /// The count alone is the table's header without its page: `filter=thunk`
    /// counts import thunks and says so, where a bare `functions` read as
    /// though it counted every function.
    ///
    /// # Arguments
    ///
    /// * `FunctionsParams` - Destructured tool parameters (see its field docs).
    ///
    /// # Errors
    ///
    /// When no binary is loaded or the analysis is unavailable.
    #[tool(
        description = "List discovered functions as `entry size blocks instrs callers callees src name` rows, paged; filter on name or entry hex, sort=size for the largest. Not for imports (use symbols).",
        annotations(
            read_only_hint = true,
            destructive_hint = false,
            idempotent_hint = true,
            open_world_hint = false
        )
    )]
    pub(crate) fn functions(
        &self,
        Parameters(FunctionsParams {
            filter,
            sort,
            offset,
            limit,
            count_only,
        }): Parameters<FunctionsParams>,
    ) -> Result<String, ErrorData> {
        let page = Page::new(offset, limit, count_only, 50, 300)?;
        let order = sort.unwrap_or_default().into();
        self.with_analysis(Feature::Discover, |_, a, o| {
            let (shown, _, text) =
                render::functions_tsv(a, o, filter.as_deref(), order, page.offset, page.limit.n);
            if page.count_only {
                let head = text.lines().next().unwrap_or_default();
                let counted = head
                    .strip_prefix(&format!("# showing {shown} of "))
                    .unwrap_or(head);
                return Ok(format!("# {counted}\n"));
            }
            Ok(text)
        })
        .map(|text| page.limit.noted(text))
    }

    /// Returns one function's detail and one page of its basic-block table.
    ///
    /// # Arguments
    ///
    /// * `FunctionDetailParams` - Destructured tool parameters (see its field docs).
    ///
    /// # Errors
    ///
    /// When no binary is loaded or the address is not inside a discovered function.
    #[tool(
        description = "Show one function's raw facts: range, counts, callers, callees and block table (`start size term successors`), 300 blocks a page. Not for a readable triage (use function_summary).",
        annotations(
            read_only_hint = true,
            destructive_hint = false,
            idempotent_hint = true,
            open_world_hint = false
        )
    )]
    pub(crate) fn function(
        &self,
        Parameters(FunctionDetailParams { address, offset }): Parameters<FunctionDetailParams>,
    ) -> Result<String, ErrorData> {
        let offset = to_usize(offset.unwrap_or(0));
        self.with_analysis(Feature::Discover, |p, a, o| {
            let entry = self.function_entry(p, a, &address)?;
            render::function_detail(a, o, entry, offset)
                .ok_or_else(|| format!("no function at {entry:#x}"))
        })
    }

    /// Lists cross-references to an address or name, or the functions using
    /// a class's field.
    ///
    /// A target that is neither an address nor a name is read as
    /// `Class+offset` ([`class_field`]): the readers and writers of that
    /// field through pointers typed as the class
    /// ([`borer_engine::analysis::classes::typed_field_uses`]), one row per
    /// function: a byte search by offset finds every object's field at that
    /// offset, and a filter on function names misses the unnamed writers.
    ///
    /// # Arguments
    ///
    /// * `XrefsParams` - Destructured tool parameters (see its field docs).
    ///
    /// # Errors
    ///
    /// When no binary is loaded or the target resolves to neither an address
    /// nor a class field.
    #[tool(
        description = "List references to an address or name, one row per function, paged; an import lists calls through its slot, `Class+0x24` who touches that field. Not for call paths (use reaches).",
        annotations(
            read_only_hint = true,
            destructive_hint = false,
            idempotent_hint = true,
            open_world_hint = false
        )
    )]
    pub(crate) fn xrefs(
        &self,
        Parameters(XrefsParams {
            address,
            offset,
            limit,
            count_only,
        }): Parameters<XrefsParams>,
    ) -> Result<String, ErrorData> {
        let page = Page::new(
            offset,
            limit,
            count_only,
            render::XREF_ROWS_DEFAULT,
            render::XREF_ROWS_MAX,
        )?;
        self.with_analysis(Feature::Discover, |p, a, o| {
            let va = match self.addr(p, &address) {
                Ok(va) => va,
                Err(unknown) => {
                    let (class, offset) = class_field(p, a, o, &address).ok_or_else(|| {
                        format!(
                            "{unknown}; nor is it Class+offset, a field of a class with methods or a vtable"
                        )
                    })?;
                    if let Some(why) = p.refuses(Feature::Decompile) {
                        return Err(format!(
                            "{class}+{offset:#x} is a field, read from decompiled methods: {why}"
                        ));
                    }
                    let uses = borer_engine::analysis::classes::typed_field_uses(p, a, o, &class, offset)
                        .ok_or_else(|| format!("no class {class}"))?;
                    return Ok(borer_engine::analysis::classes::typed_field_uses_tsv(
                        &uses,
                        a,
                        o,
                        offset,
                        page.offset,
                        page.limit.n,
                        page.count_only,
                    ));
                }
            };
            Ok(render::xrefs_tsv(
                p,
                a,
                o,
                va,
                page.offset,
                page.limit.n,
                page.count_only,
            ))
        })
        .map(|text| page.limit.noted(text))
    }

    /// Renders a class layout recovered from its methods' field accesses,
    /// or with `apply` defines it as a user struct and types each method's
    /// object with it ([`borer_engine::analysis::apply::from_class`]).
    ///
    /// # Arguments
    ///
    /// * `ClassLayoutParams` - Destructured tool parameters (see its field docs).
    ///
    /// # Errors
    ///
    /// When no binary is loaded, the address is not a class method, nothing
    /// belongs to the class, or the struct to apply is refused.
    #[tool(
        description = "Infer a C++ class's fields, methods and vftable from how its methods use the object: offset, width, reads, writes. Use it on an unknown class; for a known layout use set_type. apply=Name saves it as a struct (dry run until dry_run=false).",
        meta = effects(&[Effect::ChangesSession]),
        annotations(
            read_only_hint = false,
            destructive_hint = false,
            idempotent_hint = true,
            open_world_hint = false
        )
    )]
    pub(crate) fn class_layout(
        &self,
        Parameters(ClassLayoutParams {
            class,
            apply,
            dry_run,
        }): Parameters<ClassLayoutParams>,
    ) -> Result<String, ErrorData> {
        self.with_analysis(Feature::Decompile, |p, a, o| {
            let name = match self.function_entry(p, a, &class) {
                Ok(entry) => {
                    let n = borer_engine::analysis::name_of(a, o, entry);
                    borer_engine::analysis::classes::class_of(&n)
                        .ok_or_else(|| format!("{n} is not a class method"))?
                        .to_owned()
                }
                Err(_) => class.clone(),
            };
            let layout =
                borer_engine::analysis::classes::class_layout(p, a, o, &name).ok_or_else(|| {
                    format!(
                        "no function belongs to class {}",
                        borer_engine::text::quoted(&name)
                    )
                })?;
            let Some(apply) = &apply else {
                return Ok(borer_engine::analysis::classes::render_layout(
                    &layout, a, o,
                ));
            };
            let plan = borer_engine::analysis::apply::from_class(p, a, o, &layout, apply)?;
            Ok(self.answer_plan(plan, a, o, dry_run.unwrap_or(true)))
        })
    }

    /// Renders the callee graph from a function as mermaid.
    ///
    /// Walking callers from an import or a data symbol answers who
    /// references it; it has no body to walk callees from.
    ///
    /// # Arguments
    ///
    /// * `CallgraphParams` - Destructured tool parameters (see its field docs).
    ///
    /// # Errors
    ///
    /// When no binary is loaded or the address is not inside a discovered function.
    #[tool(
        description = "Draw a function's call graph as mermaid: callees, or callers with callers=true; imports are leaves and a %% line counts nodes cut by max_nodes. Not for one path (use reaches) or a caller list (use xrefs).",
        annotations(
            read_only_hint = true,
            destructive_hint = false,
            idempotent_hint = true,
            open_world_hint = false
        )
    )]
    pub(crate) fn callgraph(
        &self,
        Parameters(CallgraphParams {
            address,
            max_nodes,
            callers,
        }): Parameters<CallgraphParams>,
    ) -> Result<String, ErrorData> {
        let max = count_param(max_nodes, 30, 100, "max_nodes")?;
        let callers = callers.unwrap_or(false);
        self.with_analysis(Feature::Discover, |p, a, o| {
            let root = match self.function_entry(p, a, &address) {
                Ok(root) => root,
                Err(e) => {
                    let va = self.addr(p, &address)?;
                    if callers && (a.symbol_at(p, va).is_some() || a.xrefs.contains_key(&va)) {
                        va
                    } else {
                        return Err(e);
                    }
                }
            };
            Ok(render::callgraph_mermaid(p, a, o, root, max.n, callers))
        })
        .map(|text| max.noted_with("%%", text))
    }

    /// Answers whether one function reaches another through calls.
    ///
    /// The goal may be an import with no thunk, called through its slot:
    /// it was refused for want of a function containing the slot.
    ///
    /// # Arguments
    ///
    /// * `ReachesParams` - Destructured tool parameters (see its field docs).
    ///
    /// # Errors
    ///
    /// When no binary is loaded, `from` is not inside a discovered function,
    /// or `to` is neither inside one nor an import.
    #[tool(
        description = "Find the shortest call chain from one function to another or to an import, or say none exists within depth. Not for the whole neighbourhood (use callgraph) or direct callers (use xrefs).",
        annotations(
            read_only_hint = true,
            destructive_hint = false,
            idempotent_hint = true,
            open_world_hint = false
        )
    )]
    pub(crate) fn reaches(
        &self,
        Parameters(ReachesParams { from, to, depth }): Parameters<ReachesParams>,
    ) -> Result<String, ErrorData> {
        let deep = count_param(depth, 24, 64, "depth")?;
        self.with_analysis(Feature::Discover, |p, a, o| {
            let start = self.function_entry(p, a, &from)?;
            let goal = match self.function_entry(p, a, &to) {
                Ok(goal) => goal,
                Err(e) => {
                    let va = self.addr(p, &to)?;
                    if a.symbol_at(p, va)
                        .is_some_and(|s| s.kind == borer_engine::program::SymbolKind::Import)
                    {
                        va
                    } else {
                        return Err(e);
                    }
                }
            };
            Ok(render::call_path(p, a, o, start, goal, deep.n))
        })
        .map(|text| deep.noted(text))
    }

    /// Renders a function's control-flow graph as mermaid.
    ///
    /// # Arguments
    ///
    /// * `CfgParams` - Destructured tool parameters (see its field docs).
    ///
    /// # Errors
    ///
    /// When no binary is loaded or the address is not inside a discovered function.
    #[tool(
        description = "Draw a function's control-flow graph as mermaid: blocks and successor edges, 300 blocks a page, a %% line when cut. Not for reading logic (use decompile) or a block table (use function).",
        annotations(
            read_only_hint = true,
            destructive_hint = false,
            idempotent_hint = true,
            open_world_hint = false
        )
    )]
    pub(crate) fn cfg(
        &self,
        Parameters(CfgParams { address, offset }): Parameters<CfgParams>,
    ) -> Result<String, ErrorData> {
        let offset = to_usize(offset.unwrap_or(0));
        self.with_analysis(Feature::Discover, |p, a, o| {
            let entry = self.function_entry(p, a, &address)?;
            render::cfg_mermaid(a, o, entry, offset)
                .ok_or_else(|| format!("no function at {entry:#x}"))
        })
    }
}

/// Reads a `Class+offset` target: a class's field.
///
/// The class is a class name as
/// [`borer_engine::analysis::classes::resolve_class`] reads it, a class
/// known by its vtable alone, or the address or name of a class's vtable
/// (`0x140123450`, `Net::Client::vftable`); the offset is hex or
/// decimal.
///
/// # Arguments
///
/// * `p` - The loaded program.
/// * `a` - Its analysis, with the classes and their vtables.
/// * `o` - Names in force.
/// * `text` - The target as the agent passed it.
///
/// # Returns
///
/// The qualified class and the offset, or `None` when the text is not of
/// that form or names no class.
pub(crate) fn class_field(
    p: &Program,
    a: &Analysis,
    o: &Overlay,
    text: &str,
) -> Option<(String, u64)> {
    let (head, off) = text.rsplit_once('+')?;
    let offset = parse_addr(off)?;
    let head = head.trim();
    let class = borer_engine::analysis::classes::resolve_class(a, o, head)
        .or_else(|| {
            a.classes
                .by_name
                .contains_key(head)
                .then(|| head.to_owned())
        })
        .or_else(|| {
            resolve(p, a, o, head)
                .ok()
                .and_then(|va| a.classes.vtables.get(&va).cloned())
        })?;
    Some((class, offset))
}

#[cfg(test)]
mod tests {
    /// Before `load_binary`, `functions` refuses the way every other tool
    /// does: invalid params, naming the call to make first.
    ///
    /// It read the analysis outside the tool-body boundary and answered the
    /// one refusal its siblings give as invalid params as an internal error
    /// instead, so a client telling the two codes apart saw a broken server
    /// where every other tool showed a missing step.
    ///
    /// # Panics
    ///
    /// When the refusal differs from a sibling's in code or message.
    #[test]
    fn functions_refuses_without_a_binary_like_every_other_tool() {
        let server = crate::BorerServer::default();
        let refused = server
            .functions(rmcp::handler::server::wrapper::Parameters(
                crate::params::FunctionsParams {
                    filter: None,
                    sort: None,
                    offset: None,
                    limit: None,
                    count_only: None,
                },
            ))
            .expect_err("nothing is loaded");
        let sibling = server
            .function(rmcp::handler::server::wrapper::Parameters(
                crate::params::FunctionDetailParams {
                    address: "0x1000".to_owned(),
                    offset: None,
                },
            ))
            .expect_err("nothing is loaded");
        assert_eq!(refused.code, rmcp::model::ErrorCode::INVALID_PARAMS);
        assert_eq!(refused.code, sibling.code);
        assert_eq!(refused.message, sibling.message);
        assert_eq!(refused.message, crate::state::NO_BINARY);
    }

    /// `xrefs` reads a target that is neither an address nor a name as
    /// `Class+offset`.
    ///
    /// It lists the functions using that field through a pointer typed as
    /// the class, with the value stored and the instruction; a class
    /// nothing belongs to is refused, saying which forms the target may
    /// take.
    ///
    /// # Panics
    ///
    /// When the field's writer is missing, or the refusal does not name
    /// the field form.
    #[test]
    fn xrefs_reads_a_class_and_an_offset_as_a_field() {
        use crate::params::XrefsParams;
        use borer_engine::program::{Arch, Program, Section};
        use rmcp::handler::server::wrapper::Parameters;
        let mut code = vec![0xc3; 0x100];
        // ASM: mov dword [rcx+0x24], 5; ret
        code[..8].copy_from_slice(&[0xc7, 0x41, 0x24, 0x05, 0x00, 0x00, 0x00, 0xc3]);
        let text = Section::mapped(".text", 0x1000, 0, 0x100, false, true);
        let program = Program::raw(code, Arch::X86_64, 0, Some(0x1000), vec![text]);
        let mut overlay = borer_engine::analysis::Overlay::default();
        overlay.names.insert(0x1000, "Foo::Set".to_owned());
        let server = crate::BorerServer {
            program: std::sync::Arc::new(std::sync::RwLock::new(Some(std::sync::Arc::new(
                program,
            )))),
            pdb_applied: std::sync::Arc::new(std::sync::RwLock::new(true)),
            overlay: std::sync::Arc::new(std::sync::RwLock::new(overlay)),
            ..crate::BorerServer::default()
        };
        let xrefs = |address: &str| {
            server.xrefs(Parameters(XrefsParams {
                address: address.to_owned(),
                offset: None,
                limit: None,
                count_only: None,
            }))
        };
        let field = xrefs("Foo+0x24").expect("a field");
        assert!(
            field
                .starts_with("# Foo+0x24: 1 functions use it through a pointer typed as the class"),
            "{field}"
        );
        assert!(
            field.contains(
                "
0x1000	Foo::Set	a1	w	0x5	0x1000
"
            ),
            "{field}"
        );
        let refused = xrefs("Nope+0x24").expect_err("no such class");
        assert!(
            refused
                .message
                .ends_with("; nor is it Class+offset, a field of a class with methods or a vtable"),
            "{}",
            refused.message
        );
    }
}
