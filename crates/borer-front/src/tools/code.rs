//! The tools that read code: function summaries and listings,
//! cross-references, the call graph, the CFG, disassembly and decompilation.

use borer_engine::analysis::{Analysis, Overlay, decompile, parse_addr, render, resolve};
use borer_engine::program::{Feature, Program};

use super::params::{
    CallgraphParams, CfgParams, DecompileParams, DisassembleFunctionParams, FunctionDetailParams,
    FunctionParams, FunctionsParams, Page, ReachesParams, XrefsParams, count_param, to_usize,
};
use super::{Failure, Held, HeldExt};

/// Returns the one-call triage of a function.
///
/// # Arguments
///
/// * `h` - What the front end holds.
/// * `p` - The tool's parameters.
///
/// # Errors
///
/// When no binary is loaded or the address is not inside a discovered function.
pub fn function_summary(h: &dyn Held, p: &FunctionParams) -> Result<String, Failure> {
    h.run(Box::new(|prog| {
        let a = h.ensure_analysis()?;
        let entry = h.function_entry(prog, &a, &p.address)?;
        render::function_summary(prog, &a, &h.overlay(), entry)
            .ok_or_else(|| format!("no function at {entry:#x}"))
    }))
}

/// Lists the string literals a function references.
///
/// # Arguments
///
/// * `h` - What the front end holds.
/// * `p` - The tool's parameters.
///
/// # Errors
///
/// When no binary is loaded or the address is not inside a discovered function.
pub fn function_strings(h: &dyn Held, p: &FunctionParams) -> Result<String, Failure> {
    if let Some(answer) = h.il_answer(&p.address, borer_engine::clr::managed::strings_tsv) {
        return answer;
    }
    h.with_analysis(Feature::Discover, |prog, a, o| {
        let entry = h.function_entry(prog, a, &p.address)?;
        render::function_strings_tsv(prog, a, o, entry)
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
/// * `h` - What the front end holds.
/// * `p` - The tool's parameters.
///
/// # Errors
///
/// When no binary is loaded or the analysis is unavailable.
pub fn functions(h: &dyn Held, p: &FunctionsParams) -> Result<String, Failure> {
    let page = Page::new(p.offset, p.limit, p.count_only, 50, 300)?;
    let order = p.sort.unwrap_or_default().into();
    h.with_analysis(Feature::Discover, |_, a, o| {
        let rows =
            render::function_rows(a, o, p.filter.as_deref(), order, page.offset, page.limit.n);
        Ok(if page.count_only {
            rows.counted()
        } else {
            rows.spell()
        })
    })
    .map(|text| page.limit.noted(text))
}

/// Returns one function's detail and one page of its basic-block table.
///
/// # Arguments
///
/// * `h` - What the front end holds.
/// * `p` - The tool's parameters.
///
/// # Errors
///
/// When no binary is loaded or the address is not inside a discovered function.
pub fn function(h: &dyn Held, p: &FunctionDetailParams) -> Result<String, Failure> {
    let offset = to_usize(p.offset.unwrap_or(0));
    if let Some(answer) = h.il_answer(&p.address, |prog, a, token| {
        borer_engine::clr::managed::detail(prog, a, token, offset)
    }) {
        return answer;
    }
    h.with_analysis(Feature::Discover, |prog, a, o| {
        let entry = h.function_entry(prog, a, &p.address)?;
        render::function_detail(a, o, entry, offset)
            .ok_or_else(|| format!("no function at {entry:#x}"))
    })
}

/// Lists cross-references to an address or name, or the functions using a
/// class's field.
///
/// A target that is neither an address nor a name is read as
/// `Class+offset` ([`class_field`]): the readers and writers of that field
/// through pointers typed as the class
/// ([`borer_engine::analysis::classes::typed_field_uses`]), one row per
/// function: a byte search by offset finds every object's field at that
/// offset, and a filter on function names misses the unnamed writers.
///
/// # Arguments
///
/// * `h` - What the front end holds.
/// * `p` - The tool's parameters.
///
/// # Errors
///
/// When no binary is loaded or the target resolves to neither an address
/// nor a class field.
pub fn xrefs(h: &dyn Held, p: &XrefsParams) -> Result<String, Failure> {
    let page = Page::new(
        p.offset,
        p.limit,
        p.count_only,
        render::XREF_ROWS_DEFAULT,
        render::XREF_ROWS_MAX,
    )?;
    let address = &p.address;
    if let Some(answer) = h.managed_answer(address, |prog, a, targets| {
        borer_engine::clr::managed::xrefs_tsv(
            prog,
            a,
            targets,
            page.offset,
            page.limit.n,
            page.count_only,
        )
    }) {
        return answer.map(|text| page.limit.noted(text));
    }
    h.with_analysis(Feature::Discover, |prog, a, o| {
        let va = match h.addr(prog, address) {
            Ok(va) => va,
            Err(unknown) => return field_xrefs(prog, (a, o), address, &unknown, page),
        };
        Ok(render::xrefs_tsv(
            prog,
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

/// Lists the functions using a class's field, for an `xrefs` target that
/// names no address.
///
/// # Arguments
///
/// * `p` - The program held.
/// * `(a, o)` - Its analysis and the names in force.
/// * `target` - The target as written, `Class+offset`.
/// * `unknown` - Why it named no address, for the refusal.
/// * `page` - The page asked.
///
/// # Errors
///
/// When the target is not a class's field, or the program does not
/// decompile.
fn field_xrefs(
    p: &Program,
    (a, o): (&Analysis, &Overlay),
    target: &str,
    unknown: &str,
    page: Page,
) -> Result<String, String> {
    let (class, offset) = class_field(p, a, o, target).ok_or_else(|| {
        format!("{unknown}; nor is it Class+offset, a field of a class with methods or a vtable")
    })?;
    if let Some(why) = p.refuses(Feature::Decompile) {
        return Err(format!(
            "{class}+{offset:#x} is a field, read from decompiled methods: {why}"
        ));
    }
    let uses = borer_engine::analysis::classes::typed_field_uses(p, a, o, &class, offset)
        .ok_or_else(|| format!("no class {class}"))?;
    Ok(borer_engine::analysis::classes::typed_field_uses_tsv(
        &uses,
        a,
        o,
        offset,
        page.offset,
        page.limit.n,
        page.count_only,
    ))
}

/// Reads a `Class+offset` target: a class's field.
///
/// The class is a class name as
/// [`borer_engine::analysis::classes::resolve_class`] reads it, a class
/// known by its vtable alone, or the address or name of a class's vtable
/// (`0x140123450`, `Net::Client::vftable`); the offset is hex or decimal.
///
/// # Arguments
///
/// * `p` - The program held.
/// * `a` - Its analysis, with the classes and their vtables.
/// * `o` - Names in force.
/// * `text` - The target as the caller passed it.
///
/// # Returns
///
/// The qualified class and the offset, or `None` when the text is not of
/// that form or names no class.
#[must_use]
pub fn class_field(p: &Program, a: &Analysis, o: &Overlay, text: &str) -> Option<(String, u64)> {
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

/// Renders the call graph from a function as mermaid.
///
/// Walking callers from an import or a data symbol answers who references
/// it; it has no body to walk callees from.
///
/// # Arguments
///
/// * `h` - What the front end holds.
/// * `p` - The tool's parameters.
///
/// # Errors
///
/// When no binary is loaded or the address is not inside a discovered function.
pub fn callgraph(h: &dyn Held, p: &CallgraphParams) -> Result<String, Failure> {
    let max = count_param(p.max_nodes, 30, 100, "max_nodes")?;
    let callers = p.callers.unwrap_or(false);
    h.with_analysis(Feature::Discover, |prog, a, o| {
        let root = match h.function_entry(prog, a, &p.address) {
            Ok(root) => root,
            Err(e) => {
                let va = h.addr(prog, &p.address)?;
                if callers && (a.symbol_at(prog, va).is_some() || a.xrefs.contains_key(&va)) {
                    va
                } else {
                    return Err(e);
                }
            }
        };
        Ok(render::callgraph_mermaid(prog, a, o, root, max.n, callers))
    })
    .map(|text| max.noted_with("%%", text))
}

/// Answers whether one function reaches another through calls.
///
/// The goal may be an import with no thunk, called through its slot: it
/// was refused for want of a function containing the slot.
///
/// # Arguments
///
/// * `h` - What the front end holds.
/// * `p` - The tool's parameters.
///
/// # Errors
///
/// When no binary is loaded, `from` is not inside a discovered function,
/// or `to` is neither inside one nor an import.
pub fn reaches(h: &dyn Held, p: &ReachesParams) -> Result<String, Failure> {
    let deep = count_param(p.depth, 24, 64, "depth")?;
    h.with_analysis(Feature::Discover, |prog, a, o| {
        let start = h.function_entry(prog, a, &p.from)?;
        let goal = match h.function_entry(prog, a, &p.to) {
            Ok(goal) => goal,
            Err(e) => {
                let va = h.addr(prog, &p.to)?;
                if a.symbol_at(prog, va)
                    .is_some_and(|s| s.kind == borer_engine::program::SymbolKind::Import)
                {
                    va
                } else {
                    return Err(e);
                }
            }
        };
        Ok(render::call_path(prog, a, o, start, goal, deep.n))
    })
    .map(|text| deep.noted(text))
}

/// Renders a function's control-flow graph as mermaid.
///
/// # Arguments
///
/// * `h` - What the front end holds.
/// * `p` - The tool's parameters.
///
/// # Errors
///
/// When no binary is loaded or the address is not inside a discovered function.
pub fn cfg(h: &dyn Held, p: &CfgParams) -> Result<String, Failure> {
    let offset = to_usize(p.offset.unwrap_or(0));
    h.with_analysis(Feature::Discover, |prog, a, o| {
        let entry = h.function_entry(prog, a, &p.address)?;
        render::cfg_mermaid(prog, a, o, entry, offset)
            .ok_or_else(|| format!("no function at {entry:#x}"))
    })
}

/// Disassembles a whole function block by block, or a `.NET` method's CIL
/// ([`borer_engine::answer::disasm_function`]).
///
/// # Arguments
///
/// * `h` - What the front end holds.
/// * `p` - The tool's parameters.
///
/// # Errors
///
/// When no binary is loaded or the address is not inside a discovered function.
pub fn disassemble_function(
    h: &dyn Held,
    p: &DisassembleFunctionParams,
) -> Result<String, Failure> {
    use borer_engine::answer::{FUNCTION_INSTRS_DEFAULT, disasm_function};
    let max = count_param(p.max_instrs, FUNCTION_INSTRS_DEFAULT, 2000, "max_instrs")?;
    h.run(Box::new(|prog| {
        let a = h.analysis_or_empty();
        disasm_function(
            prog,
            &a,
            &h.overlay(),
            &p.address,
            max.n,
            p.bytes.unwrap_or(false),
        )
    }))
    .map(|text| max.noted(text))
}

/// Returns the pseudo-C of one function.
///
/// `detail` is an enum: anything but `skeleton` used to fall through to the
/// whole function, so a caller who misspelled it read a complete
/// decompilation believing it was the outline and was never told
/// otherwise.
///
/// The answer is the engine's ([`decompile::answer()`]), paged
/// ([`decompile::window`]). Its second line says what of it was checked
/// against the binary ([`decompile::checked_header`]). The index stores
/// another form of it ([`decompile::shown`]), made without the repair
/// search and under the empty overlay: none of the session's names,
/// comments, types, prototypes or fields, and no name tables. Its lines can
/// differ from these: each comment is a line of its own, so the lines after
/// one are numbered otherwise there; a function the check flags has no note
/// and no repaired rendering there; and what the session named or typed, or
/// a constant a name table spells, reads as the binary alone gives it.
///
/// # Arguments
///
/// * `h` - What the front end holds.
/// * `p` - The tool's parameters.
///
/// # Errors
///
/// When no binary is loaded, the address is not inside a discovered
/// function, or the decompiler produces nothing.
pub fn decompile(h: &dyn Held, p: &DecompileParams) -> Result<String, Failure> {
    if p.limit == Some(0) {
        return Err(Failure::asked(decompile::LIMIT_ZERO));
    }
    h.run(Box::new(|prog| {
        if let Some(why) = prog.refuses(Feature::Decompile) {
            return Err(why);
        }
        let (a, entry) = h.decompile_entry(prog, h.ensure_analysis()?, &p.address)?;
        let detail = p.detail.unwrap_or_default().into();
        let text = decompile::answer(prog, &a, &h.overlay(), entry, detail)
            .ok_or_else(|| format!("decompilation failed at {entry:#x}"))?;
        Ok(decompile::window(
            &text,
            p.filter.as_deref(),
            p.offset,
            p.limit,
        ))
    }))
}
