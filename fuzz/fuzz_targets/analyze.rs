//! Loads arbitrary bytes, lists the code at its entry, analyzes what loads,
//! builds the control-flow graph of its first functions, decompiles them
//! and reads each text as a view and its next steps, reads the template
//! signatures each references (every string the program references is
//! parsed for them on the first ask), proposes a struct
//! through its first argument, lists the types and opens the first page of
//! them, lists what the assertions name, pages the linear listing both ways
//! from the entry, an address the input names and the image's end, draws a
//! band of a cell count the input names, spells the typed triage, for a .NET
//! assembly lists its first IL methods and its obfuscator markers, and reads
//! every chart series table, a hostile spec among them: the path every agent
//! request takes after a load. The first functions' call graphs, typed
//! and mermaid, and call tree levels are walked both ways too, with their
//! reference graphs, and the callers of the first imports, which have no
//! body.

#![no_main]

use borer_engine::analysis::classes::{class_layout, render_layout};
use borer_engine::analysis::decompile::view::view_of;
use borer_engine::analysis::decompile::{decompile, unit_of};
use borer_engine::analysis::modsdk::{self, header::class_headers};
use borer_engine::analysis::render::{
    Bytes, Dir, Level, Walk, asserted_fields_tsv, band, call_children, call_graph, callgraph, cfg,
    disasm_function_with, disasm_view, linear, next_steps, propose, source_tree_tsv,
    source_vocabulary_tsv, triage, xref_graph,
};
use borer_engine::analysis::split::{sources, split_map};
use borer_engine::analysis::stats::stats_tsv;
use borer_engine::analysis::utypes::{type_detail, type_rows};
use borer_engine::analysis::vtables::family_of;
use borer_engine::analysis::{Analysis, Overlay, referenced_signatures};
use borer_engine::clr::managed::{self, Managed};
use borer_engine::clr::markers::markers_tsv;
use borer_engine::disasm::disassemble_program;
use borer_engine::program::{Feature, Program, SymbolKind};
use borer_engine::table::Window;
use libfuzzer_sys::fuzz_target;

/// Functions decompiled per input, so one input stays fast.
const DECOMPILED: usize = 4;
/// Instructions listed at the entry, and bytes read for them.
const LISTED: usize = 64;
/// Types listed and opened per input.
const TYPES: usize = 200;

fuzz_target!(|data: &[u8]| {
    let Ok(program) = Program::from_bytes_with("fuzz".into(), data.to_vec(), false, None) else {
        return;
    };
    if let (Some(isa), Some(entry)) = (program.arch.isa(), program.entry)
        && let Some(code) = program.read_va_upto(entry, LISTED * 4)
    {
        _ = disassemble_program(&program, code, entry, isa, LISTED);
    }
    let analysis = Analysis::compute(&program);
    let overlay = Overlay::default();
    let sdk = modsdk::build(&program, &analysis, &overlay);
    let mut cited = sources(&program, &analysis);
    cited.file_by_class(&program, &analysis, &overlay, &sdk);
    for f in analysis.functions.iter().take(DECOMPILED) {
        for bytes in [Bytes::Hidden, Bytes::Shown] {
            let text = disasm_function_with(&program, &analysis, &overlay, f.entry, LISTED, bytes);
            if let Some(v) = disasm_view(&program, &analysis, &overlay, f.entry, LISTED, bytes) {
                assert_eq!(Some(v.spell()), text);
                for i in 0..v.lines() {
                    if let Some(line) = v.line(i) {
                        for (span, _, _) in v.tokens(i) {
                            _ = &line[span];
                        }
                    }
                }
            }
        }
        for walk in [Walk::Callees, Walk::Callers] {
            _ = callgraph(&program, &analysis, &overlay, f.entry, LISTED, walk);
            let g = call_graph(&program, &analysis, &overlay, f.entry, walk, 4, LISTED);
            assert_eq!(g.layout().at.len(), g.nodes.len());
        }
        let g = xref_graph(&program, &analysis, &overlay, f.entry, 4, LISTED);
        assert_eq!(g.layout().routes.len(), g.edges.len());
        for level in [Level::Callees, Level::CalleesAndVirtuals, Level::Callers] {
            _ = call_children(&program, &analysis, &overlay, f.entry, level);
        }
        _ = next_steps(&program, &analysis, &overlay, f.entry);
        _ = referenced_signatures(&program, &analysis, f.entry);
        if let Ok(g) = cfg(&program, &analysis, &overlay, f.entry) {
            _ = g.listing.lines();
        }
        if let Some(text) = decompile(&program, &analysis, &overlay, f.entry) {
            _ = view_of(&program, &analysis, &overlay, f.entry, &text);
            _ = unit_of(&text);
            _ = cited.filed(f.entry, &text);
        }
        _ = propose(&program, &analysis, &overlay, &format!("{:#x}", f.entry));
    }
    for row in type_rows(&program, &analysis, &overlay, None, 0, TYPES).rows {
        _ = type_detail(
            &program, &analysis, &overlay, &row.name, row.source, row.kind,
        );
    }
    for s in program
        .symbols
        .iter()
        .filter(|s| s.kind == SymbolKind::Import)
        .take(DECOMPILED)
    {
        _ = callgraph(&program, &analysis, &overlay, s.addr, LISTED, Walk::Callers);
        _ = call_children(&program, &analysis, &overlay, s.addr, Level::Callers);
    }
    let word = |at: usize, len: usize| {
        data.iter()
            .skip(at)
            .take(len)
            .rev()
            .fold(0u64, |v, &b| (v << 8) | u64::from(b))
    };
    let chosen = [program.entry.unwrap_or(0), word(0, 8), u64::MAX];
    for (at, dir) in chosen
        .into_iter()
        .flat_map(|at| [(at, Dir::Next), (at, Dir::Prev)])
    {
        if let Some(page) = linear(&program, &analysis, &overlay, at, dir, LISTED) {
            assert!(page.rows.len() <= LISTED);
            assert!(page.next.is_none_or(|next| next > page.first));
            assert!(page.prev.is_none_or(|prev| prev < page.first));
        }
    }
    let cells = usize::try_from(word(8, 2)).unwrap_or(LISTED);
    assert!(band(&program, &analysis, &overlay, cells).len() <= cells.max(1));
    if program.refuses(Feature::Decompile).is_none() {
        _ = triage(&program, &analysis, &overlay).spell();
    }
    for m in Managed::of(&program, &analysis)
        .methods
        .iter()
        .take(DECOMPILED)
    {
        _ = managed::listing(&program, m.token, usize::MAX);
        _ = managed::detail(&program, &analysis, m.token, 0);
    }
    _ = asserted_fields_tsv(&program, &analysis, &overlay, "");
    _ = source_tree_tsv(&program, &analysis, ".");
    _ = source_vocabulary_tsv(&program, &analysis, &overlay, ".");
    for class in analysis.classes.by_name.keys().take(DECOMPILED) {
        _ = family_of(&analysis, &overlay, class);
        if let Some(layout) = class_layout(&program, &analysis, &overlay, class) {
            _ = render_layout(&layout, &analysis, &overlay);
        }
    }
    let split = class_headers(&sdk);
    let named: Vec<(&str, &str)> = split
        .classes
        .iter()
        .map(|(class, file, _)| (class.as_str(), file.as_str()))
        .collect();
    _ = split_map(&analysis, &overlay, &sdk, &named, &Default::default());
    _ = markers_tsv(&program, &analysis, "");
    _ = managed::methods_tsv(&program, &analysis, "");
    for spec in [
        "entropy",
        "strings,window=64",
        "sizes,bins=3",
        "sections,count",
        "entropy,window=18446744073709551615,filter=\u{202e},window=0",
        "sizes,bins=4294967296,filter=0x",
    ] {
        _ = stats_tsv(&program, &analysis, spec, Window::first(LISTED));
    }
    for uri in [
        "borer://find/a",
        "borer://find/0x401000",
        "borer://find/str:%00%E2%80%AE!limit=3",
        "borer://stats/strings,window=64!offset=1!limit=2",
        "borer://encoded!limit=4",
        "borer://indirect!limit=3",
        "borer://indirect/0x401000,form=vtable",
    ] {
        _ = borer_engine::answer::listing(&program, Some(&analysis), &overlay, uri);
    }
});
