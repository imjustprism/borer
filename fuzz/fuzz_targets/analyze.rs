//! Loads arbitrary bytes, lists the code at its entry, analyzes what loads,
//! decompiles its first functions, reads each text as a view and proposes a
//! struct through its first argument, lists the types and opens the first
//! page of them, for a .NET assembly lists its first IL methods and its
//! obfuscator markers, and reads every chart series table, a hostile spec
//! among them: the path every agent request takes after a load. The first
//! functions' call graphs and call tree levels are walked both ways too, and
//! the callers of the first imports, which have no body.

#![no_main]

use borer_engine::analysis::decompile::decompile;
use borer_engine::analysis::decompile::view::view_of;
use borer_engine::analysis::render::{
    Bytes, Level, Walk, call_children, callgraph, disasm_function_with, disasm_view, propose,
};
use borer_engine::analysis::stats::stats_tsv;
use borer_engine::analysis::utypes::{type_detail, type_rows};
use borer_engine::analysis::{Analysis, Overlay};
use borer_engine::clr::managed::{self, Managed};
use borer_engine::clr::markers::markers_tsv;
use borer_engine::disasm::disassemble_program;
use borer_engine::program::{Program, SymbolKind};
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
        }
        for level in [Level::Callees, Level::CalleesAndVirtuals, Level::Callers] {
            _ = call_children(&program, &analysis, &overlay, f.entry, level);
        }
        if let Some(text) = decompile(&program, &analysis, &overlay, f.entry) {
            _ = view_of(&program, &analysis, &overlay, f.entry, &text);
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
    for m in Managed::of(&program, &analysis)
        .methods
        .iter()
        .take(DECOMPILED)
    {
        _ = managed::listing(&program, m.token, usize::MAX);
        _ = managed::detail(&program, &analysis, m.token, 0);
    }
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
});
