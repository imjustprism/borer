//! Loads arbitrary bytes, lists the code at its entry, analyzes what loads,
//! decompiles its first functions and reads each text as a view, and for a
//! .NET assembly lists its first IL methods and its obfuscator markers: the
//! path every agent request takes after a load.

#![no_main]

use borer_engine::analysis::decompile::decompile;
use borer_engine::analysis::decompile::view::view_of;
use borer_engine::analysis::render::{Bytes, disasm_function_with, disasm_view};
use borer_engine::analysis::{Analysis, Overlay};
use borer_engine::clr::managed::{self, Managed};
use borer_engine::clr::markers::markers_tsv;
use borer_engine::disasm::disassemble_program;
use borer_engine::program::Program;
use libfuzzer_sys::fuzz_target;

/// Functions decompiled per input, so one input stays fast.
const DECOMPILED: usize = 4;
/// Instructions listed at the entry, and bytes read for them.
const LISTED: usize = 64;

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
        if let Some(text) = decompile(&program, &analysis, &overlay, f.entry) {
            _ = view_of(&program, &analysis, &overlay, f.entry, &text);
        }
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
});
