//! Loads arbitrary bytes, analyzes what loads and decompiles its first
//! functions, and for a .NET assembly lists its first IL methods and its
//! obfuscator markers: the path every agent request takes after a load.

#![no_main]

use borer_engine::analysis::decompile::decompile;
use borer_engine::analysis::{Analysis, Overlay};
use borer_engine::clr::managed::{self, Managed};
use borer_engine::clr::markers::markers_tsv;
use borer_engine::program::Program;
use libfuzzer_sys::fuzz_target;

/// Functions decompiled per input, so one input stays fast.
const DECOMPILED: usize = 4;

fuzz_target!(|data: &[u8]| {
    let Ok(program) = Program::from_bytes_with("fuzz".into(), data.to_vec(), false, None) else {
        return;
    };
    let analysis = Analysis::compute(&program);
    let overlay = Overlay::default();
    for f in analysis.functions.iter().take(DECOMPILED) {
        _ = decompile(&program, &analysis, &overlay, f.entry);
    }
    for m in Managed::of(&program, &analysis).methods.iter().take(DECOMPILED) {
        _ = managed::listing(&program, m.token, usize::MAX);
        _ = managed::detail(&program, &analysis, m.token);
    }
    _ = markers_tsv(&program, &analysis);
    _ = managed::methods_tsv(&program, &analysis, "");
});
