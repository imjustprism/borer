//! Parses arbitrary text as a find query and runs it over a small program
//! built from the rest of the input, with symbols (one mangled each way), a
//! user name and a comment from the text: the path a find box takes on
//! every keystroke.

#![no_main]

use borer_engine::analysis::find::{Query, everywhere};
use borer_engine::analysis::{Analysis, Overlay};
use borer_engine::num::from_usize;
use borer_engine::program::{Arch, Program, Section, Symbol, SymbolKind};
use libfuzzer_sys::fuzz_target;

/// Where the program's one section maps and its entry.
const BASE: u64 = 0x1000;
/// Most hits a find lists per input.
const LISTED: usize = 64;

fuzz_target!(|data: &[u8]| {
    let split = data.iter().position(|&b| b == 0).unwrap_or(data.len());
    let (text, bytes) = data.split_at(split);
    let text = String::from_utf8_lossy(text);
    let bytes = bytes.to_vec();
    let size = from_usize(bytes.len());
    let section = Section::mapped(".text", BASE, 0, size, false, true);
    let mut program = Program::raw(bytes, Arch::X86_64, 0, Some(BASE), vec![section]);
    let symbol = |name: String, kind: SymbolKind| Symbol {
        name,
        addr: BASE,
        kind,
    };
    program.symbols = vec![
        symbol(format!("KERNEL32.dll!{text}"), SymbolKind::Import),
        symbol(
            format!("_ZN4find{}{text}Ev", text.len()),
            SymbolKind::Export,
        ),
        symbol(format!("?{text}@@YAXXZ"), SymbolKind::Local),
    ];
    let analysis = Analysis::compute(&program);
    let mut overlay = Overlay::default();
    overlay.names.insert(BASE + 1, text.to_string());
    overlay.comments.insert(BASE, text.to_string());
    let query = Query::parse(&text);
    let found = everywhere(&program, &analysis, &overlay, &query, LISTED);
    assert!(found.hits.len() <= LISTED);
    _ = found.spell();
});
