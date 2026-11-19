//! Parses arbitrary text as a find query and runs it over a small program
//! built from the rest of the input, with symbols (one mangled each way), a
//! user name and a comment from the text: the path a find box takes on
//! every keystroke. The text is then run as a search spec over the same
//! program, whose second half is a data section, which answers or
//! refuses; the bytes are also decoded as arm64, ARM32 (both instruction
//! sets) and RISC-V and each instruction's constants read.

#![no_main]

use borer_engine::analysis::find::{Query, everywhere};
use borer_engine::analysis::{Analysis, Overlay};
use borer_engine::num::from_usize;
use borer_engine::program::{Arch, Program, Section, Symbol, SymbolKind};
use borer_engine::isa::{a32, a64, rv};
use borer_engine::table::Window;
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
    constants(&bytes);
    let size = from_usize(bytes.len());
    let half = size / 2;
    let sections = vec![
        Section::mapped(".text", BASE, 0, half, false, true),
        Section::mapped(".data", BASE + half, half, size - half, true, false),
    ];
    let mut program = Program::raw(bytes, Arch::X86_64, 0, Some(BASE), sections);
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
    _ = borer_engine::search::form::search_tsv(
        &program,
        &analysis,
        &overlay,
        &text,
        Window::first(LISTED),
    );
});

/// Decodes every offset of `bytes` as arm64, ARM32 in both instruction
/// sets and RISC-V, reading each instruction's constants.
///
/// # Arguments
///
/// * `bytes` - The code.
fn constants(bytes: &[u8]) {
    let mut seen = 0usize;
    let mut count = |_: borer_engine::isa::Constant| seen += 1;
    for (k, word) in bytes.chunks_exact(4).enumerate() {
        let w = u32::from_le_bytes([word[0], word[1], word[2], word[3]]);
        a64::decode(w, BASE + from_usize(k * 4)).constants(&mut count);
    }
    for at in 0..bytes.len() {
        let rest = &bytes[at..];
        let va = BASE + from_usize(at);
        for mode in [a32::Mode::Arm, a32::Mode::Thumb] {
            if let Some(i) = a32::decode(rest, va, mode, &mut a32::ItState::default()) {
                i.constants(&mut count);
            }
        }
        for xlen in [rv::Xlen::X32, rv::Xlen::X64] {
            if let Some(i) = rv::decode(rest, va, xlen) {
                i.constants(xlen, &mut count);
            }
        }
    }
    assert!(seen <= bytes.len().saturating_mul(16));
}
