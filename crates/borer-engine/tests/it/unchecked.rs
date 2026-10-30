//! A function the checker cannot cover is not the first read and gets no
//! solve hint.

#![expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]

use borer_engine::analysis::render::{next_steps, triage_tsv};
use borer_engine::analysis::{Analysis, Overlay};
use borer_engine::program::{Arch, Symbol, SymbolKind};

use crate::raw::image;

const BASE: u64 = 0x401000;
/// The smaller caller, past the entry's jumps.
const SMALL: u64 = 0x4014c4;
/// The `ret` thunk named `WriteProcessMemory`.
const THUNK: u64 = 0x4014ca;

/// A mostly unchecked caller is not the first function to read.
///
/// The entry compares `ecx` with `0x1337abcd`, calls the smaller function,
/// calls the import, then jumps to the next instruction 600 times. Both
/// callers score the same. The long one sorts after the one the checker
/// can cover, and it gets no solve step.
#[test]
fn a_mostly_unchecked_function_is_not_read_first_and_gets_no_solve_hint() {
    let mut code = vec![
        0x81, 0xf9, 0xcd, 0xab, 0x37, 0x13, // ASM: cmp ecx, 0x1337abcd
        0x0f, 0x94, 0xc0, // ASM: sete al
        0xe8, 0xb6, 0x04, 0x00, 0x00, // ASM: call 0x4014c4
        0xe8, 0xb7, 0x04, 0x00, 0x00, // ASM: call 0x4014ca
    ];
    for _ in 0..600 {
        code.extend_from_slice(&[0xeb, 0x00]); // ASM: jmp next
    }
    code.extend_from_slice(&[
        0xc3, // ASM: ret
        0xe8, 0x01, 0x00, 0x00, 0x00, // ASM: call 0x4014ca
        0xc3, // ASM: ret
        0xc3, // ASM: ret
    ]);
    let mut p = image(Arch::X86_64, &code, &[]);
    p.symbols.push(Symbol {
        name: "KERNEL32.dll!WriteProcessMemory".to_owned(),
        addr: THUNK,
        kind: SymbolKind::Import,
    });
    let a = Analysis::compute(&p);
    let huge = a.function(BASE).expect("the entry is a function");
    assert!(huge.blocks.len() > 512, "{}", huge.blocks.len());
    let out = triage_tsv(&p, &a, &Overlay::default());
    let first = out
        .lines()
        .skip_while(|l| *l != "# read first")
        .nth(1)
        .expect("a reading list");
    assert!(first.starts_with(&format!("{SMALL:#x}")), "{first}\n{out}");
    let steps = next_steps(&p, &a, &Overlay::default(), BASE);
    assert!(steps.iter().all(|s| !s.contains("solve")), "{steps:?}");
}
