//! A function the checker cannot cover is not the first read and gets no
//! solve hint, and a local a call nothing models was handed is unchecked,
//! not a disagreement, when it is read back unset.

#![expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]

use borer_engine::analysis::decompile::decompile_named;
use borer_engine::analysis::render::{Verdict, check_generated_iso, next_steps, triage_tsv};
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

/// The address of `GetModuleFileNameA`, `strlen` and `memset` as imports in
/// this image's `.rdata`.
const IMPORTS: [(&str, u64); 3] = [
    ("KERNEL32.dll!GetModuleFileNameA", 0x402000),
    ("msvcrt.dll!strlen", 0x402008),
    ("msvcrt.dll!memset", 0x402010),
];

/// Builds `GetModuleFileNameA(NULL, &buf, 16); <tail>; ret`, where `buf` is
/// at `[rsp+0x30]`, and returns the text and the ISO verdict of each
/// generated input.
///
/// # Arguments
///
/// * `tail` - The code after the call, before the epilogue.
///
/// # Returns
///
/// The decompiled text and each input's verdict.
fn handed(tail: &[u8]) -> (String, Vec<Verdict>) {
    let mut code = vec![
        0x48, 0x83, 0xec, 0x48, // ASM: sub rsp,0x48
        0x31, 0xc9, // ASM: xor ecx,ecx
        0x48, 0x8d, 0x54, 0x24, 0x30, // ASM: lea rdx,[rsp+0x30]
        0x41, 0xb8, 0x10, 0x00, 0x00, 0x00, // ASM: mov r8d,0x10
        0xff, 0x15, 0xe9, 0x0f, 0x00, 0x00, // ASM: call [rip+0xfe9] (GetModuleFileNameA)
    ];
    code.extend_from_slice(tail);
    code.extend_from_slice(&[0x48, 0x83, 0xc4, 0x48, 0xc3]); // ASM: add rsp,0x48; ret
    let mut p = image(Arch::X86_64, &code, &[]);
    for (name, addr) in IMPORTS {
        p.symbols.push(Symbol {
            name: name.to_owned(),
            addr,
            kind: SymbolKind::Import,
        });
    }
    let (a, o) = (Analysis::compute(&p), Overlay::default());
    let text = decompile_named(&p, &a, &o, 0x401000).unwrap_or_default();
    let rows = check_generated_iso(&p, &a, &o, 0x401000, 4, 1, 20_000).unwrap_or_default();
    (text, rows.into_iter().map(|(_, v)| v).collect())
}

/// A local the text hands to a call nothing models is unchecked, not a
/// disagreement, when it is read back unset.
///
/// The real call would have written it; the emulator's stub wrote nothing.
/// Read directly or measured by `strlen`, every input is unchecked and
/// names the handing call.
///
/// # Panics
///
/// When an input differs, or its reason does not name the call.
#[test]
fn a_local_handed_to_a_call_nothing_models_is_unchecked() {
    let read = [0x48, 0x8b, 0x44, 0x24, 0x30]; // ASM: mov rax,[rsp+0x30]
    let measured = [
        0x48, 0x8d, 0x4c, 0x24, 0x30, // ASM: lea rcx,[rsp+0x30]
        0xff, 0x15, 0xe6, 0x0f, 0x00, 0x00, // ASM: call [rip+0xfe6] (strlen)
    ];
    for tail in [&read[..], &measured[..]] {
        let (text, verdicts) = handed(tail);
        assert!(!verdicts.is_empty(), "{text}");
        assert!(
            verdicts.iter().all(|v| matches!(
                v,
                Verdict::Unchecked(_, why) if why.contains("handed to GetModuleFileNameA")
            )),
            "{text}\n{verdicts:?}"
        );
    }
}

/// Only the handed local is excused: a byte that `memset`, which is
/// modeled, did not fill is still read unset, so the text differs there.
///
/// # Panics
///
/// When no input differs on the unwritten byte.
#[test]
fn a_local_a_modeled_call_fills_in_part_still_differs() {
    let (text, verdicts) = handed(&[
        0x48, 0x8d, 0x4c, 0x24, 0x20, // ASM: lea rcx,[rsp+0x20]
        0xba, 0x41, 0x00, 0x00, 0x00, // ASM: mov edx,0x41
        0x41, 0xb8, 0x04, 0x00, 0x00, 0x00, // ASM: mov r8d,4
        0xff, 0x15, 0xe3, 0x0f, 0x00, 0x00, // ASM: call [rip+0xfe3] (memset)
        0x48, 0x8b, 0x44, 0x24, 0x20, // ASM: mov rax,[rsp+0x20]
    ]);
    assert!(!verdicts.is_empty(), "{text}");
    assert!(
        verdicts.iter().all(|v| matches!(
            v,
            Verdict::Differs(_, why) if why.contains("is read before any line writes it")
        )),
        "{text}\n{verdicts:?}"
    );
}
