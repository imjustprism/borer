//! A function the checker cannot cover is not the first read and gets no
//! solve hint, and a local a call nothing models was handed is unchecked,
//! not a disagreement, when it is read back unset.
//!
//! A text every run of which stops at a vector store is unchecked too, not
//! agreeing, while a difference beside float code the check reads is found.

#![expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]

use borer_engine::analysis::decompile::decompile_named;
use borer_engine::analysis::render::{
    Verdict, blame_tsv, check_generated_iso, next_steps, triage_tsv,
};
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

/// Blame answers a difference in an integer result that stands beside
/// float code, and `unchecked` where the code beside it is a vector store
/// the check does not compute.
///
/// `mov eax,ecx; mov ecx,-5; cdq; idiv ecx; ret` returns a quotient the
/// text states at 64 bits where the machine cleared the upper half. After
/// `movsd xmm0,[rdx]; addsd xmm0,xmm0; movsd [rdx],xmm0` the check runs the
/// float lines and reports that difference. After `movdqu xmm0,[rdx]; paddd
/// xmm0,xmm0; movdqu [rdx],xmm0` every run stops at the vector store, so
/// the quotient is never compared: the answer is `unchecked` with that
/// reason and the count, not `agrees`.
///
/// The difference is a defect of the decompiler this test borrows, not
/// one it is about: the text declares `uint64_t f(int32_t a1)` and returns
/// `a1 / -5`, an `int` that C sign-extends to the return type, where the
/// `idiv` left the quotient in `eax` and `rax` zero above it. When that is
/// fixed the first assertion fails, since nothing differs any more: give
/// the test another text whose integer result differs, do not drop it.
#[test]
fn blame_reads_an_integer_result_beside_float_code() {
    const QUOTIENT: [u8; 11] = [
        0x89, 0xc8, // ASM: mov eax,ecx
        0xb9, 0xfb, 0xff, 0xff, 0xff, // ASM: mov ecx,0xfffffffb
        0x99, // ASM: cdq
        0xf7, 0xf9, // ASM: idiv ecx
        0xc3, // ASM: ret
    ];
    let float: [u8; 12] = [
        0xf2, 0x0f, 0x10, 0x02, // ASM: movsd xmm0,[rdx]
        0xf2, 0x0f, 0x58, 0xc0, // ASM: addsd xmm0,xmm0
        0xf2, 0x0f, 0x11, 0x02, // ASM: movsd [rdx],xmm0
    ];
    let vector: [u8; 12] = [
        0xf3, 0x0f, 0x6f, 0x02, // ASM: movdqu xmm0,[rdx]
        0x66, 0x0f, 0xfe, 0xc0, // ASM: paddd xmm0,xmm0
        0xf3, 0x0f, 0x7f, 0x02, // ASM: movdqu [rdx],xmm0
    ];
    let blamed = |beside: &[u8]| {
        let p = image(Arch::X86_64, &[beside, &QUOTIENT[..]].concat(), &[]);
        let a = Analysis::compute(&p);
        blame_tsv(&p, &a, &Overlay::default(), "0x401000,count=16").expect("blames")
    };
    let out = blamed(&float);
    assert!(
        out.contains("\ndiffers\t") && out.contains("the low 32 bits agree"),
        "{out}"
    );
    let out = blamed(&vector);
    assert!(
        out.contains("\nunchecked\t16\ta 128-bit value this does not compute\n"),
        "{out}"
    );
    assert!(
        !out.contains("\nagrees\t") && !out.contains("\ndiffers\t"),
        "{out}"
    );
}

/// Blame says how many of the inputs a text that agrees was checked on.
///
/// `L: test cl,1; jne L; xor eax,eax; ret` returns on an even argument and
/// spins on an odd one, where no result is compared. The answer counts the
/// inputs that agree apart from the ones left unchecked, with why, so the
/// ten that ran do not read as all sixteen.
#[test]
fn blame_counts_the_inputs_that_agree_apart_from_the_ones_left_unchecked() {
    let code = [
        0xf6, 0xc1, 0x01, // ASM: test cl,1
        0x75, 0xfb, // ASM: jne 0x401000
        0x31, 0xc0, // ASM: xor eax,eax
        0xc3, // ASM: ret
    ];
    let p = image(Arch::X86_64, &code, &[]);
    let a = Analysis::compute(&p);
    let out = blame_tsv(&p, &a, &Overlay::default(), "0x401000,count=16").expect("blames");
    let counted = "; the text agrees on 10 of 16 inputs, 6 left unchecked (6: both ran out of steps before returning, so no result was compared); ";
    assert!(out.contains(counted), "{out}");
}
