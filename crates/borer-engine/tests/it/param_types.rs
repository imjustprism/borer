//! Parameter types read off the code: what a function's own accesses and
//! the calls it makes show its parameters to be.

#![expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]

use crate::decompiled;
use borer_engine::analysis::decompile::decompile;
use borer_engine::analysis::{Analysis, Overlay};
use borer_engine::program::{Program, Symbol, SymbolKind};
use decompiled::{program64, program64_with_data, replays_clean};

/// The caller of [`passes_to_strlen`] that hands its `rcx` to `g`:
/// `sub rsp,0x28; mov rax,rcx; mov rcx,rax; call g; add rsp,0x28; ret`.
const PASSES_A1: [u8; 20] = [
    0x48, 0x83, 0xec, 0x28, // ASM: sub rsp, 0x28
    0x48, 0x89, 0xc8, // ASM: mov rax, rcx
    0x48, 0x89, 0xc1, // ASM: mov rcx, rax
    0xe8, 0x11, 0x00, 0x00, 0x00, // ASM: call 0x140001020
    0x48, 0x83, 0xc4, 0x28, // ASM: add rsp, 0x28
    0xc3, // ASM: ret
];

/// Returns the image of a caller and a callee.
///
/// The caller `f` at `0x1_4000_1000` calls `g` at `0x1_4000_1020`, which
/// hands its `rcx` to `strlen`.
///
/// # Arguments
///
/// * `caller` - The bytes of `f`, at most `0x20`.
fn passes_to_strlen(caller: &[u8]) -> Program {
    let mut code = caller.to_vec();
    code.resize(0x20, 0xcc);
    code.extend_from_slice(&[
        0x48, 0x83, 0xec, 0x28, // ASM: sub rsp, 0x28
        0xff, 0x15, 0xd6, 0x0f, 0x00, 0x00, // ASM: call [rip+0xfd6]
        0x48, 0x83, 0xc4, 0x28, // ASM: add rsp, 0x28
        0xc3, // ASM: ret
    ]);
    let mut p = program64_with_data(&code, &[0u8; 8]);
    p.symbols = vec![Symbol {
        name: "msvcrt.dll!strlen".to_owned(),
        addr: 0x1_4000_2000,
        kind: SymbolKind::Import,
    }];
    p
}

/// A parameter a call clobbers is no pointer through what the call hands
/// back.
///
/// `mov eax, edx` copies the second parameter into `rax`, the call returns
/// its own value there, and `mov rax, [rax]` loads through that result:
/// the load says nothing of `a2`, which is not a `uint64_t *`.
#[test]
fn a_load_through_a_call_result_types_no_parameter() {
    let mut code = vec![
        0x48, 0x83, 0xec, 0x28, // ASM: sub rsp,0x28
        0x89, 0xd0, // ASM: mov eax,edx
        0xe8, 0x35, 0x00, 0x00, 0x00, // ASM: call 0x1_4000_1040
        0x48, 0x8b, 0x00, // ASM: mov rax,[rax]
        0x48, 0x83, 0xc4, 0x28, // ASM: add rsp,0x28
        0xc3, // ASM: ret
    ];
    code.resize(0x40, 0xcc);
    code.extend_from_slice(&[
        0x48, 0x89, 0xc8, // ASM: mov rax,rcx
        0xc3, // ASM: ret
    ]);
    let p = program64(&code);
    let a = Analysis::compute(&p);
    let text = decompile(&p, &a, &Overlay::default(), 0x1_4000_1000).unwrap_or_default();
    assert!(!text.contains("*a2"), "{text}");
    replays_clean(&p, &a, &[0x1_4000_1000]);
}

/// A parameter passed whole to a function of the image takes the pointer
/// type that function's own text gives the parameter it lands in.
///
/// `sub rsp,0x28; mov rax,rcx; mov rcx,rax; call g; add rsp,0x28; ret`
/// hands its `rcx` to `g`, which hands its own to `strlen`: `g` takes a
/// `char *`, and so does the caller's `a1`, where it read `uint64_t`.
#[test]
fn a_parameter_passed_to_a_typed_callee_takes_its_type() {
    let p = passes_to_strlen(&PASSES_A1);
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let callee = decompile(&p, &a, &o, 0x1_4000_1020).unwrap_or_default();
    assert!(callee.contains("(char *a1)"), "{callee}");
    let text = decompile(&p, &Analysis::compute(&p), &o, 0x1_4000_1000).unwrap_or_default();
    assert!(text.contains("(char *a1)"), "{text}");
    assert!(!text.contains("// callee "), "{text}");
    replays_clean(&p, &a, &[0x1_4000_1000]);
}

/// The unit declares a function of the image with the pointer type both
/// its own text and the caller's give the parameter passed to it, where
/// its ABI facts said only how wide it is.
///
/// The image of [`a_parameter_passed_to_a_typed_callee_takes_its_type`]:
/// `f(char *a1)` passes `a1` to `g`, whose own text reads `char *a1`, so
/// the declaration of `g` before `f` takes a `char *` and not a
/// `uint64_t`, and the call reads as C that compiles cleanly.
#[test]
fn a_callee_is_declared_with_the_type_both_texts_agree_on() {
    let p = passes_to_strlen(&PASSES_A1);
    let a = Analysis::compute(&p);
    let text = decompile(&p, &a, &Overlay::default(), 0x1_4000_1000).unwrap_or_default();
    assert!(text.contains("(char *a1)"), "{text}");
    let extern_g = text
        .lines()
        .find(|l| l.starts_with("extern ") && l.contains("sub_140001020("))
        .unwrap_or_default();
    assert!(extern_g.contains("sub_140001020(char *)"), "{text}");
}

/// A call passing a callee anything but a parameter of the type keeps the
/// callee's declaration at its ABI type.
///
/// `f` calls `g(a1)`, then `g(0x10)`: `a1` is a `char *` as `g`'s own
/// text reads its parameter, but a declaration `g(char *)` would refuse
/// the second call, so `g` stays declared as taking a `uint64_t`.
#[test]
fn a_callee_passed_an_integer_keeps_its_abi_declaration() {
    let p = passes_to_strlen(&[
        0x48, 0x83, 0xec, 0x28, // ASM: sub rsp, 0x28
        0x48, 0x89, 0xc8, // ASM: mov rax, rcx
        0x48, 0x89, 0xc1, // ASM: mov rcx, rax
        0xe8, 0x11, 0x00, 0x00, 0x00, // ASM: call 0x140001020
        0xb9, 0x10, 0x00, 0x00, 0x00, // ASM: mov ecx, 0x10
        0xe8, 0x07, 0x00, 0x00, 0x00, // ASM: call 0x140001020
        0x48, 0x83, 0xc4, 0x28, // ASM: add rsp, 0x28
        0xc3, // ASM: ret
    ]);
    let a = Analysis::compute(&p);
    let text = decompile(&p, &a, &Overlay::default(), 0x1_4000_1000).unwrap_or_default();
    assert!(text.contains("(char *a1)"), "{text}");
    assert!(text.contains("sub_140001020(16)"), "{text}");
    let extern_g = text
        .lines()
        .find(|l| l.starts_with("extern ") && l.contains("sub_140001020("))
        .unwrap_or_default();
    assert!(extern_g.contains("sub_140001020(uint64_t)"), "{text}");
}
