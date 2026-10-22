//! The `float` or `double` a 64-bit function hands back in `xmm0`.
//!
//! It is read off the exits that return normally (an error exit that
//! calls a handler and an exit that hands the argument back past scratch
//! work in `eax` beside them), or stated by the function's declaration
//! whatever its body seems to say: the type library's row for its name, or
//! its debug information. The bodies are the shapes of `msvcrt.dll`'s math.

#![expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]

use std::collections::BTreeMap;

use borer_engine::analysis::decompile::decompile;
use borer_engine::analysis::{Analysis, Overlay};
use borer_engine::dwarf::Subprogram;
use borer_engine::program::{Program, Symbol, SymbolKind};

use crate::decompiled::{program64, replays_clean};

/// The single a function leaves in `xmm0` on its exits that return
/// normally is its result, though another exit ends calling the error
/// handler that returns the float for it.
///
/// `ceilf` hands a NaN to its handler and returns what the handler
/// returns: `ucomiss xmm0,xmm0; jp E; addss xmm0,xmm0; ret; E: call H;
/// ret`, which nothing calls, returns a `float` from both exits, and so
/// does the handler `mulss xmm0,xmm0; ret` it calls in tail position.
#[test]
fn an_exit_calling_an_error_handler_keeps_the_float_result() {
    let mut code = vec![
        0x48, 0x83, 0xec, 0x28, // ASM: sub rsp,0x28
        0x0f, 0x2e, 0xc0, // ASM: ucomiss xmm0,xmm0
        0x7a, 0x09, // ASM: jp 0x140001012
        0xf3, 0x0f, 0x58, 0xc0, // ASM: addss xmm0,xmm0
        0x48, 0x83, 0xc4, 0x28, // ASM: add rsp,0x28
        0xc3, // ASM: ret
        0xe8, 0x29, 0x00, 0x00, 0x00, // ASM: call 0x140001040
        0x48, 0x83, 0xc4, 0x28, // ASM: add rsp,0x28
        0xc3, // ASM: ret
    ];
    code.resize(0x40, 0xcc);
    code.extend_from_slice(&[
        0xf3, 0x0f, 0x59, 0xc0, // ASM: mulss xmm0,xmm0
        0xc3, // ASM: ret
    ]);
    let p = program64(&code);
    let a = Analysis::compute(&p);
    let widths = [0x1_4000_1000, 0x1_4000_1040].map(|e| a.function(e).and_then(|f| f.ret_float));
    assert_eq!(widths, [Some(32), Some(32)]);
    let text = decompile(&p, &a, &Overlay::default(), 0x1_4000_1000).unwrap_or_default();
    assert!(text.contains("// signature: float "), "{text}");
    assert!(text.contains("return sub_140001040("), "{text}");
    assert!(!text.contains("return;"), "{text}");
    replays_clean(&p, &a, &[0x1_4000_1000, 0x1_4000_1040]);
}

/// `_copysignf` as `msvcrt.dll` has it: the two singles' bits are
/// compared in `eax`, and the first comes back as it was or negated.
const COPYSIGNF: [u8; 39] = [
    0xf3, 0x0f, 0x11, 0x44, 0x24, 0x08, // ASM: movss [rsp+8],xmm0
    0x8b, 0x4c, 0x24, 0x08, // ASM: mov ecx,[rsp+8]
    0xf3, 0x0f, 0x11, 0x4c, 0x24, 0x08, // ASM: movss [rsp+8],xmm1
    0x8b, 0x44, 0x24, 0x08, // ASM: mov eax,[rsp+8]
    0x33, 0xc1, // ASM: xor eax,ecx
    0x7d, 0x0e, // ASM: jge 0x140001026
    0x0f, 0xba, 0xf9, 0x1f, // ASM: btc ecx,0x1f
    0x89, 0x4c, 0x24, 0x08, // ASM: mov [rsp+8],ecx
    0xf3, 0x0f, 0x10, 0x44, 0x24, 0x08, // ASM: movss xmm0,[rsp+8]
    0xc3, // ASM: ret
];

/// The `xor eax, ecx` of [`COPYSIGNF`] is scratch, not the result.
///
/// The exit it reaches hands the argument back in `xmm0` untouched, the
/// other exit loads the negated single into `xmm0`, so the function
/// returns a `float`, never `eax`.
#[test]
fn a_scratch_eax_beside_the_float_argument_is_no_result() {
    let p = program64(&COPYSIGNF);
    let a = Analysis::compute(&p);
    let f = a.function(0x1_4000_1000).map(|f| f.ret_float);
    assert_eq!(f, Some(Some(32)));
    let text = decompile(&p, &a, &Overlay::default(), 0x1_4000_1000).unwrap_or_default();
    assert!(text.contains("// signature: float "), "{text}");
    assert!(text.contains("var1 = a1;"), "{text}");
    assert!(text.contains("return var1;"), "{text}");
    replays_clean(&p, &a, &[0x1_4000_1000]);
}

/// A write of `eax` nearest an exit is the result where `xmm0` holds no
/// float argument.
///
/// That is after the function wrote `xmm0` (`movss xmm0,[rcx]; comiss
/// xmm0,xmm1; jbe R; xor eax,eax; R: ret`), or in a function that never
/// reads `xmm0` before writing it (`mov eax,[rdx]; test eax,eax; je R;
/// movss xmm0,[rcx]; R: ret`).
#[test]
fn eax_written_where_xmm0_holds_no_argument_decides_against_a_float() {
    let written_first = [
        0xf3, 0x0f, 0x10, 0x01, // ASM: movss xmm0,[rcx]
        0x0f, 0x2f, 0xc1, // ASM: comiss xmm0,xmm1
        0x76, 0x03, // ASM: jbe 0x14000100c
        0x31, 0xc0, // ASM: xor eax,eax
        0xc3, // ASM: ret
        0xc3, // ASM: ret
    ];
    let no_argument = [
        0x8b, 0x02, // ASM: mov eax,[rdx]
        0x85, 0xc0, // ASM: test eax,eax
        0x74, 0x04, // ASM: je 0x14000100a
        0xf3, 0x0f, 0x10, 0x01, // ASM: movss xmm0,[rcx]
        0xc3, // ASM: ret
    ];
    for code in [&written_first[..], &no_argument[..]] {
        let a = Analysis::compute(&program64(code));
        let f = a.function(0x1_4000_1000).map(|f| f.ret_float);
        assert_eq!(f, Some(None), "{code:02x?}");
    }
}

/// An `atof` shape: the double comes from the record a callee returns a
/// pointer to, and a stack-cookie check sits between that load and the
/// `ret`, so no exit's nearest write shows the float.
///
/// `sub rsp,0x28; call P; movsd xmm0,[rax+0x10]; call C; add rsp,0x28;
/// ret`, with `P` = `lea rax,[rcx+8]; ret` and `C` = `cmp rcx,rdx; jne F;
/// ret; F: int3`.
///
/// # Arguments
///
/// * `name` - The export the entry is named, if any.
fn atof_shape(name: Option<&str>) -> Program {
    let mut code = vec![
        0x48, 0x83, 0xec, 0x28, // ASM: sub rsp,0x28
        0xe8, 0x37, 0x00, 0x00, 0x00, // ASM: call 0x140001040
        0xf2, 0x0f, 0x10, 0x40, 0x10, // ASM: movsd xmm0,[rax+0x10]
        0xe8, 0x4d, 0x00, 0x00, 0x00, // ASM: call 0x140001060
        0x48, 0x83, 0xc4, 0x28, // ASM: add rsp,0x28
        0xc3, // ASM: ret
    ];
    code.resize(0x40, 0xcc);
    code.extend_from_slice(&[
        0x48, 0x8d, 0x41, 0x08, // ASM: lea rax,[rcx+8]
        0xc3, // ASM: ret
    ]);
    code.resize(0x60, 0xcc);
    code.extend_from_slice(&[
        0x48, 0x3b, 0xca, // ASM: cmp rcx,rdx
        0x75, 0x01, // ASM: jne 0x140001066
        0xc3, // ASM: ret
        0xcc, // ASM: int3
    ]);
    let mut p = program64(&code);
    p.symbols = name
        .map(|n| Symbol {
            name: n.to_owned(),
            addr: 0x1_4000_1000,
            kind: SymbolKind::Export,
        })
        .into_iter()
        .collect();
    p
}

/// A function declared to return a `double` returns the double in `xmm0`.
///
/// The type library's `atof` returns it, not the pointer its last call
/// left in `rax`; a function the debug information declares so does too,
/// and the body alone proves nothing.
#[test]
fn a_declared_double_is_the_result_whatever_the_body_shows() {
    let p = atof_shape(Some("atof"));
    let a = Analysis::compute(&p);
    let f = a.function(0x1_4000_1000).map(|f| f.ret_float);
    assert_eq!(f, Some(Some(64)));
    let text = decompile(&p, &a, &Overlay::default(), 0x1_4000_1000).unwrap_or_default();
    assert!(text.contains("// signature: double atof("), "{text}");
    assert!(text.contains("(double*)"), "{text}");
    assert!(!text.contains("return sub_140001040("), "{text}");
    replays_clean(&p, &a, &[0x1_4000_1000]);
    let mut p = atof_shape(None);
    p.debug_functions.push(Subprogram {
        low_pc: 0x1_4000_1000,
        name: "parse".to_owned(),
        parameters: Vec::new(),
        return_type: Some("double".to_owned()),
        locals: BTreeMap::new(),
    });
    let f = Analysis::compute(&p)
        .function(0x1_4000_1000)
        .map(|f| f.ret_float);
    assert_eq!(f, Some(Some(64)));
    let f = Analysis::compute(&atof_shape(None))
        .function(0x1_4000_1000)
        .map(|f| f.ret_float);
    assert_eq!(f, Some(None));
}

/// A declaration that states an integer result outweighs a body that
/// looks like a float's: [`COPYSIGNF`] exported as `_isnanf`, which the
/// type library declares to return an `int`, hands back no float.
#[test]
fn a_declared_integer_is_no_float_result() {
    let mut p = program64(&COPYSIGNF);
    p.symbols = vec![Symbol {
        name: "_isnanf".to_owned(),
        addr: 0x1_4000_1000,
        kind: SymbolKind::Export,
    }];
    let f = Analysis::compute(&p)
        .function(0x1_4000_1000)
        .map(|f| f.ret_float);
    assert_eq!(f, Some(None));
}

/// `tanf`'s tail as `msvcrt.dll` has it: the kernel's `double` is negated
/// on one path by a sign mask loaded into `xmm5`, then narrowed to the
/// result.
const TANF_TAIL: [u8; 40] = [
    0x48, 0x83, 0xec, 0x28, // ASM: sub rsp,0x28
    0x89, 0x54, 0x24, 0x20, // ASM: mov [rsp+0x20],edx
    0xe8, 0x33, 0x00, 0x00, 0x00, // ASM: call 0x140001040
    0xf2, 0x0f, 0x10, 0x2d, 0xeb, 0x00, 0x00, 0x00, // ASM: movsd xmm5,[rip+0xeb]
    0x83, 0x7c, 0x24, 0x20, 0x00, // ASM: cmp dword [rsp+0x20],0
    0x74, 0x03, // ASM: je 0x14000101f
    0x0f, 0x57, 0xc5, // ASM: xorps xmm0,xmm5
    0xf2, 0x0f, 0x5a, 0xc0, // ASM: cvtsd2ss xmm0,xmm0
    0x48, 0x83, 0xc4, 0x28, // ASM: add rsp,0x28
    0xc3, // ASM: ret
];

/// A caller that reads `xmm0` after a branch past the call still takes the
/// callee's `double`, and the sign mask it loaded into a register negates
/// that `double`.
///
/// [`TANF_TAIL`] tests a flag before either path reads the result, so the
/// scan after the call follows both ways; the mask in `xmm5` is a known
/// constant, so `xorps` is the negation, not a vector of integer bits.
#[test]
fn a_result_read_past_a_branch_is_a_float() {
    let mut code = TANF_TAIL.to_vec();
    code.resize(0x40, 0xcc);
    code.extend_from_slice(&[
        0xf2, 0x0f, 0x59, 0xc0, // ASM: mulsd xmm0,xmm0
        0xc3, // ASM: ret
    ]);
    code.resize(0x100, 0xcc);
    code.extend_from_slice(&[0, 0, 0, 0, 0, 0, 0, 0x80, 0, 0, 0, 0, 0, 0, 0, 0]);
    let p = program64(&code);
    let a = Analysis::compute(&p);
    assert_eq!(
        a.function(0x1_4000_1040).and_then(|f| f.ret_float),
        Some(64)
    );
    let text = decompile(&p, &a, &Overlay::default(), 0x1_4000_1000).unwrap_or_default();
    assert!(text.contains("double sub_140001040("), "{text}");
    assert!(text.contains("= -var"), "{text}");
    assert!(!text.contains("u64x2"), "{text}");
    replays_clean(&p, &a, &[0x1_4000_1000, 0x1_4000_1040]);
}

/// `acosf`'s sign flip as `msvcrt.dll` has it: a broadcast single sign
/// mask from memory over a copy of the argument.
const ACOSF_FLIP: [u8; 18] = [
    0x0f, 0x28, 0xe0, // ASM: movaps xmm4,xmm0
    0x85, 0xd2, // ASM: test edx,edx
    0x79, 0x07, // ASM: jns 0x14000100e
    0x0f, 0x57, 0x25, 0xf2, 0x00, 0x00, 0x00, // ASM: xorps xmm4,[rip+0xf2]
    0x0f, 0x28, 0xc4, // ASM: movaps xmm0,xmm4
    0xc3, // ASM: ret
];

/// A sign mask over a register the text declares as an integer flips the
/// bits the machine flips, where C's `-` would negate the integer.
#[test]
fn a_sign_mask_over_integer_bits_flips_the_bits() {
    let mut code = ACOSF_FLIP.to_vec();
    code.resize(0x100, 0xcc);
    code.extend_from_slice(&[0, 0, 0, 0x80].repeat(4));
    let p = program64(&code);
    let a = Analysis::compute(&p);
    let text = decompile(&p, &a, &Overlay::default(), 0x1_4000_1000).unwrap_or_default();
    assert!(text.contains("^= 0x8000000080000000;"), "{text}");
    assert!(!text.contains("= -var"), "{text}");
    replays_clean(&p, &a, &[0x1_4000_1000]);
}

/// A conversion of a register the text declares as an integer converts the
/// `double` its bits encode, not the integer.
///
/// The broadcast mask leaves `xmm4` integer bits ([`ACOSF_FLIP`]'s
/// shape), and `cvtsd2ss` then reads them as a `double`.
#[test]
fn a_conversion_reads_integer_declared_bits_as_a_float() {
    let mut code = ACOSF_FLIP[..14].to_vec();
    code.extend_from_slice(&[
        0xf2, 0x0f, 0x5a, 0xc4, // ASM: cvtsd2ss xmm0,xmm4
        0xc3, // ASM: ret
    ]);
    code.resize(0x100, 0xcc);
    code.extend_from_slice(&[0, 0, 0, 0x80].repeat(4));
    let p = program64(&code);
    let a = Analysis::compute(&p);
    let text = decompile(&p, &a, &Overlay::default(), 0x1_4000_1000).unwrap_or_default();
    assert!(text.contains("*(double*)&var"), "{text}");
    replays_clean(&p, &a, &[0x1_4000_1000]);
}

/// A single loaded into a register that is no sign mask leaves `xorps`
/// to the vector code, and the decompiler does not fail on it.
#[test]
fn a_single_held_in_a_register_is_no_mask() {
    let mut code = vec![
        0xf3, 0x0f, 0x10, 0x0d, 0xf8, 0x00, 0x00, 0x00, // ASM: movss xmm1,[rip+0xf8]
        0x0f, 0x57, 0xc1, // ASM: xorps xmm0,xmm1
        0xc3, // ASM: ret
    ];
    code.resize(0x100, 0xcc);
    code.extend_from_slice(&[0x00, 0x00, 0x80, 0x3f]);
    let p = program64(&code);
    let a = Analysis::compute(&p);
    assert!(decompile(&p, &a, &Overlay::default(), 0x1_4000_1000).is_some());
    replays_clean(&p, &a, &[0x1_4000_1000]);
}

/// A mask in a register whose lanes are not of one shape over a `double`
/// is bits, not the `double`'s negation: the machine flips bit 31 too.
#[test]
fn a_mixed_mask_over_a_double_is_no_negation() {
    let mut code = vec![
        0xf2, 0x0f, 0x59, 0xc0, // ASM: mulsd xmm0,xmm0
        0xf2, 0x0f, 0x10, 0x0d, 0xf4, 0x00, 0x00, 0x00, // ASM: movsd xmm1,[rip+0xf4]
        0x0f, 0x57, 0xc1, // ASM: xorps xmm0,xmm1
        0xc3, // ASM: ret
    ];
    code.resize(0x100, 0xcc);
    code.extend_from_slice(&[0, 0, 0, 0x80, 0, 0, 0, 0x80]);
    let p = program64(&code);
    let a = Analysis::compute(&p);
    let text = decompile(&p, &a, &Overlay::default(), 0x1_4000_1000).unwrap_or_default();
    assert!(!text.contains("= -"), "{text}");
    replays_clean(&p, &a, &[0x1_4000_1000]);
}

/// A double's sign mask over a single loaded through a pointer is vector
/// work on the register, never an integer bit operation over a float,
/// which would not be C.
#[test]
fn a_mask_over_a_float_of_another_width_is_no_bit_operation() {
    let mut code = vec![
        0xf3, 0x0f, 0x10, 0x01, // ASM: movss xmm0,[rcx]
        0x66, 0x0f, 0x57, 0x05, 0xf4, 0x00, 0x00, 0x00, // ASM: xorpd xmm0,[rip+0xf4]
        0xf2, 0x0f, 0x11, 0x02, // ASM: movsd [rdx],xmm0
        0xc3, // ASM: ret
    ];
    code.resize(0x100, 0xcc);
    code.extend_from_slice(&[0, 0, 0, 0, 0, 0, 0, 0x80, 0, 0, 0, 0, 0, 0, 0, 0]);
    let p = program64(&code);
    let a = Analysis::compute(&p);
    let text = decompile(&p, &a, &Overlay::default(), 0x1_4000_1000).unwrap_or_default();
    assert!(!text.contains(" ^ 0x8000000000000000"), "{text}");
    assert!(!text.contains("^= 0x8000000000000000"), "{text}");
    replays_clean(&p, &a, &[0x1_4000_1000]);
}

/// A single's sign mask whose later lanes mix over a double flips bit 31,
/// not the double's sign: no negation of the double.
#[test]
fn a_mixed_single_mask_over_a_double_is_no_negation() {
    let mut code = vec![
        0xf2, 0x0f, 0x10, 0x01, // ASM: movsd xmm0,[rcx]
        0x0f, 0x57, 0x05, 0xf5, 0x00, 0x00, 0x00, // ASM: xorps xmm0,[rip+0xf5]
        0xf2, 0x0f, 0x11, 0x02, // ASM: movsd [rdx],xmm0
        0xc3, // ASM: ret
    ];
    code.resize(0x100, 0xcc);
    code.extend_from_slice(&[0, 0, 0, 0x80, 0, 0, 0, 0, 0, 0, 0, 0x80, 0, 0, 0, 0]);
    let p = program64(&code);
    let a = Analysis::compute(&p);
    let text = decompile(&p, &a, &Overlay::default(), 0x1_4000_1000).unwrap_or_default();
    assert!(!text.contains("= -"), "{text}");
    replays_clean(&p, &a, &[0x1_4000_1000]);
}

/// A single's broadcast sign mask over a double flips bit 31 and bit 63
/// of the double's bits, an integer `^` over those bits: `^` over a
/// `double` would not be C, and the store keeps the bits.
#[test]
fn a_single_sign_mask_over_a_double_xors_its_bits() {
    let mut code = vec![
        0xf2, 0x0f, 0x10, 0x01, // ASM: movsd xmm0,[rcx]
        0x0f, 0x57, 0x05, 0xf5, 0x00, 0x00, 0x00, // ASM: xorps xmm0,[rip+0xf5]
        0xf2, 0x0f, 0x11, 0x02, // ASM: movsd [rdx],xmm0
        0xc3, // ASM: ret
    ];
    code.resize(0x100, 0xcc);
    code.extend_from_slice(&[0, 0, 0, 0x80].repeat(4));
    let p = program64(&code);
    let a = Analysis::compute(&p);
    let text = decompile(&p, &a, &Overlay::default(), 0x1_4000_1000).unwrap_or_default();
    assert!(
        text.contains("*(uint64_t*)a2 = *(uint64_t*)a1 ^ 0x8000000080000000;"),
        "{text}"
    );
    assert!(!text.contains("*(double*)"), "{text}");
    replays_clean(&p, &a, &[0x1_4000_1000]);
}

/// A float copied into a register the text declares as an integer is
/// copied as its bits, and returned as the result's bits.
///
/// A plain `movaps` copies the argument into the register whose bits a
/// sign mask flips, and that register is handed back in `xmm0`: C would
/// convert the number on both copies. [`ACOSF_FLIP`] copies a `float`
/// argument, and the same shape ending in `cvtsd2ss xmm0,xmm4` copies a
/// `double` one.
#[test]
fn a_float_copied_into_integer_bits_is_copied_as_its_bits() {
    let mut code = ACOSF_FLIP.to_vec();
    code.resize(0x100, 0xcc);
    code.extend_from_slice(&[0, 0, 0, 0x80].repeat(4));
    let p = program64(&code);
    let a = Analysis::compute(&p);
    let text = decompile(&p, &a, &Overlay::default(), 0x1_4000_1000).unwrap_or_default();
    assert!(text.contains("var1 = *(uint32_t*)&a1;"), "{text}");
    assert!(!text.contains("return var1;"), "{text}");
    assert!(text.contains("return *("), "{text}");
    replays_clean(&p, &a, &[0x1_4000_1000]);

    let mut code = ACOSF_FLIP[..14].to_vec();
    code.extend_from_slice(&[
        0xf2, 0x0f, 0x5a, 0xc4, // ASM: cvtsd2ss xmm0,xmm4
        0xc3, // ASM: ret
    ]);
    code.resize(0x100, 0xcc);
    code.extend_from_slice(&[0, 0, 0, 0x80].repeat(4));
    let p = program64(&code);
    let a = Analysis::compute(&p);
    let text = decompile(&p, &a, &Overlay::default(), 0x1_4000_1000).unwrap_or_default();
    assert!(text.contains("var1 = *(uint64_t*)&a1;"), "{text}");
    replays_clean(&p, &a, &[0x1_4000_1000]);
}
