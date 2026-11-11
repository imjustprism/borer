//! Float parameters, results and conversions in the text.

use super::*;

/// A double handed back in xmm0 is a result, though nothing writes rax.
///
/// `call 0x140001020; movsd [rdx],xmm0; ret` reads xmm0 after calling the
/// wrapper `sub rsp,0x28; call 0x140001040; add rsp,0x28; ret`, which hands
/// on what `test rcx,rcx; jne L; xorps xmm0,xmm0; jmp E; L: cvtsi2sd
/// xmm0,rcx; E: ret` leaves there: both return a double.
#[test]
fn a_double_in_xmm0_is_a_result() {
    let mut code = vec![0xe8, 0x1b, 0x00, 0x00, 0x00, 0xf2, 0x0f, 0x11, 0x02, 0xc3];
    code.resize(0x20, 0xcc);
    code.extend_from_slice(&[
        0x48, 0x83, 0xec, 0x28, 0xe8, 0x17, 0x00, 0x00, 0x00, 0x48, 0x83, 0xc4, 0x28, 0xc3,
    ]);
    code.resize(0x40, 0xcc);
    code.extend_from_slice(&[
        0x48, 0x85, 0xc9, 0x75, 0x05, 0x0f, 0x57, 0xc0, 0xeb, 0x05, 0xf2, 0x48, 0x0f, 0x2a, 0xc1,
        0xc3,
    ]);
    let p = program64(&code);
    let a = Analysis::compute(&p);
    for entry in [0x1_4000_1020, 0x1_4000_1040] {
        let f = a.function(entry).map(|f| (f.returns_value, f.ret_float));
        assert_eq!(f, Some((Some(true), Some(64))), "{entry:#x}");
    }
    let text = decompile(&p, &a, &Overlay::default(), 0x1_4000_1040).unwrap_or_default();
    assert!(text.contains("// signature: double "), "{text}");
    assert!(text.contains("return (double)"), "{text}");
    assert!(!text.contains("return;"), "{text}");
    let wrapper = decompile(&p, &a, &Overlay::default(), 0x1_4000_1020).unwrap_or_default();
    assert!(wrapper.contains("// signature: double "), "{wrapper}");
    assert!(wrapper.contains("return sub_140001040("), "{wrapper}");
}

/// A double reaching the exit past a check is a result, never the check's.
///
/// `call 0x140001020; movsd [rdx],xmm0; ret` reads xmm0 after calling the
/// wrapper `sub rsp,0x28; call 0x140001040; call 0x140001060; add
/// rsp,0x28; ret`, whose double from `cvtsi2sd xmm0,rcx; ret` passes the
/// check `cmp rcx,rdx; jne F; ret; F: int3`, which touches no register a
/// result comes back in: the leaf takes the double's type, the wrapper
/// returns a value, and its text never returns the check's result.
#[test]
fn a_double_past_a_check_is_a_result() {
    let mut code = vec![0xe8, 0x1b, 0x00, 0x00, 0x00, 0xf2, 0x0f, 0x11, 0x02, 0xc3];
    code.resize(0x20, 0xcc);
    code.extend_from_slice(&[
        0x48, 0x83, 0xec, 0x28, 0xe8, 0x17, 0x00, 0x00, 0x00, 0xe8, 0x32, 0x00, 0x00, 0x00, 0x48,
        0x83, 0xc4, 0x28, 0xc3,
    ]);
    code.resize(0x40, 0xcc);
    code.extend_from_slice(&[0xf2, 0x48, 0x0f, 0x2a, 0xc1, 0xc3]);
    code.resize(0x60, 0xcc);
    code.extend_from_slice(&[0x48, 0x3b, 0xca, 0x75, 0x01, 0xc3, 0xcc]);
    let p = program64(&code);
    let a = Analysis::compute(&p);
    let leaf = a.function(0x1_4000_1040).map(|f| f.ret_float);
    assert_eq!(leaf, Some(Some(64)));
    let wrapper = a.function(0x1_4000_1020).map(|f| f.returns_value);
    assert_eq!(wrapper, Some(Some(true)));
    let text = decompile(&p, &a, &Overlay::default(), 0x1_4000_1020).unwrap_or_default();
    assert!(!text.contains("return sub_140001060"), "{text}");
}

/// A function whose double passes a check on its way out returns that
/// double, typed so: the check leaves `xmm0` as it found it, so the double
/// is still there at the `ret`.
///
/// The wrapper of [`a_double_past_a_check_is_a_result`], `sub rsp,0x28;
/// call 0x140001040; call 0x140001060; add rsp,0x28; ret`, keeps the
/// leaf's double across the check `cmp rcx,rdx; jne F; ret; F: int3`.
#[test]
fn a_double_past_a_check_types_its_function() {
    let mut code = vec![0xe8, 0x1b, 0x00, 0x00, 0x00, 0xf2, 0x0f, 0x11, 0x02, 0xc3];
    code.resize(0x20, 0xcc);
    code.extend_from_slice(&[
        0x48, 0x83, 0xec, 0x28, 0xe8, 0x17, 0x00, 0x00, 0x00, 0xe8, 0x32, 0x00, 0x00, 0x00, 0x48,
        0x83, 0xc4, 0x28, 0xc3,
    ]);
    code.resize(0x40, 0xcc);
    code.extend_from_slice(&[0xf2, 0x48, 0x0f, 0x2a, 0xc1, 0xc3]);
    code.resize(0x60, 0xcc);
    code.extend_from_slice(&[0x48, 0x3b, 0xca, 0x75, 0x01, 0xc3, 0xcc]);
    let p = program64(&code);
    let a = Analysis::compute(&p);
    let wrapper = a.function(0x1_4000_1020).map(|f| f.ret_float);
    assert_eq!(wrapper, Some(Some(64)));
    let text = decompile(&p, &a, &Overlay::default(), 0x1_4000_1020).unwrap_or_default();
    assert!(text.contains("// signature: double "), "{text}");
    assert!(text.contains("var1 = sub_140001040("), "{text}");
    assert!(text.contains("return var1;"), "{text}");
}

/// What a float function's callee leaves in rax is no result.
///
/// `call 0x140001020; movsd [rdx],xmm0; ret` takes a double from `sub
/// rsp,0x28; call 0x140001040; xorps xmm0,xmm0; add rsp,0x28; ret`, whose
/// call hands rax on unread to its `ret`; the callee there, `sub rsp,0x28;
/// call 0x140001060; add rsp,0x28; ret`, hands back only what `mov dword
/// [rcx],0; mov eax,5; ret` left, so it returns nothing.
#[test]
fn rax_handed_to_a_float_function_is_no_result() {
    let mut code = vec![0xe8, 0x1b, 0x00, 0x00, 0x00, 0xf2, 0x0f, 0x11, 0x02, 0xc3];
    code.resize(0x20, 0xcc);
    code.extend_from_slice(&[
        0x48, 0x83, 0xec, 0x28, 0xe8, 0x17, 0x00, 0x00, 0x00, 0x0f, 0x57, 0xc0, 0x48, 0x83, 0xc4,
        0x28, 0xc3,
    ]);
    code.resize(0x40, 0xcc);
    code.extend_from_slice(&[
        0x48, 0x83, 0xec, 0x28, 0xe8, 0x17, 0x00, 0x00, 0x00, 0x48, 0x83, 0xc4, 0x28, 0xc3,
    ]);
    code.resize(0x60, 0xcc);
    code.extend_from_slice(&[
        0xc7, 0x01, 0x00, 0x00, 0x00, 0x00, 0xb8, 0x05, 0x00, 0x00, 0x00, 0xc3,
    ]);
    let p = program64(&code);
    let a = Analysis::compute(&p);
    let float = a.function(0x1_4000_1020).map(|f| f.ret_float);
    assert_eq!(float, Some(Some(64)));
    let inner = a.function(0x1_4000_1040).map(|f| f.returns_value);
    assert_eq!(inner, Some(Some(false)));
}

/// A function forwarding a double returns it, whoever reads it.
///
/// `call 0x140001020; call 0x140001060; movsd [rdx],xmm0; ret` reads the
/// double `cvtsi2sd xmm0,rcx; ret` leaves; `jmp 0x140001060` forwards it
/// though its one caller, `call 0x140001040; xor eax,eax; ret`, drops it.
#[test]
fn forwarding_a_double_returns_it() {
    let mut code = vec![
        0xe8, 0x1b, 0x00, 0x00, 0x00, 0xe8, 0x56, 0x00, 0x00, 0x00, 0xf2, 0x0f, 0x11, 0x02, 0xc3,
    ];
    code.resize(0x20, 0xcc);
    code.extend_from_slice(&[0xe8, 0x1b, 0x00, 0x00, 0x00, 0x33, 0xc0, 0xc3]);
    code.resize(0x40, 0xcc);
    code.extend_from_slice(&[0xe9, 0x1b, 0x00, 0x00, 0x00]);
    code.resize(0x60, 0xcc);
    code.extend_from_slice(&[0xf2, 0x48, 0x0f, 0x2a, 0xc1, 0xc3]);
    let p = program64(&code);
    let a = Analysis::compute(&p);
    let forward = a
        .function(0x1_4000_1040)
        .map(|f| (f.returns_value, f.ret_float));
    assert_eq!(forward, Some((Some(true), Some(64))));
}

/// What a function returning a double leaves in rax is nothing.
///
/// `call 0x140001040; movsd [rdx],xmm0; ret` reads the double `cvtsi2sd
/// xmm0,rcx; ret` leaves, so the entry, `sub rsp,0x28; call 0x140001020;
/// call 0x140001040; addsd xmm0,xmm0; add rsp,0x28; ret`, which nothing
/// calls, hands back no value in rax: what it returns is the double its
/// own `addsd` leaves in xmm0.
#[test]
fn a_float_callee_leaves_nothing_in_rax() {
    let mut code = vec![
        0x48, 0x83, 0xec, 0x28, 0xe8, 0x17, 0x00, 0x00, 0x00, 0xe8, 0x32, 0x00, 0x00, 0x00, 0xf2,
        0x0f, 0x58, 0xc0, 0x48, 0x83, 0xc4, 0x28, 0xc3,
    ];
    code.resize(0x20, 0xcc);
    code.extend_from_slice(&[0xe8, 0x1b, 0x00, 0x00, 0x00, 0xf2, 0x0f, 0x11, 0x02, 0xc3]);
    code.resize(0x40, 0xcc);
    code.extend_from_slice(&[0xf2, 0x48, 0x0f, 0x2a, 0xc1, 0xc3]);
    let p = program64(&code);
    let a = Analysis::compute(&p);
    let leaf = a.function(0x1_4000_1040).map(|f| f.ret_float);
    assert_eq!(leaf, Some(Some(64)));
    let entry = a
        .function(0x1_4000_1000)
        .map(|f| (f.returns_value, f.ret_float));
    assert_eq!(entry, Some((Some(true), Some(64))));
}

/// A float written to xmm0 and stored is no result when no caller reads
/// it: `movsd xmm0,[rcx]; addsd xmm0,xmm0; movsd [rcx],xmm0; ret` called
/// by `call 0x140001040; xor eax,eax; ret` stays `void`.
#[test]
fn a_float_no_caller_reads_is_no_result() {
    let mut code = vec![0xe8, 0x3b, 0x00, 0x00, 0x00, 0x33, 0xc0, 0xc3];
    code.resize(0x40, 0xcc);
    code.extend_from_slice(&[
        0xf2, 0x0f, 0x10, 0x01, 0xf2, 0x0f, 0x58, 0xc0, 0xf2, 0x0f, 0x11, 0x01, 0xc3,
    ]);
    let p = program64(&code);
    let a = Analysis::compute(&p);
    let f = a.function(0x1_4000_1040).map(|f| f.ret_float);
    assert_eq!(f, Some(None));
    let text = decompile(&p, &a, &Overlay::default(), 0x1_4000_1040).unwrap_or_default();
    assert!(text.contains("// signature: void "), "{text}");
}

/// A function nothing calls returns the single it computes.
///
/// No call site says what a caller reads, so the body answers: `subss
/// xmm1,xmm0; mulss xmm1,xmm2; addss xmm0,xmm1; ret` writes xmm0 last and
/// never writes rax, so it hands back a `float`, and only the lane the
/// caller reads is returned, not the bits the scalar instructions kept
/// above it.
#[test]
fn a_function_nothing_calls_returns_the_single_it_computes() {
    let code = [
        0xf3, 0x0f, 0x5c, 0xc8, // ASM: subss xmm1,xmm0
        0xf3, 0x0f, 0x59, 0xca, // ASM: mulss xmm1,xmm2
        0xf3, 0x0f, 0x58, 0xc1, // ASM: addss xmm0,xmm1
        0xc3, // ASM: ret
    ];
    let p = program64(&code);
    let a = Analysis::compute(&p);
    let f = a.function(0x1_4000_1000).map(|f| f.ret_float);
    assert_eq!(f, Some(Some(32)));
    let text = decompile(&p, &a, &Overlay::default(), 0x1_4000_1000).unwrap_or_default();
    assert!(text.contains("// signature: float "), "{text}");
    assert!(text.contains("return a1 + (a2 - a1) * a3;"), "{text}");
}

/// A function nothing calls returns the double it moves into xmm0 after
/// its integer work.
///
/// `mov eax,edx; cvtsi2sd xmm1,eax; addsd xmm1,xmm0; movapd xmm0,xmm1;
/// ret` writes rax first and xmm0 nearest the exit, so the result is the
/// `double`, and the precision the scalar instructions read names the
/// parameter's type.
#[test]
fn a_function_nothing_calls_returns_the_double_it_moves_back() {
    let code = [
        0x89, 0xd0, // ASM: mov eax,edx
        0xf2, 0x0f, 0x2a, 0xc8, // ASM: cvtsi2sd xmm1,eax
        0xf2, 0x0f, 0x58, 0xc8, // ASM: addsd xmm1,xmm0
        0x66, 0x0f, 0x28, 0xc1, // ASM: movapd xmm0,xmm1
        0xc3, // ASM: ret
    ];
    let p = program64(&code);
    let a = Analysis::compute(&p);
    let f = a.function(0x1_4000_1000).map(|f| f.ret_float);
    assert_eq!(f, Some(Some(64)));
    let text = decompile(&p, &a, &Overlay::default(), 0x1_4000_1000).unwrap_or_default();
    assert!(text.contains("// signature: double "), "{text}");
    assert!(text.contains("double a1"), "{text}");
}

/// A float parameter is typed by the precision that reads it.
///
/// `mulsd xmm0,xmm0; cvttsd2si eax,xmm0; ret` reads its first argument as
/// a `double`, not the `float` every vector parameter used to be.
#[test]
fn a_float_parameter_takes_the_precision_that_reads_it() {
    let code = [
        0xf2, 0x0f, 0x59, 0xc0, // ASM: mulsd xmm0,xmm0
        0xf2, 0x0f, 0x2c, 0xc0, // ASM: cvttsd2si eax,xmm0
        0xc3, // ASM: ret
    ];
    let p = program64(&code);
    let a = Analysis::compute(&p);
    let text = decompile(&p, &a, &Overlay::default(), 0x1_4000_1000).unwrap_or_default();
    assert!(text.contains("(double a1)"), "{text}");
}

/// A float exit through a bit copy takes the precision of what it copies.
///
/// `subss xmm2,xmm0; mulss xmm2,xmm2; movaps xmm0,xmm2; ret`, which
/// nothing calls, returns the single `mulss` left: the `movaps` that moves
/// it names no precision of its own, its source's writer does.
#[test]
fn a_copied_single_is_a_float_result() {
    let code = [
        0xf3, 0x0f, 0x5c, 0xd0, // ASM: subss xmm2,xmm0
        0xf3, 0x0f, 0x59, 0xd2, // ASM: mulss xmm2,xmm2
        0x0f, 0x28, 0xc2, // ASM: movaps xmm0,xmm2
        0xc3, // ASM: ret
    ];
    let p = program64(&code);
    let a = Analysis::compute(&p);
    let f = a.function(0x1_4000_1000).map(|f| f.ret_float);
    assert_eq!(f, Some(Some(32)));
    let text = decompile(&p, &a, &Overlay::default(), 0x1_4000_1000).unwrap_or_default();
    assert!(text.contains("// signature: float "), "{text}");
    assert!(!text.contains("0xffffffff00000000"), "{text}");
}

/// The check reads a float parameter at the width the signature gives it.
///
/// `cvtss2sd xmm0,xmm0; ret`, which nothing calls, is `double f(float a1)`
/// returning `(double)a1`: the machine converts the single in `xmm0`, and
/// so does the text, so every block agrees.
#[test]
fn a_float_parameter_converts_as_the_float_it_is() {
    let code = [
        0xf3, 0x0f, 0x5a, 0xc0, // ASM: cvtss2sd xmm0,xmm0
        0xc3, // ASM: ret
    ];
    let p = program64(&code);
    let a = Analysis::compute(&p);
    let text = decompile(&p, &a, &Overlay::default(), 0x1_4000_1000).unwrap_or_default();
    assert!(text.contains("(float a1)"), "{text}");
    replays_clean(&p, &a, &[0x1_4000_1000]);
}

/// A body that names no precision returns the float its callers read.
///
/// `movd xmm0,ecx; ret` is `f32::from_bits`: the move names no width, and
/// the caller's `cvtss2sd xmm0,xmm0` after `call` reads a single, so the
/// callee returns a `float` and the caller's result is one too.
#[test]
fn a_bit_move_returns_the_float_its_callers_read() {
    let mut code = vec![
        0xe8, 0x3b, 0x00, 0x00, 0x00, // ASM: call 0x140001040
        0xf3, 0x0f, 0x5a, 0xc0, // ASM: cvtss2sd xmm0,xmm0
        0xf2, 0x0f, 0x11, 0x02, // ASM: movsd [rdx],xmm0
        0xc3, // ASM: ret
    ];
    code.resize(0x40, 0xcc);
    code.extend_from_slice(&[
        0x66, 0x0f, 0x6e, 0xc1, // ASM: movd xmm0,ecx
        0xc3, // ASM: ret
    ]);
    let p = program64(&code);
    let a = Analysis::compute(&p);
    let callee = a.function(0x1_4000_1040).map(|f| f.ret_float);
    assert_eq!(callee, Some(Some(32)));
    let text = decompile(&p, &a, &Overlay::default(), 0x1_4000_1000).unwrap_or_default();
    replays_clean(&p, &a, &[0x1_4000_1000]);
    assert!(!text.contains("double xmm0"), "{text}");
}

/// The check reads each call's float result at that callee's width.
///
/// The body is a debug build's `match` on `a2`, copied from one: one arm
/// returns a `double` callee's result (`cvtsi2sd xmm0,rcx; ret`), the
/// other widens what `f32::from_bits` returns (`movd xmm0,ecx; ret`, read
/// by `cvtss2sd`). The function declares `xmm0` once, as the `double`,
/// yet the block after the second call starts with the single its callee
/// left, and the check converts it as one.
#[test]
fn each_float_call_result_is_checked_at_its_callees_width() {
    let mut code = vec![
        0x48, 0x83, 0xec, 0x48, // ASM: sub rsp,0x48
        0x48, 0x89, 0x4c, 0x24, 0x28, // ASM: mov [rsp+0x28],rcx
        0x48, 0x89, 0x4c, 0x24, 0x38, // ASM: mov [rsp+0x38],rcx
        0x66, 0x89, 0x54, 0x24, 0x42, // ASM: mov [rsp+0x42],dx
        0x66, 0x83, 0xfa, 0x20, // ASM: cmp dx,0x20
        0x74, 0x12, // ASM: je 0x14000102b
        0x48, 0x8b, 0x4c, 0x24, 0x28, // ASM: mov rcx,[rsp+0x28]
        0xe8, 0x3d, 0x00, 0x00, 0x00, // ASM: call 0x140001060
        0xf2, 0x0f, 0x11, 0x44, 0x24, 0x30, // ASM: movsd [rsp+0x30],xmm0
        0xeb, 0x21, // ASM: jmp 0x14000104c
        0x48, 0x8b, 0x4c, 0x24, 0x28, // ASM: mov rcx,[rsp+0x28]
        0xe8, 0x3b, 0x00, 0x00, 0x00, // ASM: call 0x140001070
        0x89, 0xc1, // ASM: mov ecx,eax
        0xe8, 0x44, 0x00, 0x00, 0x00, // ASM: call 0x140001080
        0xf3, 0x0f, 0x11, 0x44, 0x24, 0x44, // ASM: movss [rsp+0x44],xmm0
        0xf3, 0x0f, 0x5a, 0xc0, // ASM: cvtss2sd xmm0,xmm0
        0xf2, 0x0f, 0x11, 0x44, 0x24, 0x30, // ASM: movsd [rsp+0x30],xmm0
        0xf2, 0x0f, 0x10, 0x44, 0x24, 0x30, // ASM: movsd xmm0,[rsp+0x30]
        0x48, 0x83, 0xc4, 0x48, // ASM: add rsp,0x48
        0xc3, // ASM: ret
    ];
    code.resize(0x60, 0xcc);
    code.extend_from_slice(&[
        0xf2, 0x48, 0x0f, 0x2a, 0xc1, // ASM: cvtsi2sd xmm0,rcx
        0xc3, // ASM: ret
    ]);
    code.resize(0x70, 0xcc);
    code.extend_from_slice(&[
        0x89, 0xc8, // ASM: mov eax,ecx
        0xc3, // ASM: ret
    ]);
    code.resize(0x80, 0xcc);
    code.extend_from_slice(&[
        0x50, // ASM: push rax
        0x89, 0x4c, 0x24, 0x04, // ASM: mov [rsp+4],ecx
        0x66, 0x0f, 0x6e, 0xc1, // ASM: movd xmm0,ecx
        0x58, // ASM: pop rax
        0xc3, // ASM: ret
    ]);
    let p = program64(&code);
    let a = Analysis::compute(&p);
    let widths = [0x1_4000_1060, 0x1_4000_1080].map(|e| a.function(e).and_then(|f| f.ret_float));
    assert_eq!(widths, [Some(64), Some(32)]);
    replays_clean(&p, &a, &[0x1_4000_1000]);
}

/// A 32-bit function its callers hand a float in `xmm0` takes it as a
/// parameter.
///
/// `cvtss2sd xmm0,xmm0; ret`, called as `call; movsd [ecx],xmm0`, is a
/// C runtime SSE2 helper's shape: its float arrives in `xmm0` after its
/// stack arguments, so it is `a1`, a `float`, apart from the `double` the
/// register then holds.
#[test]
fn a_32_bit_function_takes_the_float_its_callers_pass_in_xmm0() {
    let mut code = vec![
        0xe8, 0x1b, 0x00, 0x00, 0x00, // ASM: call 0x401020
        0xf2, 0x0f, 0x11, 0x01, // ASM: movsd [ecx],xmm0
        0xc3, // ASM: ret
    ];
    code.resize(0x20, 0xcc);
    code.extend_from_slice(&[
        0xf3, 0x0f, 0x5a, 0xc0, // ASM: cvtss2sd xmm0,xmm0
        0xc3, // ASM: ret
    ]);
    let p = program32(&code);
    let a = Analysis::compute(&p);
    let text = decompile(&p, &a, &Overlay::default(), 0x401_020).unwrap_or_default();
    assert!(text.contains("(float a1)"), "{text}");
    replays_clean(&p, &a, &[0x401_020]);
}

/// A 32-bit function's float parameter converts to an integer as the float
/// it is: `cvttss2si eax,xmm0; ret`, called as `call; mov [ecx],eax`,
/// truncates the single its caller passed in `xmm0`.
#[test]
fn a_32_bit_float_parameter_converts_to_an_integer() {
    let mut code = vec![
        0xe8, 0x1b, 0x00, 0x00, 0x00, // ASM: call 0x401020
        0x89, 0x01, // ASM: mov [ecx],eax
        0xc3, // ASM: ret
    ];
    code.resize(0x20, 0xcc);
    code.extend_from_slice(&[
        0xf3, 0x0f, 0x2c, 0xc0, // ASM: cvttss2si eax,xmm0
        0xc3, // ASM: ret
    ]);
    let p = program32(&code);
    let a = Analysis::compute(&p);
    let text = decompile(&p, &a, &Overlay::default(), 0x401_020).unwrap_or_default();
    assert!(text.contains("(float a1)"), "{text}");
    replays_clean(&p, &a, &[0x401_020]);
}

/// A 32-bit function returning a single in `xmm0` returns a `float`.
///
/// `cvtsd2ss xmm0,xmm0; ret` keeps the bits above the lane it writes, but
/// its caller (`call; cvtss2sd xmm0,xmm0; movsd [ecx],xmm0`) reads only
/// that lane, so the result is the single, not the merged register.
#[test]
fn a_32_bit_single_result_is_a_float() {
    let mut code = vec![
        0xe8, 0x1b, 0x00, 0x00, 0x00, // ASM: call 0x401020
        0xf3, 0x0f, 0x5a, 0xc0, // ASM: cvtss2sd xmm0,xmm0
        0xf2, 0x0f, 0x11, 0x01, // ASM: movsd [ecx],xmm0
        0xc3, // ASM: ret
    ];
    code.resize(0x20, 0xcc);
    code.extend_from_slice(&[
        0xf2, 0x0f, 0x5a, 0xc0, // ASM: cvtsd2ss xmm0,xmm0
        0xc3, // ASM: ret
    ]);
    let p = program32(&code);
    let a = Analysis::compute(&p);
    let text = decompile(&p, &a, &Overlay::default(), 0x401_020).unwrap_or_default();
    assert!(text.contains("// signature: float "), "{text}");
    replays_clean(&p, &a, &[0x401_020]);
}

/// A prologue store of `xmm6`, callee-saved under the Microsoft x64
/// convention, is a save and not a local, even where a call would
/// reload the locals around it.
///
/// `sub rsp,0x38; movaps [rsp+0x20],xmm6; lea rcx,[rsp+0x10]; call
/// 0x140001040; xorps xmm6,xmm6; addss xmm6,xmm0; movaps xmm0,xmm6;
/// movaps xmm6,[rsp+0x20]; add rsp,0x38; ret`; the callee `mov eax,1;
/// ret`.
#[test]
fn a_saved_xmm_register_is_not_a_local() {
    let mut code = vec![
        0x48, 0x83, 0xec, 0x38, 0x0f, 0x29, 0x74, 0x24, 0x20, 0x48, 0x8d, 0x4c, 0x24, 0x10, 0xe8,
        0x2d, 0x00, 0x00, 0x00, 0x0f, 0x57, 0xf6, 0xf3, 0x0f, 0x58, 0xf0, 0x0f, 0x28, 0xc6, 0x0f,
        0x28, 0x74, 0x24, 0x20, 0x48, 0x83, 0xc4, 0x38, 0xc3,
    ];
    code.resize(0x40, 0xcc);
    code.extend_from_slice(&[0xb8, 0x01, 0x00, 0x00, 0x00, 0xc3]);
    let p = program64(&code);
    let text = decompiled(&p, 0x1_4000_1000);
    assert!(!text.contains("uint128_t"), "{text}");
    assert!(!text.contains("= xmm6;"), "{text}");
}

/// A float parked in a home slot and read back as bits is a float
/// parameter: the callee takes `float a1` and the caller passes the
/// float, not `rcx`.
///
/// The caller is `movss xmm0,[rip+c]; call 0x140001040; ret` with `c`
/// holding 2.0f, the callee `movss [rsp+8],xmm0; mov eax,[rsp+8]; ret`.
#[test]
fn a_float_parked_in_a_home_slot_is_a_float_parameter() {
    let mut code = vec![
        0xf3, 0x0f, 0x10, 0x05, 0xf8, 0x0f, 0x00, 0x00, 0xe8, 0x33, 0x00, 0x00, 0x00, 0xc3,
    ];
    code.resize(0x40, 0xcc);
    code.extend_from_slice(&[
        0xf3, 0x0f, 0x11, 0x44, 0x24, 0x08, 0x8b, 0x44, 0x24, 0x08, 0xc3,
    ]);
    let p = program64_with_data(&code, &2.0f32.to_le_bytes());
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let caller = decompile(&p, &a, &o, 0x1_4000_1000).unwrap_or_default();
    assert!(caller.contains("sub_140001040(2."), "{caller}");
    assert!(!caller.contains("rcx"), "{caller}");
    let callee = decompile(&p, &a, &o, 0x1_4000_1040).unwrap_or_default();
    assert!(callee.contains("sub_140001040(float a1)"), "{callee}");
}

/// `FL2`: `xorps` with the sign mask negates, `andps` with the magnitude mask
/// is `fabs`; the mask constants never appear.
///
/// `FL2` has no `ret` of its own and runs up to `FL3`, a function in its
/// own right. The walk once fell through into it and rendered both as one,
/// which is where the extra field accesses came from that earned `a1` a
/// layout; a fall-through into another function's start is now where a
/// function ends, so `FL2` is its own six instructions.
#[test]
fn float_sign_and_magnitude_masks_render_as_neg_and_fabs() {
    let out = dc(0x1320);
    assert!(
        out.contains("6 instructions"),
        "FL3 was absorbed again:
{out}"
    );
    assert!(out.contains("*(float*)a2 = -*(float*)a1;"), "{out}");
    assert!(
        out.contains("*(float*)(a2 + 4) = fabs(*(float*)(a1 + 4));"),
        "{out}"
    );
    assert!(!out.contains("0x2070") && !out.contains("0x2080"), "{out}");
}

/// `FR`: a call whose result the next instruction reads from `xmm0` binds a
/// typed float result instead of leaving a stale register name.
#[test]
fn float_call_result_is_bound_to_xmm0() {
    let out = dc(0x13f0);
    assert!(out.contains("var1 = sub_1400();"), "{out}");
    assert!(out.contains("*(float*)rcx = var1;"), "{out}");
    assert!(out.contains("float var1;"), "{out}");
}

/// A loop exit that only returns is written inline even when the loop has
/// no single continuation.
///
/// `LP3`'s fall-through `F` is also the prologue's target, so the loop's
/// exits meet nowhere; its other exit `E` sets the result and returns, so
/// it is written in place of its `goto`.
#[test]
fn returning_loop_exits_are_inlined_without_a_single_continuation() {
    let out = dc(0x1cf0);
    assert!(!out.contains("goto "), "{out}");
    assert!(out.contains("while (1) {"), "{out}");
    assert!(out.contains("break;"), "{out}");
    assert!(out.contains("return a1;"), "{out}");
}

/// The double-width shifts lift instead of leaving an assembly comment.
///
/// `SH` is `shld rax, rdx, cl` and `SH2` is `shrd rax, rdx, cl`: each
/// combines the two registers around a count masked to the operand's
/// width.
#[test]
fn double_width_shifts_lift() {
    let shld = dc(0x41d0);
    assert!(!shld.contains("/*"), "{shld}");
    assert!(
        shld.contains("<<") && shld.contains(">>") && shld.contains(" | "),
        "{shld}"
    );
    let shrd = dc(0x41e0);
    assert!(!shrd.contains("/*"), "{shrd}");
    assert!(
        shrd.contains("<<") && shrd.contains(">>") && shrd.contains(" | "),
        "{shrd}"
    );
}

/// A float comparison drops the unordered test the compiler branched on.
///
/// `x != y` on floats compiles to a parity branch and then a not-equal
/// branch; C's `!=` is already true when an operand is NaN, so the pair is
/// the comparison alone, and `!isunordered(x, y) && x == y` is `x == y`.
#[test]
fn unordered_float_compares_fold_to_the_comparison() {
    let text = "if (isunordered(xmm8, 0.0) || xmm8 != 0.0) {
  return 1;
}
if (!isunordered(xmm6, local_3f0) && xmm6 == local_3f0) {
  return 2;
}
if (rax > 0 || (isunordered(xmm1, xmm2) || xmm1 != xmm2)) {
  return 3;
}
return 0;
";
    let out = cleanup(text);
    assert!(out.contains("if (xmm8 != 0.0) {"), "{out}");
    assert!(out.contains("if (xmm6 == local_3f0) {"), "{out}");
    assert!(out.contains("xmm1 != xmm2"), "{out}");
    assert!(!out.contains("isunordered"), "{out}");
}

/// A function returning floating point hands the value back in xmm0.
///
/// `Fr::Get` multiplies two of its own floats and returns the product,
/// which never touches `rax`; reading `rax` at the return leaves the
/// multiply dead and hands back a register the function never set.
#[test]
fn a_float_return_comes_back_in_the_float_register() {
    let out = dc(0x5130);
    assert!(
        out.contains(
            "return *(float*)((uintptr_t)this + 0x10) * *(float*)((uintptr_t)this + 0x14);"
        ),
        "{out}"
    );
}

/// An argument that travels in a vector register is still an argument.
///
/// `FP` reads `xmm1`, which is where the second argument goes when it is a
/// float, and `FC` passes one there. Reading only `rcx`, `rdx`, `r8` and
/// `r9` left the argument out of the signature and out of the call.
#[test]
fn a_float_argument_is_a_parameter_and_shows_at_the_call() {
    let callee = dc(0x5580);
    assert!(callee.contains("float a2"), "{callee}");
    let caller = dc(0x5590);
    assert!(
        caller.contains("sub_5580(a2, *(float*)a2)"),
        "the float is missing: {caller}"
    );
}

/// A System V floating argument is still an argument.
///
/// The convention counts its integer and floating arguments separately:
/// `SF` takes an integer in `rdi` and a double in `xmm0`, and `SC` passes
/// one of each. The float mask left the double out of the callee's
/// signature and out of the call, as no register carried it.
///
/// # Panics
///
/// When the double is missing from either text.
#[test]
fn a_sysv_float_argument_is_a_parameter_and_shows_at_the_call() {
    use borer_engine::program::{Arch, BinaryFormat, Program, Section};
    let mut code = vec![
        0xbf, 0x05, 0x00, 0x00, 0x00, // ASM: mov edi,5
        0xf2, 0x0f, 0x10, 0x05, 0xf3, 0x0f, 0x00,
        0x00, // ASM: movsd xmm0,[rip+0xff3] -> 0x140002000
        0xe8, 0x0e, 0x00, 0x00, 0x00, // ASM: call 0x140001020 (SF)
        0xc3, // ASM: ret
    ];
    code.resize(0x20, 0xcc);
    code.extend_from_slice(&[
        0xf2, 0x0f, 0x59, 0xc0, // ASM: mulsd xmm0,xmm0
        0xf2, 0x48, 0x0f, 0x2c, 0xc0, // ASM: cvttsd2si rax,xmm0
        0x48, 0x01, 0xf8, // ASM: add rax,rdi
        0xc3, // ASM: ret
    ]);
    let mut bytes = vec![0u8; 0x1000];
    bytes[..code.len()].copy_from_slice(&code);
    bytes.extend_from_slice(&2.5f64.to_le_bytes());
    bytes.resize(0x2000, 0);
    let mut p = Program::raw(
        bytes,
        Arch::X86_64,
        0x1_4000_0000,
        Some(0x1_4000_1000),
        vec![
            Section::mapped(".text", 0x1_4000_1000, 0, 0x1000, false, true),
            Section::mapped(".rodata", 0x1_4000_2000, 0x1000, 0x1000, false, false),
        ],
    );
    p.format = BinaryFormat::Elf;
    let callee = decompiled(&p, 0x1_4000_1020);
    assert!(callee.contains("double a2"), "{callee}");
    let caller = decompiled(&p, 0x1_4000_1000);
    assert!(
        caller.contains("sub_140001020(5, 2.5)"),
        "the double is missing: {caller}"
    );
}

/// Double-precision shifts by a constant and `xgetbv` lift.
///
/// `SD` renders `(a1 << 8) | (a2 >> 0x18)` and `XG` returns `xgetbv(a1)`,
/// neither with an asm comment.
#[test]
fn double_shifts_and_xgetbv_lift() {
    let sd = dc(0x18a0);
    assert!(!sd.contains("/*"), "{sd}");
    assert!(sd.contains("(a1 << 8) | (a2 >> 0x18)"), "{sd}");
    let xg = dc(0x18b0);
    assert!(!xg.contains("/*"), "{xg}");
    assert!(xg.contains("xgetbv("), "{xg}");
}

/// Singletons render by their class, under the name a pack gives the
/// static.
///
/// `Tls::Tls` stores `Tls::instance = this;` and `TU` reads `Tls::instance`
/// through the same TLS walk; a pack naming the static `Singleton` makes it
/// `Tls::Singleton`. A global singleton (`GU` through `Glob::Glob`'s global)
/// resolves its virtual call.
#[test]
fn tls_singletons_render_by_class() {
    let tc = dc(0x1a60);
    assert!(tc.contains("Tls::instance = this;"), "{tc}");
    let tu = dc(0x1a90);
    assert!(tu.contains("Tls::instance"), "{tu}");
    assert!(!tu.contains("gs + 0x58"), "{tu}");
    let gu = dc(0x1b00);
    assert!(gu.contains("g64_27c0->"), "{gu}");
    let named = dc_pack(0x1a60);
    assert!(named.contains("Tls::Singleton = this;"), "{named}");
}

/// A receiver the class machinery names as a singleton resolves its virtual
/// call, and one whose class holds no table does not.
///
/// `GU` calls slot 1 through the global that holds the one `Glob`, and `TW`
/// walks `TU`'s TLS path for the singleton of `T2`, a class whose
/// constructor stores a vtable, so both calls resolve to the slot's
/// function; `TU`'s `Tls` registered a singleton but has no table, so its
/// call still names the slot.
#[test]
fn singleton_receivers_resolve_their_virtual_calls() {
    let p = fixture();
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let method = |va: u64| {
        let full = borer_engine::analysis::name_of(&a, &o, va);
        full.rsplit("::").next().unwrap_or(&full).to_owned()
    };
    let gu = decompile(&p, &a, &o, 0x1b00).unwrap_or_default();
    let glob_slot1 = method(0x13a0);
    assert!(gu.contains(&format!("g64_27c0->{glob_slot1}(")), "{gu}");
    let tw = decompile(&p, &a, &o, 0x57a0).unwrap_or_default();
    let t2_slot1 = method(0x57c6);
    assert!(tw.contains(&format!("T2::instance->{t2_slot1}(")), "{tw}");
    assert!(!tw.contains("->vtable["), "{tw}");
    assert_eq!(
        borer_engine::analysis::decompile::virtual_callees(&p, &a, &o, 0x57a0),
        vec![0x57c6]
    );
    let tu = decompile(&p, &a, &o, 0x1a90).unwrap_or_default();
    assert!(tu.contains("Tls::instance->vtable[1]()"), "{tu}");
}

/// A float argument a call takes keeps its value up to the call.
///
/// `sub rsp,0x28; movss xmm1,[rcx+0x10]; movss [rcx+0x20],xmm1; mov dword
/// [rcx+0x30],0; call f; add rsp,0x28; ret` with `f` taking `xmm1`: the
/// value loaded is written out before the store and passed, where the
/// store once dropped it as unread and the call passed `xmm1`, a variable
/// the text never assigned.
#[test]
fn a_float_argument_keeps_its_value_up_to_the_call() {
    let mut code = vec![
        0x48, 0x83, 0xec, 0x28, 0xf3, 0x0f, 0x10, 0x49, 0x10, 0xf3, 0x0f, 0x11, 0x49, 0x20, 0xc7,
        0x41, 0x30, 0x00, 0x00, 0x00, 0x00, 0xe8, 0x26, 0x00, 0x00, 0x00, 0x48, 0x83, 0xc4, 0x28,
        0xc3,
    ];
    code.resize(0x40, 0xcc);
    code.extend_from_slice(&[0x0f, 0x28, 0xc1, 0xc3]);
    let p = program64(&code);
    let text = decompiled(&p, 0x1_4000_1000);
    assert!(text.contains("var1 = a1->field_0x10;"), "{text}");
    assert!(text.contains("sub_140001040(a1, var1);"), "{text}");
}

/// `je` after `comiss` holds on a NaN. C's `==` does not.
///
/// The compiler's `jp` then `je` is still C's `==`: unordered takes the
/// other arm. A lone `je` has no such arm, so the test is equality or
/// unordered. `jne` is that test inverted, not C's `!=`.
#[test]
fn a_float_equality_includes_unordered() {
    use borer_engine::analysis::decompile::replay::{replay_function, replay_tsv};
    use borer_engine::analysis::decompile::verify::{verify, verify_tsv};

    let cases: &[(&[u8], &[&str])] = &[
        // ASM: movss xmm0,[rcx] / comiss xmm0,[rdx] / je / mov eax,1 / ret
        // ASM: mov eax,2 / ret
        (
            &[
                0xf3, 0x0f, 0x10, 0x01, 0x0f, 0x2f, 0x02, 0x74, 0x06, 0xb8, 0x01, 0x00, 0x00, 0x00,
                0xc3, 0xb8, 0x02, 0x00, 0x00, 0x00, 0xc3,
            ],
            &["isunordered", "=="],
        ),
        // ASM: movss xmm0,[rcx] / comiss xmm0,[rdx] / jne / mov eax,1 / ret
        // ASM: mov eax,2 / ret
        (
            &[
                0xf3, 0x0f, 0x10, 0x01, 0x0f, 0x2f, 0x02, 0x75, 0x06, 0xb8, 0x01, 0x00, 0x00, 0x00,
                0xc3, 0xb8, 0x02, 0x00, 0x00, 0x00, 0xc3,
            ],
            &["isunordered"],
        ),
        // ASM: movss xmm0,[rcx] / comiss xmm0,[rdx] / jp / mov eax,1 / ret
        // ASM: je / mov eax,2 / ret / mov eax,3 / ret
        (
            &[
                0xf3, 0x0f, 0x10, 0x01, 0x0f, 0x2f, 0x02, 0x7a, 0x06, 0xb8, 0x01, 0x00, 0x00, 0x00,
                0xc3, 0x74, 0x06, 0xb8, 0x02, 0x00, 0x00, 0x00, 0xc3, 0xb8, 0x03, 0x00, 0x00, 0x00,
                0xc3,
            ],
            &["=="],
        ),
    ];
    for (code, parts) in cases {
        let p = program64(code);
        let text = decompiled(&p, 0x1_4000_1000);
        for part in *parts {
            assert!(text.contains(part), "missing `{part}`\n{text}");
        }
        assert!(!text.contains("/* asm"), "{text}");
        let a = Analysis::compute(&p);
        for seed in 1..=8 {
            let v = verify(&p, &a, &[0x1_4000_1000], seed);
            assert!(
                v.checked > 0 && v.mismatches.is_empty() && v.unreadable == 0,
                "{text}\nseed {seed}: {}",
                verify_tsv(&v)
            );
            let r = replay_function(&p, &a, 0x1_4000_1000, seed);
            assert!(
                r.checked > 0 && r.wrong().is_empty(),
                "{text}\nseed {seed}: {}",
                replay_tsv(&r)
            );
        }
    }
}

/// The SSE2 conversion of an unsigned 64-bit integer to a double is that
/// cast.
///
/// `movq xmm0,rcx; punpckldq xmm0,[k1]; subpd xmm0,[k2]; movapd xmm1,xmm0;
/// unpckhpd xmm1,xmm0; addsd xmm1,xmm0; movapd xmm0,xmm1; ret` with the
/// exponent and bias constants compilers emit for `(double)n`.
#[test]
fn the_unsigned_to_double_idiom_is_a_cast() {
    let code = [
        0x66, 0x48, 0x0f, 0x6e, 0xc1, // ASM: movq xmm0,rcx
        0x66, 0x0f, 0x62, 0x05, 0xf3, 0x0f, 0x00, 0x00, // ASM: punpckldq xmm0,[rip+0xff3]
        0x66, 0x0f, 0x5c, 0x05, 0xfb, 0x0f, 0x00, 0x00, // ASM: subpd xmm0,[rip+0xffb]
        0x66, 0x0f, 0x28, 0xc8, // ASM: movapd xmm1,xmm0
        0x66, 0x0f, 0x15, 0xc8, // ASM: unpckhpd xmm1,xmm0
        0xf2, 0x0f, 0x58, 0xc8, // ASM: addsd xmm1,xmm0
        0x66, 0x0f, 0x28, 0xc1, // ASM: movapd xmm0,xmm1
        0xc3, // ASM: ret
    ];
    let mut data: Vec<u8> = [0x4330_0000u32, 0x4530_0000, 0, 0]
        .iter()
        .flat_map(|v| v.to_le_bytes())
        .collect();
    data.extend(0x4330_0000_0000_0000u64.to_le_bytes());
    data.extend(0x4530_0000_0000_0000u64.to_le_bytes());
    let p = program64_with_data(&code, &data);
    let text = decompiled(&p, 0x1_4000_1000);
    assert!(text.contains("return (double)a1;"), "{text}");
    assert!(!text.contains("unpckhpd"), "{text}");
}

/// A `double` spilled whole and read back a word at a time is no view of
/// two integer fields: a shift of the number is no C at all.
///
/// `hi(double d)` returns the high 32 bits of `d`'s encoding, as clang
/// `-O0` for System V x86-64 builds it. The view of a spilled structure's
/// fields (`a1 >> 32` over an `int` pair) must not take a `double` for
/// one; its bits wait for a bit cast.
#[test]
fn a_spilled_double_is_no_pair_of_integer_fields() {
    use borer_engine::program::{Arch, BinaryFormat, Program, Section};
    let code = [
        0x55, // ASM: push rbp
        0x48, 0x89, 0xe5, // ASM: mov rbp,rsp
        0xf2, 0x0f, 0x11, 0x45, 0xf8, // ASM: movsd [rbp-0x8],xmm0
        0x8b, 0x45, 0xfc, // ASM: mov eax,[rbp-0x4]
        0x5d, // ASM: pop rbp
        0xc3, // ASM: ret
    ];
    let mut bytes = vec![0u8; 0x1000];
    bytes[..code.len()].copy_from_slice(&code);
    let mut p = Program::raw(
        bytes,
        Arch::X86_64,
        0x400_000,
        Some(0x401_000),
        vec![Section::mapped(".text", 0x401_000, 0, 0x1000, false, true)],
    );
    p.format = BinaryFormat::Elf;
    let a = Analysis::compute(&p);
    let text = decompile(&p, &a, &Overlay::default(), 0x401_000).unwrap_or_default();
    assert!(!text.contains(">> 32"), "{text}");
}
