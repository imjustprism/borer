//! The x87 stack and SSE floats of 32-bit code.

use super::*;

/// `fld a; fld b; fcomi st1; fcmovb st1; fstp st1` is `max(a, b)`.
///
/// The compare sets the flags, the conditional move selects on them, and no
/// x87 instruction is left as asm. `fcmovb` moves on below or unordered,
/// so the select tests `!(b >= a)`, which a NaN satisfies, never `b < a`,
/// which it does not.
#[test]
fn x87_compare_and_conditional_move_select() {
    let text = dc(&[
        0xdd, 0x44, 0x24, 0x04, 0xdd, 0x44, 0x24, 0x0c, 0xdb, 0xf1, 0xda, 0xc1, 0xdd, 0xd9, 0xdd,
        0x19, 0xc3,
    ]);
    assert!(!text.contains("/* asm"), "{text}");
    assert!(text.contains(" ? "), "{text}");
    assert!(
        text.contains("!isgreaterequal(") || text.contains(" >= "),
        "{text}"
    );
    assert!(!text.contains(" < "), "{text}");
    assert!(text.contains("*(double*)"), "{text}");
}

/// A 32-bit function whose exits all leave a double in `xmm0`, which its
/// caller reads, returns it there.
///
/// `test ecx,ecx; je L; movsd xmm0,[0x402000]; ret; L: xorps xmm0,xmm0;
/// ret`, called by `call 0x401040; movsd [0x402010],xmm0; ret`: the
/// convention a whole-program compiler gives such a function. The text
/// read it as returning nothing, `void` and two bare `return;`s, while
/// its caller assigned `xmm0` from the call.
#[test]
fn a_32_bit_double_returned_in_xmm0_is_its_result() {
    let mut code = vec![
        0xe8, 0x3b, 0x00, 0x00, 0x00, // ASM: call 0x401040
        0xf2, 0x0f, 0x11, 0x05, 0x10, 0x20, 0x40, 0x00, // ASM: movsd [0x402010], xmm0
        0xc3, // ASM: ret
    ];
    code.resize(0x40, 0xcc);
    code.extend_from_slice(&[
        0x85, 0xc9, // ASM: test ecx, ecx
        0x74, 0x09, // ASM: je 0x40104d
        0xf2, 0x0f, 0x10, 0x05, 0x00, 0x20, 0x40, 0x00, // ASM: movsd xmm0, [0x402000]
        0xc3, // ASM: ret
        0x0f, 0x57, 0xc0, // ASM: xorps xmm0, xmm0
        0xc3, // ASM: ret
    ]);
    let p = image_with_data(&code, &2.5f64.to_bits().to_le_bytes());
    let text = decompiled(&p, 0x401040);
    assert!(text.contains("// signature: double sub_401040("), "{text}");
    assert!(!text.contains("return;"), "{text}");
    assert!(text.contains("return 0;"), "{text}");
}

#[test]
fn global_singleton_receivers_resolve_their_calls() {
    let mut code = vec![
        0xc7, 0x01, 0x18, 0x20, 0x40, 0x00, // ASM: mov dword [ecx],0x402018
        0x89, 0x0d, 0xe0, 0x20, 0x40, 0x00, // ASM: mov dword [0x4020e0],ecx
        0xc3, // ASM: ret
    ];
    code.resize(0x10, 0xcc);
    code.extend_from_slice(&[0xb8, 0x01, 0x00, 0x00, 0x00, 0xc3]);
    code.resize(0x20, 0xcc);
    code.extend_from_slice(&[0xb8, 0x02, 0x00, 0x00, 0x00, 0xc3]);
    code.resize(0x30, 0xcc);
    code.extend_from_slice(&[
        0x8b, 0x0d, 0xe0, 0x20, 0x40, 0x00, 0x8b, 0x01, 0xff, 0x50, 0x04, 0xc3,
    ]);
    code.resize(0x40, 0xcc);
    code.extend_from_slice(&[
        0x8b, 0x0d, 0xe4, 0x20, 0x40, 0x00, 0x8b, 0x01, 0xff, 0x50, 0x04, 0xc3,
    ]);
    let le = |v: u32| v.to_le_bytes();
    let mut data = vec![0u8; 0x100];
    let put = |data: &mut Vec<u8>, at: usize, bytes: &[u8]| {
        data[at..at + bytes.len()].copy_from_slice(bytes);
    };
    for (k, v) in [0u32, 0, 0, 0x402040, 0x402070].into_iter().enumerate() {
        put(&mut data, k * 4, &le(v));
    }
    put(&mut data, 0x14, &le(0x402000));
    put(&mut data, 0x18, &le(0x401010));
    put(&mut data, 0x1c, &le(0x401020));
    put(&mut data, 0x48, b".?AVG2@@\0");
    let p = image_with_data(&code, &data);
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    assert_eq!(
        a.classes.by_name.get("G2").map(|c| c.vtable),
        Some(Some(0x402018))
    );
    let gu2 = decompile(&p, &a, &o, 0x401030).unwrap_or_default();
    assert!(gu2.contains("g32_4020e0->vfunc_1("), "{gu2}");
    assert!(!gu2.contains("->vtable["), "{gu2}");
    assert_eq!(
        borer_engine::analysis::decompile::virtual_callees(&p, &a, &o, 0x401030),
        vec![0x401020]
    );
    let gu3 = decompile(&p, &a, &o, 0x401040).unwrap_or_default();
    assert!(gu3.contains("g32_4020e4->vtable[1]()"), "{gu3}");
}

/// A low-lane move says it merged, rather than claiming the register.
///
/// `movlpd xmm0,[esp]` carries sixty-four bits into the low lane and leaves
/// the high lane as it was. Read as a whole-register write it would claim
/// what the instruction did not do, which is the mistake `movss` between
/// registers is already spelled as a merge to avoid. Storing the low lane
/// writes exactly the sixty-four bits the destination holds, so that half is
/// a plain store.
#[test]
fn a_low_lane_move_merges_rather_than_claiming_the_register() {
    let text = dc(&[
        0x8b, 0x44, 0x24, 0x04, 0x66, 0x0f, 0x12, 0x44, 0x24, 0x08, 0x66, 0x0f, 0x13, 0x00, 0xc3,
    ]);
    assert!(
        !text.contains("/* asm"),
        "the low-lane move was left unmodeled: {text}"
    );
    assert!(
        text.contains("movlpd("),
        "the load claimed the whole register rather than merging: {text}"
    );
}

/// The high-lane form names the instruction that merged, so a reader can see
/// that only half the register moved.
#[test]
fn a_high_lane_move_names_itself_rather_than_assigning() {
    let text = dc(&[
        0x8b, 0x44, 0x24, 0x04, 0x66, 0x0f, 0x16, 0x44, 0x24, 0x08, 0x66, 0x0f, 0x13, 0x00, 0xc3,
    ]);
    assert!(
        text.contains("movhpd("),
        "the high-lane move read as a whole-register assignment: {text}"
    );
}

/// x87 arithmetic lifts against a register stack: a load pushes, a
/// store with `p` pops, and the expression comes out whole.
///
/// `mov eax,[esp+4]; fld dword [eax]; fmul dword [eax+4]; fstp dword
/// [eax+8]; ret`, then `fild dword [eax]; fistp dword [eax+4]`.
#[test]
fn x87_arithmetic_lifts_through_the_register_stack() {
    let text = dc(&[
        0x8b, 0x44, 0x24, 0x04, 0xd9, 0x00, 0xd8, 0x48, 0x04, 0xd9, 0x58, 0x08, 0xc3,
    ]);
    assert!(!text.contains("/* asm"), "{text}");
    assert!(
        text.contains("a1->field_0x8 = (double)a1->field_0x0 * (double)a1->field_0x4;"),
        "{text}"
    );
    assert!(
        text.contains("layout a1: 0x0 f32, 0x4 f32, 0x8 f32"),
        "{text}"
    );
    let text = dc(&[0x8b, 0x44, 0x24, 0x04, 0xdb, 0x00, 0xdb, 0x58, 0x04, 0xc3]);
    assert!(!text.contains("/* asm"), "{text}");
    assert!(text.contains("(double)"), "{text}");
}

/// `ucomiss; lahf; test ah, mask; jp` reads the float compare's outcome.
///
/// `test ah, 0x44; jp` is the floating-point equality the compare made, and
/// `test ah, 5` with the parity is the order: less alone, which no NaN
/// satisfies, so `a2 > a1` (spelled with the C99 macro when the operands do
/// not read as floats), never the flags' below.
///
/// `movss xmm0,[esp+4]; ucomiss xmm0,[esp+8]; lahf; test ah,mask; jp L;
/// mov eax,1; ret; L: xor eax,eax; ret` with masks 0x44 and 5.
#[test]
fn lahf_after_a_float_compare_is_the_comparison() {
    let compare = |mask: u8| {
        dc(&[
            0xf3, 0x0f, 0x10, 0x44, 0x24, 0x04, 0x0f, 0x2e, 0x44, 0x24, 0x08, 0x9f, 0xf6, 0xc4,
            mask, 0x7a, 0x06, 0xb8, 0x01, 0x00, 0x00, 0x00, 0xc3, 0x33, 0xc0, 0xc3,
        ])
    };
    let equal = compare(0x44);
    assert!(!equal.contains("asm"), "{equal}");
    assert!(!equal.contains("/*"), "{equal}");
    assert!(equal.contains(" == ") || equal.contains(" != "), "{equal}");
    let below = compare(0x05);
    assert!(!below.contains("asm"), "{below}");
    assert!(
        below.contains("isgreater(a2, a1)") || below.contains(" < "),
        "{below}"
    );
    assert!(!below.contains("isgreaterequal"), "{below}");
}

/// `sahf` puts back the flags `lahf` saved from a floating-point compare.
///
/// `movss xmm0,[esp+4]; ucomiss xmm0,[esp+8]; lahf; mov ecx,5; sahf;
/// ja L; mov eax,1; ret; L: xor eax,eax; ret`. The operands read as stack
/// arguments, so the comparison is the C99 `isgreater`, which a text pass
/// negates as a whole rather than flipping it to an ordered `<=`.
#[test]
fn sahf_restores_the_flags_lahf_saved() {
    let text = dc(&[
        0xf3, 0x0f, 0x10, 0x44, 0x24, 0x04, 0x0f, 0x2e, 0x44, 0x24, 0x08, 0x9f, 0xb9, 0x05, 0x00,
        0x00, 0x00, 0x9e, 0x77, 0x06, 0xb8, 0x01, 0x00, 0x00, 0x00, 0xc3, 0x33, 0xc0, 0xc3,
    ]);
    assert!(!text.contains("asm"), "{text}");
    assert!(!text.contains("FLAGS_UNKNOWN"), "{text}");
    assert!(
        text.contains("isgreater(a1, a2)") || text.contains(" > "),
        "{text}"
    );
    assert!(!text.contains(" <= "), "{text}");
}

/// `movss xmm0, [esp+4]; comiss xmm0, [-1.0]; jb` jumps on below or
/// unordered, so a NaN takes it: `!(a1 >= -1.0f)`, which a NaN satisfies,
/// never `a1 < -1.0f`, which it does not.
///
/// `movss xmm0,[esp+4]; comiss xmm0,[0x402000]; jb L; xor eax,eax; ret;
/// L: mov eax,1; ret` with -1.0f at 0x402000.
#[test]
fn comiss_then_jb_holds_on_nan() {
    let text = dc_data(
        &[
            0xf3, 0x0f, 0x10, 0x44, 0x24, 0x04, 0x0f, 0x2f, 0x05, 0x00, 0x20, 0x40, 0x00, 0x72,
            0x03, 0x33, 0xc0, 0xc3, 0xb8, 0x01, 0x00, 0x00, 0x00, 0xc3,
        ],
        &(-1.0f32).to_le_bytes(),
        &[],
    );
    assert!(text.contains("if (!(a1 >= -1.0f)) {"), "{text}");
    assert!(!text.contains("< -1.0f"), "{text}");
    for x in [f32::NAN, -2.0, -1.0, 0.0, f32::INFINITY, f32::NEG_INFINITY] {
        let jb = x.is_nan() || x < -1.0;
        assert_eq!(
            matches!(x.partial_cmp(&-1.0), None | Some(std::cmp::Ordering::Less)),
            jb,
            "a1 = {x}"
        );
    }
}

/// A push onto the x87 stack moves the registers' text variables down.
///
/// After a join wrote `st0`, `fld1; faddp st1, st0` adds 1.0 to that
/// `st0`, never to a `st1` nothing assigned, and the registers are
/// declared as the floats they hold.
///
/// `fld qword [esp+4]; test ecx,ecx; je +2; fchs; fld1; faddp st1,st0;
/// fstp qword [edx]; ret`.
#[test]
fn an_x87_push_renames_the_stack() {
    let text = dc(&[
        0xdd, 0x44, 0x24, 0x04, 0x85, 0xc9, 0x74, 0x02, 0xd9, 0xe0, 0xd9, 0xe8, 0xde, 0xc1, 0xdd,
        0x1a, 0xc3,
    ]);
    assert!(text.contains("*(double*)a2 = st0 + 1.0;"), "{text}");
    assert!(text.contains("double st0"), "{text}");
    assert!(!text.contains("uint32_t st0"), "{text}");
}

/// `fxch` swaps `st0` with the register it names: iced lists `st0` as its
/// first operand and the other register second, even for the bare form.
///
/// `mov eax,[esp+4]; fld qword [eax]; fld qword [eax+8]; fxch st1; fstp
/// qword [eax+0x10]; fstp qword [eax+0x18]; ret` stores the first double at
/// 0x10 and the second at 0x18.
#[test]
fn fxch_swaps_st0_with_the_register_it_names() {
    let text = dc(&[
        0x8b, 0x44, 0x24, 0x04, 0xdd, 0x00, 0xdd, 0x40, 0x08, 0xd9, 0xc9, 0xdd, 0x58, 0x10, 0xdd,
        0x58, 0x18, 0xc3,
    ]);
    assert!(text.contains("a1->field_0x10 = a1->field_0x0;"), "{text}");
    assert!(text.contains("st0 = a1->field_0x8;"), "{text}");
    assert!(text.contains("a1->field_0x18 = st0;"), "{text}");
}

/// A swap of two x87 registers that read each other parks one in a
/// `double`, which holds the float whole, never in a truncating integer.
///
/// `fxch` of the two values a function was entered with, kept across a
/// loop, writes the cycle out through a temporary: `fxch; L: fprem; fnstsw
/// ax; sahf; jp L; fstp st1; ret`, the shape of the C runtime's `fmod`
/// helper.
#[test]
fn an_x87_swap_parks_a_double() {
    let text = dc(&[
        0xd9, 0xc9, 0xd9, 0xf8, 0xdf, 0xe0, 0x9e, 0x7a, 0xf9, 0xdd, 0xd9, 0xc3,
    ]);
    assert!(text.contains("st1 = st0;"), "{text}");
    assert!(!text.contains("uint32_t tmp"), "{text}");
}

/// `fxch` swaps `st0` with the register it names in the lifter and the
/// emulator alike.
///
/// Both once took the decoder's first operand, `st0` itself, and agreed on
/// a no-op; d3dx9's 0x1002a72d stores what the swap brought up.
#[test]
fn fxch_agrees_with_the_emulator() {
    agrees_with_the_emulator(&[
        0x8b, 0x44, 0x24, 0x04, // ASM: mov eax,[esp+4]
        0xdd, 0x00, // ASM: fld qword [eax]
        0xdd, 0x40, 0x08, // ASM: fld qword [eax+8]
        0xdd, 0x40, 0x10, // ASM: fld qword [eax+0x10]
        0xd9, 0xca, // ASM: fxch st2
        0xdd, 0x58, 0x18, // ASM: fstp qword [eax+0x18]
        0xd9, 0xc9, // ASM: fxch
        0xdd, 0x58, 0x20, // ASM: fstp qword [eax+0x20]
        0xdd, 0x58, 0x28, // ASM: fstp qword [eax+0x28]
        0xc3, // ASM: ret
    ]);
}

/// A value kept on the x87 stack across a loop is read under the name it
/// was written to: a push moves only the registers that hold something,
/// so no text reads a deeper register nothing loaded.
///
/// The shape of d3dx9's 0x100265d3: `mov eax,[esp+4]; fld qword [esp+8];
/// L: test eax,eax; je D; fld qword [eax+8]; fsub st0,st1; fstp qword
/// [eax+8]; fadd qword [eax+0x10]; mov eax,[eax+0x30]; jmp L; D: fstp
/// st0; ret` subtracts a running sum from every node of a list. Once the
/// text named the loop's copies `st1 = st0; ... st0 = st1; st1 = st2;`,
/// and `st2` was never assigned.
#[test]
fn a_value_kept_on_the_x87_stack_is_read_where_it_was_written() {
    let text = dc(&[
        0x8b, 0x44, 0x24, 0x04, 0xdd, 0x44, 0x24, 0x08, 0x85, 0xc0, 0x74, 0x10, 0xdd, 0x40, 0x08,
        0xd8, 0xe1, 0xdd, 0x58, 0x08, 0xdc, 0x40, 0x10, 0x8b, 0x40, 0x30, 0xeb, 0xec, 0xdd, 0xd8,
        0xc3,
    ]);
    assert!(text.contains("*(double*)(var1 + 8)"), "{text}");
    assert_st_written(&text);
}

/// A float a call leaves in `st0` is the call's result.
///
/// The store after a call through a vtable reads it as such, never a `st0`
/// no statement assigned: d3dx9's 0x100265d3 stores what its virtual call
/// returns.
///
/// `mov ecx,[esp+4]; mov eax,[ecx]; call [eax+0x14]; mov eax,[esp+4];
/// fstp dword [eax+8]; ret`.
#[test]
fn a_call_leaves_its_float_in_st0() {
    let text = dc(&[
        0x8b, 0x4c, 0x24, 0x04, // ASM: mov ecx,[esp+4]
        0x8b, 0x01, // ASM: mov eax,[ecx]
        0xff, 0x50, 0x14, // ASM: call [eax+0x14]
        0x8b, 0x44, 0x24, 0x04, // ASM: mov eax,[esp+4]
        0xd9, 0x58, 0x08, // ASM: fstp dword [eax+8]
        0xc3, // ASM: ret
    ]);
    assert!(text.contains("st0 = (a1)->vtable[5]("), "{text}");
    assert_st_written(&text);
}

/// A 32-bit function returns the float it leaves on the x87 stack, and a
/// call to it leaves that float in `st0`.
///
/// `sub_401020` is `fld dword [ecx+4]; ret`; the caller is `mov ecx,
/// [esp+4]; call sub_401020; mov eax,[esp+4]; fstp dword [eax+8]; ret`.
/// The value it hands back is a single, so it returns `float`.
#[test]
fn a_function_returns_its_float_in_st0() {
    let mut code = vec![
        0x8b, 0x4c, 0x24, 0x04, // ASM: mov ecx,[esp+4]
        0xe8, 0x17, 0x00, 0x00, 0x00, // ASM: call 0x401020
        0x8b, 0x44, 0x24, 0x04, // ASM: mov eax,[esp+4]
        0xd9, 0x58, 0x08, // ASM: fstp dword [eax+8]
        0xc3, // ASM: ret
    ];
    code.resize(0x20, 0xcc);
    code.extend([
        0xd9, 0x41, 0x04, // ASM: fld dword [ecx+4]
        0xc3, // ASM: ret
    ]);
    let p = image(&code);
    let callee = decompiled(&p, 0x401020);
    assert!(callee.contains("float sub_401020("), "{callee}");
    assert!(callee.contains("return *(float*)(this + 4);"), "{callee}");
    let caller = decompiled(&p, 0x401000);
    assert!(caller.contains("st0 = sub_401020("), "{caller}");
    assert_st_written(&caller);
}

/// A value kept on the x87 stack across a call to a callee that runs no
/// x87 instruction is still there after it, never the call's result.
///
/// A compiler that sees the whole program keeps a `1.0` on the stack
/// across `sub_401020`, forty `inc ecx` and a call to `mov eax,ecx; ret`:
/// the caller is `fld1; call sub_401020; mov eax,[esp+4]; fstp dword
/// [eax]; ret`, and d3dx9's 0x10138070 keeps a `0.0` across a string
/// compare the same way.
#[test]
fn an_x87_value_outlives_a_call_that_leaves_the_stack_alone() {
    let mut code = vec![
        0xd9, 0xe8, // ASM: fld1
        0xe8, 0x19, 0x00, 0x00, 0x00, // ASM: call 0x401020
        0x8b, 0x44, 0x24, 0x04, // ASM: mov eax,[esp+4]
        0xd9, 0x18, // ASM: fstp dword [eax]
        0xc3, // ASM: ret
    ];
    code.resize(0x20, 0xcc);
    code.resize(0x48, 0x41); // ASM: inc ecx, forty times
    code.extend([
        0xe8, 0x33, 0x00, 0x00, 0x00, // ASM: call 0x401080
        0xc3, // ASM: ret
    ]);
    code.resize(0x80, 0xcc);
    code.extend([
        0x89, 0xc8, // ASM: mov eax,ecx
        0xc3, // ASM: ret
    ]);
    let text = decompiled(&image(&code), 0x401000);
    assert!(text.contains("*(float*)a2 = 1.0f;"), "{text}");
    assert!(!text.contains("st0 = sub_401020"), "{text}");
}

/// A 32-bit callee hands a float back in `xmm0` only when it is known to:
/// its body leaves one there, and the float it takes there is its
/// argument.
///
/// `sub_401020` is `sqrtsd xmm0,xmm0; ret`; the caller is `movsd xmm0,
/// [esp+4]; call sub_401020; mov eax,[esp+12]; movsd [eax],xmm0; ret`.
#[test]
fn a_32_bit_callee_returning_in_xmm0_binds_it() {
    let mut code = vec![
        0xf2, 0x0f, 0x10, 0x44, 0x24, 0x04, // ASM: movsd xmm0,[esp+4]
        0xe8, 0x15, 0x00, 0x00, 0x00, // ASM: call 0x401020
        0x8b, 0x44, 0x24, 0x0c, // ASM: mov eax,[esp+12]
        0xf2, 0x0f, 0x11, 0x00, // ASM: movsd [eax],xmm0
        0xc3, // ASM: ret
    ];
    code.resize(0x20, 0xcc);
    code.extend([
        0xf2, 0x0f, 0x51, 0xc0, // ASM: sqrtsd xmm0,xmm0
        0xc3, // ASM: ret
    ]);
    let text = dc(&code);
    assert!(text.contains("var1 = sub_401020(a1);"), "{text}");
    assert!(text.contains("*(double*)a3 = var1;"), "{text}");
}

/// A 32-bit call clobbers the vector registers.
///
/// A callee that hands no float back in `xmm0` binds none there: the read
/// after it is of a register the convention leaves undefined, never the
/// call's result.
///
/// `sub_401020` is `push esi; call sub_401040; pop esi; ret`, and
/// `sub_401040` clears `xmm0` (a callee whose callees leave a vector
/// register alone hands it back as it found it); the caller is that of
/// [`a_32_bit_callee_returning_in_xmm0_binds_it`].
#[test]
fn a_32_bit_call_binds_no_xmm0_it_does_not_return() {
    let mut code = vec![
        0xf2, 0x0f, 0x10, 0x44, 0x24, 0x04, // ASM: movsd xmm0,[esp+4]
        0xe8, 0x15, 0x00, 0x00, 0x00, // ASM: call 0x401020
        0x8b, 0x44, 0x24, 0x0c, // ASM: mov eax,[esp+12]
        0xf2, 0x0f, 0x11, 0x00, // ASM: movsd [eax],xmm0
        0xc3, // ASM: ret
    ];
    code.resize(0x20, 0xcc);
    code.extend([
        0x56, // ASM: push esi
        0xe8, 0x1a, 0x00, 0x00, 0x00, // ASM: call 0x401040
        0x5e, // ASM: pop esi
        0xc3, // ASM: ret
    ]);
    code.resize(0x40, 0xcc);
    code.extend([0x0f, 0x57, 0xc0]); // ASM: xorps xmm0,xmm0
    code.push(0xc3); // ASM: ret
    let text = dc(&code);
    assert!(!text.contains("xmm0 = sub_401020"), "{text}");
    assert!(!text.contains("*(double*)a3 = a1;"), "{text}");
}

/// The C runtime's SSE2 helpers take their doubles in `xmm0` and `xmm1`.
///
/// They return in `xmm0`, and are known by name through an import:
/// `movsd xmm0,[esp+4]; movsd xmm1,[esp+12]; call [__libm_sse2_pow]; mov
/// eax,[esp+20]; movsd [eax],xmm0; ret` stores the power.
#[test]
fn an_sse2_helper_takes_and_returns_its_doubles_in_vector_registers() {
    let code = [
        0xf2, 0x0f, 0x10, 0x44, 0x24, 0x04, // ASM: movsd xmm0,[esp+4]
        0xf2, 0x0f, 0x10, 0x4c, 0x24, 0x0c, // ASM: movsd xmm1,[esp+12]
        0xff, 0x15, 0x00, 0x20, 0x40, 0x00, // ASM: call [0x402000]
        0x8b, 0x44, 0x24, 0x14, // ASM: mov eax,[esp+20]
        0xf2, 0x0f, 0x11, 0x00, // ASM: movsd [eax],xmm0
        0xc3, // ASM: ret
    ];
    let text = dc_with(&code, &[(0x402000, "msvcrt.dll!__libm_sse2_pow")]);
    assert!(text.contains("var1 = __libm_sse2_pow(a1, a3);"), "{text}");
    assert!(text.contains("*(double*)a5 = var1;"), "{text}");
}

/// `fsincos`, `fptan` and `frndint` lift to the sine and cosine, the
/// tangent and its 1.0, and `rint`, and the lifter and the emulator agree
/// on the block.
///
/// `mov eax,[esp+4]; fld qword [eax]; fsincos; fstp qword [eax+8]; fstp
/// qword [eax+16]; fld qword [eax]; fptan; fstp st0; fstp qword [eax+24];
/// fld qword [eax]; frndint; fstp qword [eax+32]; ret`.
#[test]
fn the_x87_transcendentals_lift() {
    let code = [
        0x8b, 0x44, 0x24, 0x04, // ASM: mov eax,[esp+4]
        0xdd, 0x00, // ASM: fld qword [eax]
        0xd9, 0xfb, // ASM: fsincos
        0xdd, 0x58, 0x08, // ASM: fstp qword [eax+8]
        0xdd, 0x58, 0x10, // ASM: fstp qword [eax+16]
        0xdd, 0x00, // ASM: fld qword [eax]
        0xd9, 0xf2, // ASM: fptan
        0xdd, 0xd8, // ASM: fstp st0
        0xdd, 0x58, 0x18, // ASM: fstp qword [eax+24]
        0xdd, 0x00, // ASM: fld qword [eax]
        0xd9, 0xfc, // ASM: frndint
        0xdd, 0x58, 0x20, // ASM: fstp qword [eax+32]
        0xc3, // ASM: ret
    ];
    let text = dc(&code);
    assert!(
        text.contains("a1->field_0x8 = cos(a1->field_0x0);"),
        "{text}"
    );
    assert!(text.contains("st0 = sin(a1->field_0x0);"), "{text}");
    assert!(text.contains("a1->field_0x10 = st0;"), "{text}");
    assert!(
        text.contains("a1->field_0x18 = tan(a1->field_0x0);"),
        "{text}"
    );
    assert!(
        text.contains("a1->field_0x20 = rint(a1->field_0x0);"),
        "{text}"
    );
    assert!(!text.contains("asm"), "{text}");
    agrees_with_the_emulator(&code);
}

/// An x87 helper takes its operands off the stack and leaves its result.
///
/// The operands are its arguments in the order they were pushed: `_CIpow`
/// raises the first to the second, and the store after it stores the
/// power, never the exponent left behind.
///
/// `fld dword [esp+4]; fld dword [esp+8]; call _CIpow; mov eax,[esp+12];
/// fstp dword [eax]; ret`.
#[test]
fn an_x87_helper_takes_its_operands_off_the_stack() {
    let mut code = vec![
        0xd9, 0x44, 0x24, 0x04, // ASM: fld dword [esp+4]
        0xd9, 0x44, 0x24, 0x08, // ASM: fld dword [esp+8]
        0xe8, 0x13, 0x00, 0x00, 0x00, // ASM: call 0x401020
        0x8b, 0x44, 0x24, 0x0c, // ASM: mov eax,[esp+12]
        0xd9, 0x18, // ASM: fstp dword [eax]
        0xc3, // ASM: ret
    ];
    code.resize(0x20, 0xcc);
    code.push(0xc3); // ASM: ret
    let text = dc_data(&code, &[], &[(0x401020, "_CIpow")]);
    assert!(text.contains("st0 = _CIpow(a1, a2);"), "{text}");
    assert!(text.contains("*(float*)a3 = st0;"), "{text}");
}

/// A callee whose body pops the x87 value it was handed on every path
/// takes it as its argument, as the C runtime's `_ftol` does, named or not.
///
/// `sub_401020` is `fistp dword [esp-4]; mov eax,[esp-4]; ret`; the caller
/// is `fld dword [esp+4]; call sub_401020; fld dword [esp+8]; fstp dword
/// [eax]; ret`, which converts its first argument and stores its second
/// through the result.
#[test]
fn a_callee_popping_the_x87_stack_takes_its_operand() {
    let mut code = vec![
        0xd9, 0x44, 0x24, 0x04, // ASM: fld dword [esp+4]
        0xe8, 0x17, 0x00, 0x00, 0x00, // ASM: call 0x401020
        0xd9, 0x44, 0x24, 0x08, // ASM: fld dword [esp+8]
        0xd9, 0x18, // ASM: fstp dword [eax]
        0xc3, // ASM: ret
    ];
    code.resize(0x20, 0xcc);
    code.extend([
        0xdb, 0x5c, 0x24, 0xfc, // ASM: fistp dword [esp-4]
        0x8b, 0x44, 0x24, 0xfc, // ASM: mov eax,[esp-4]
        0xc3, // ASM: ret
    ]);
    let text = decompiled(&image(&code), 0x401000);
    assert!(text.contains("var1 = sub_401020(a1);"), "{text}");
    assert!(text.contains("*(float*)var1 = a2;"), "{text}");
}

/// A ten-byte x87 store keeps all ten bytes: it is a call on the value,
/// not an eight-byte integer store that drops two.
///
/// `mov ecx,[esp+4]; fld tword [esp+8]; fstp tword [ecx]; ret`.
#[test]
fn an_extended_x87_store_keeps_its_ten_bytes() {
    let text = dc(&[
        0x8b, 0x4c, 0x24, 0x04, 0xdb, 0x6c, 0x24, 0x08, 0xdb, 0x39, 0xc3,
    ]);
    assert!(text.contains("x87_store80(a1, st0);"), "{text}");
    assert!(!text.contains("*(uint64_t*)a1"), "{text}");
}

/// `fstp dword [esp+4]` stores the x87 value rounded to single precision.
///
/// A `movsd` that copies the slot as a dword then copies the single's bits:
/// `1.0f`, never the slot's unassigned variable or the low half of the
/// double.
///
/// `sub esp,0x10; fld1; fstp dword [esp+4]; lea esi,[esp+4]; mov
/// edi,0x402000; movsd; add esp,0x10; ret`.
#[test]
fn a_single_stored_from_x87_copies_as_its_bits() {
    let text = dc(&[
        0x83, 0xec, 0x10, 0xd9, 0xe8, 0xd9, 0x5c, 0x24, 0x04, 0x8d, 0x74, 0x24, 0x04, 0xbf, 0x00,
        0x20, 0x40, 0x00, 0xa5, 0x83, 0xc4, 0x10, 0xc3,
    ]);
    assert!(text.contains("g32_402000 = 1.0f;"), "{text}");
    assert!(text.contains("float g32_402000;"), "{text}");
    assert!(!text.contains("= local_"), "{text}");
}

/// A vector store's value keeps the register it read when the store
/// writes that register's reload out first.
///
/// `movaps xmm1,[rdx]; movaps [rcx+0x20],xmm2; sqrtps xmm0,xmm1; movaps
/// xmm1,[rdx+0x10]; movss [rcx],xmm0; movaps [rcx+0x10],xmm1; ret`: the
/// store of `xmm0` writes the reload of `xmm1` out before it, and the
/// square root stored is of the `xmm1` the binary read before the reload
/// (a real game client printed `*(this + 0x80) = sqrtps(xmm1) *
/// 0.5f` after `xmm1` was reassigned).
#[test]
fn a_vector_store_keeps_the_register_its_value_read() {
    let p = raw::image(
        Arch::X86_64,
        &[
            0x0f, 0x28, 0x0a, // ASM: movaps xmm1, [rdx]
            0x0f, 0x29, 0x51, 0x20, // ASM: movaps [rcx+0x20], xmm2
            0x0f, 0x51, 0xc1, // ASM: sqrtps xmm0, xmm1
            0x0f, 0x28, 0x4a, 0x10, // ASM: movaps xmm1, [rdx+0x10]
            0xf3, 0x0f, 0x11, 0x01, // ASM: movss [rcx], xmm0
            0x0f, 0x29, 0x49, 0x10, // ASM: movaps [rcx+0x10], xmm1
            0xc3, // ASM: ret
        ],
        &[],
    );
    let text = decompiled(&p, 0x401000);
    let reload = text
        .find("var3 = *(uint128_t*)(a2 + 0x10);")
        .expect("the reload is written out");
    let sqrt = text
        .find("sqrtps(var1)")
        .expect("the square root is printed");
    assert!(sqrt < reload, "{text}");
    assert_eq!(text.matches("sqrtps(").count(), 1, "{text}");
}

/// A stack parameter read as floating point is typed so.
///
/// `fld dword [ebp+0xc]` returns the second of three arguments widened
/// from a `float`, where the header said `uint32_t a2` (d3dx9's
/// 0x101a3ab8). `fld qword [ebp+8]` reads a `double`, whose high half is
/// the next word: no caller passes that word on its own, so the header
/// lists one parameter.
#[test]
fn a_stack_parameter_loaded_as_floating_point_is_typed_so() {
    let float = dc(&[
        0x55, 0x8b, 0xec, // ASM: push ebp; mov ebp,esp
        0xd9, 0x45, 0x0c, // ASM: fld dword [ebp+0xc]
        0x5d, 0xc2, 0x0c, 0x00, // ASM: pop ebp; ret 0xc
    ]);
    assert!(float.contains("float a2"), "{float}");
    let double = dc(&[
        0x55, 0x8b, 0xec, // ASM: push ebp; mov ebp,esp
        0xdd, 0x45, 0x08, // ASM: fld qword [ebp+8]
        0xd8, 0xc0, // ASM: fadd st0,st0
        0x5d, 0xc2, 0x08, 0x00, // ASM: pop ebp; ret 8
    ]);
    let sig = double
        .lines()
        .find(|l| l.starts_with("// signature:"))
        .unwrap_or("");
    assert!(sig.ends_with("(double a1)"), "{double}");
}

/// A float compare's flags stay a float compare when the next block reads
/// them.
///
/// `mov eax,-1; ucomisd xmm1,xmm0; ja L; mov eax,1; ucomisd xmm0,xmm1; ja
/// L; cmpneqsd xmm0,xmm1; movq rax,xmm0; and eax,1; add eax,eax; L: ret`,
/// the three-way compare of two doubles. Each `ja` is an ordered greater
/// than: a NaN takes neither, so neither may read as `<=` of the other.
#[test]
fn a_float_compare_read_after_a_block_keeps_its_nan_order() {
    let text = dc64(&[
        0xb8, 0xff, 0xff, 0xff, 0xff, 0x66, 0x0f, 0x2e, 0xc8, 0x77, 0x1a, 0xb8, 0x01, 0x00, 0x00,
        0x00, 0x66, 0x0f, 0x2e, 0xc1, 0x77, 0x0f, 0xf2, 0x0f, 0xc2, 0xc1, 0x04, 0x66, 0x48, 0x0f,
        0x7e, 0xc0, 0x83, 0xe0, 0x01, 0x01, 0xc0, 0xc3,
    ]);
    assert!(!text.contains(" <= "), "{text}");
    assert!(!text.contains("parity"), "{text}");
    assert!(!text.contains("isgreater"), "{text}");
}

/// A float read back as an integer of its width is its bits, and the bits
/// of a float with the sign bit flipped, read back as the float, are its
/// negation.
///
/// `movss [rbp-4],xmm0; movss xmm0,[rbp-4]; movss [rbp-8],xmm0; mov
/// eax,[rbp-8]` returns the single's encoding, never the number converted.
/// `mulsd xmm0,xmm2; movq rax,xmm0; mov rcx,1<<63; xor rax,rcx; movq
/// xmm0,rax; addsd xmm0,xmm1` is `-(x * z) + y`.
#[test]
fn a_float_read_as_an_integer_is_its_bits() {
    let bits = dc64(&[
        0x55, 0x48, 0x89, 0xe5, 0xf3, 0x0f, 0x11, 0x45, 0xfc, 0xf3, 0x0f, 0x10, 0x45, 0xfc, 0xf3,
        0x0f, 0x11, 0x45, 0xf8, 0x8b, 0x45, 0xf8, 0x5d, 0xc3,
    ]);
    assert!(bits.contains("*(uint32_t*)&"), "{bits}");
    let negated = dc64(&[
        0xf2, 0x0f, 0x59, 0xc2, 0x66, 0x48, 0x0f, 0x7e, 0xc0, 0x48, 0xb9, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x80, 0x48, 0x31, 0xc8, 0x66, 0x48, 0x0f, 0x6e, 0xc0, 0xf2, 0x0f, 0x58,
        0xc1, 0xc3,
    ]);
    assert!(!negated.contains("0x8000000000000000"), "{negated}");
    assert!(negated.contains("-(a1 * a3)"), "{negated}");
}

/// A sum of floats keeps the grouping the instructions computed: float
/// addition is not associative.
///
/// `addsd xmm1,xmm2; addsd xmm0,xmm1; ret` is `a + (b + c)`, never
/// `a + b + c`, which C reads as `(a + b) + c`.
#[test]
fn a_float_sum_keeps_its_grouping() {
    let text = dc64(&[0xf2, 0x0f, 0x58, 0xca, 0xf2, 0x0f, 0x58, 0xc1, 0xc3]);
    assert!(text.contains(" + ("), "{text}");
}
