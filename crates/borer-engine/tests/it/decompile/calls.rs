//! Calls: arguments, parameters, arities and what a callee leaves alone.

use super::*;

/// A register whose dead load a store dropped is not passed by its stale
/// name to the jump the text reads as a tail call.
///
/// `mov rdx,[rcx+16]; mov [r8+32],rdx; mov rax,[rcx]; mov ecx,[r9]; jmp
/// rax`: the liveness sees no read of `rdx` at the indirect jump, so the
/// store dropped its pending load unwritten, and the tail call then named
/// `rdx`, whose text variable held an older value; the check of the text
/// disagreed on the argument, as on a jump through a table the corpus
/// binary's `build_blocks` takes.
///
/// # Panics
///
/// When the call passes `rdx` or the check disagrees.
#[test]
fn a_register_dropped_dead_is_not_passed_by_its_stale_name() {
    use borer_engine::analysis::decompile::checked_header;
    let code = [
        0x48, 0x8b, 0x51, 0x10, // ASM: mov rdx,[rcx+16]
        0x49, 0x89, 0x50, 0x20, // ASM: mov [r8+32],rdx
        0x48, 0x8b, 0x01, // ASM: mov rax,[rcx]
        0x41, 0x8b, 0x09, // ASM: mov ecx,[r9]
        0xff, 0xe0, // ASM: jmp rax
    ];
    let p = program64(&code);
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let text = decompile(&p, &a, &o, 0x1_4000_1000).unwrap_or_default();
    let header = checked_header(&p, &a, &o, 0x1_4000_1000).unwrap_or_default();
    assert!(!header.contains("disagree"), "{header}\n{text}");
    let call = text
        .lines()
        .find(|l| l.contains("return (*"))
        .unwrap_or_default();
    assert!(!call.contains("rdx"), "{text}");
}

/// A register written out under its own name, because its value is long
/// and read twice, is still the second argument of the call in the next
/// block.
///
/// `mov rdx,[rcx+r8*8+0x10]; mov r9,rdx; test rdx,rdx; je L; mov ecx,7;
/// call 0x140001040; L: ret`: the load is too long to inline for the two
/// reads its block makes, so `rdx = …` is written out before the test; the
/// callee, `mov rax,rdx; add rax,rcx; ret`, reads both argument registers,
/// and `rdx` is no parameter of the caller.
#[test]
fn a_register_written_out_before_the_call_is_still_its_argument() {
    use borer_engine::program::{Arch, BinaryFormat, Program, Section};
    let mut code = vec![
        0x4a, 0x8b, 0x54, 0xc1, 0x10, 0x4c, 0x8b, 0xca, 0x48, 0x85, 0xd2, 0x74, 0x0a, 0xb9, 0x07,
        0x00, 0x00, 0x00, 0xe8, 0x29, 0x00, 0x00, 0x00, 0xc3,
    ];
    code.resize(0x40, 0xcc);
    code.extend_from_slice(&[0x48, 0x8b, 0xc2, 0x48, 0x03, 0xc1, 0xc3]);
    let mut bytes = vec![0u8; 0x1000];
    bytes[..code.len()].copy_from_slice(&code);
    let mut p = Program::raw(
        bytes,
        Arch::X86_64,
        0x1_4000_0000,
        Some(0x1_4000_1000),
        vec![Section::mapped(
            ".text",
            0x1_4000_1000,
            0,
            0x1000,
            false,
            true,
        )],
    );
    p.format = BinaryFormat::Pe;
    let text = decompiled(&p, 0x1_4000_1000);
    assert!(
        text.contains("var1 = ((uint64_t*)(a1 + 0x10))[a3];"),
        "{text}"
    );
    assert!(text.contains("sub_140001040(7, var1)"), "{text}");
}

/// A PLT stub for a function the image defines itself takes that name.
///
/// A shared object calls its own exports through `jmp [slot]` stubs whose
/// GOT slot holds the export's address. `caller` calls such a stub for
/// `helper`, so the call reads `helper(...)`, not `sub_...`. The name still
/// resolves to the function's own body, not the stub.
#[test]
fn a_plt_stub_to_an_own_export_takes_its_name() {
    use borer_engine::analysis::resolve;
    use borer_engine::program::{Symbol, SymbolKind};
    let mut code = vec![0xcc_u8; 0x30];
    code[..4].copy_from_slice(&[
        0x8d, 0x41, 0x01, // ASM: lea eax,[rcx+1]
        0xc3, // ASM: ret
    ]);
    code[0x10..0x16].copy_from_slice(&[
        0xe8, 0x0b, 0x00, 0x00, 0x00, // ASM: call 0x20
        0xc3, // ASM: ret
    ]);
    code[0x20..0x26].copy_from_slice(&[
        0xff, 0x25, 0xda, 0x0f, 0x00, 0x00, // ASM: jmp [rip+0xfda]
    ]);
    let mut p = program64_with_data(&code, &0x1_4000_1000_u64.to_le_bytes());
    p.symbols = vec![
        Symbol {
            name: "helper".to_owned(),
            addr: 0x1_4000_1000,
            kind: SymbolKind::Export,
        },
        Symbol {
            name: "caller".to_owned(),
            addr: 0x1_4000_1010,
            kind: SymbolKind::Export,
        },
    ];
    let a = Analysis::compute(&p);
    let stub = a.function(0x1_4000_1020).and_then(|f| f.name.clone());
    assert_eq!(stub.as_deref(), Some("helper"));
    let text = decompile(&p, &a, &Overlay::default(), 0x1_4000_1010).unwrap_or_default();
    assert!(text.contains("helper("), "{text}");
    assert_eq!(
        resolve(&p, &a, &Overlay::default(), "helper"),
        Ok(0x1_4000_1000)
    );
}

/// A byte moved into an argument register right before a call is the
/// whole argument.
///
/// `mov r8b,1; mov edx,2; mov ecx,3; call 0x140001020; ret` passes `1`,
/// not a merge with what `r8` held; the callee is `movzx eax,r8b; ret`.
#[test]
fn a_byte_moved_into_an_argument_register_is_the_argument() {
    let mut code = vec![
        0x41, 0xb0, 0x01, 0xba, 0x02, 0x00, 0x00, 0x00, 0xb9, 0x03, 0x00, 0x00, 0x00, 0xe8, 0x0e,
        0x00, 0x00, 0x00, 0xc3,
    ];
    code.resize(0x20, 0xcc);
    code.extend_from_slice(&[0x41, 0x0f, 0xb6, 0xc0, 0xc3]);
    let p = program64(&code);
    let text = decompiled(&p, 0x1_4000_1000);
    assert!(text.contains("sub_140001020(3, 2, 1)"), "{text}");
}

/// An argument register read on a path no call precedes is a parameter,
/// though a call sits before the read in the image.
///
/// `test ecx,ecx; je L; call 0x140001020; ret; L: mov eax,[r8+8]; ret`
/// reads `r8` on the second path; the callee is `mov eax,1; ret`.
#[test]
fn a_register_read_on_a_call_free_path_is_a_parameter() {
    let mut code = vec![
        0x85, 0xc9, 0x74, 0x06, 0xe8, 0x17, 0x00, 0x00, 0x00, 0xc3, 0x41, 0x8b, 0x40, 0x08, 0xc3,
    ];
    code.resize(0x20, 0xcc);
    code.extend_from_slice(&[0xb8, 0x01, 0x00, 0x00, 0x00, 0xc3]);
    let p = program64(&code);
    let text = decompiled(&p, 0x1_4000_1000);
    assert!(text.contains("a3 + 8") || text.contains("a3->"), "{text}");
    assert!(!text.contains("r8"), "{text}");
}

/// A callee that homes its argument registers for `va_start` is
/// variadic.
///
/// A caller passes what it set past the fixed arguments and nothing by
/// name, forwards none of them as its own parameters, and the callee's
/// own signature ends in `...`.
///
/// The callee at 0x140001040 is `mov rax,rsp; mov [rax+8],rcx; mov
/// [rax+10h],rdx; mov [rax+18h],r8; mov [rax+20h],r9; lea rax,[rax+10h];
/// ret`; the entry sets `ecx` and `edx`, calls it, then calls the
/// function at 0x140001020, which sets only `ecx` before calling it.
#[test]
fn a_variadic_callee_takes_what_the_caller_set() {
    let mut code = vec![
        0xb9, 0x07, 0x00, 0x00, 0x00, 0xba, 0x08, 0x00, 0x00, 0x00, 0xe8, 0x31, 0x00, 0x00, 0x00,
        0xe8, 0x0c, 0x00, 0x00, 0x00, 0xc3,
    ];
    code.resize(0x20, 0xcc);
    code.extend_from_slice(&[
        0xb9, 0x07, 0x00, 0x00, 0x00, 0xe8, 0x16, 0x00, 0x00, 0x00, 0xc3,
    ]);
    code.resize(0x40, 0xcc);
    code.extend_from_slice(&[
        0x48, 0x8b, 0xc4, 0x48, 0x89, 0x48, 0x08, 0x48, 0x89, 0x50, 0x10, 0x4c, 0x89, 0x40, 0x18,
        0x4c, 0x89, 0x48, 0x20, 0x48, 0x8d, 0x40, 0x10, 0xc3,
    ]);
    let p = program64(&code);
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let both = decompile(&p, &a, &o, 0x1_4000_1000).unwrap_or_default();
    assert!(both.contains("sub_140001040(7, 8)"), "{both}");
    let one = decompile(&p, &a, &o, 0x1_4000_1020).unwrap_or_default();
    assert!(one.contains("sub_140001040(7)"), "{one}");
    assert!(!one.contains("rdx"), "{one}");
    assert!(one.contains("sub_140001020()"), "{one}");
    let callee = decompile(&p, &a, &o, 0x1_4000_1040).unwrap_or_default();
    assert!(
        callee.contains("sub_140001040(uint64_t a1, ...)"),
        "{callee}"
    );
}

/// A thunk that sets one argument register and jumps on forwards the
/// rest, so its caller passes them.
///
/// The entry is both the target and the caller: `cmp ecx,1; jne L; mov
/// eax,edx; add eax,ecx; ret; L: mov ecx,7; mov edx,5; call 0x140001020;
/// ret`, and the thunk is `mov ecx,1; jmp 0x140001000`.
#[test]
fn a_thunk_that_sets_a_register_forwards_the_rest() {
    let mut code = vec![
        0x83, 0xf9, 0x01, 0x75, 0x05, 0x8b, 0xc2, 0x03, 0xc1, 0xc3, 0xb9, 0x07, 0x00, 0x00, 0x00,
        0xba, 0x05, 0x00, 0x00, 0x00, 0xe8, 0x07, 0x00, 0x00, 0x00, 0xc3,
    ];
    code.resize(0x20, 0xcc);
    code.extend_from_slice(&[0xb9, 0x01, 0x00, 0x00, 0x00, 0xe9, 0xd6, 0xff, 0xff, 0xff]);
    let p = program64(&code);
    let text = decompiled(&p, 0x1_4000_1000);
    assert!(text.contains("sub_140001020(7, 5)"), "{text}");
}

/// A wrapper that sets every argument register and jumps to a variadic
/// function is not variadic itself: its caller passes nothing.
///
/// `mov ecx,7; mov edx,8; call 0x140001020; call 0x140001040; ret`
/// calls `mov ecx,1; mov edx,2; mov r8d,3; mov r9d,4; jmp 0x140001040`,
/// which lands in a function that homes its registers for `va_start`
/// (called directly too, so it is a function of its own).
#[test]
fn a_wrapper_that_sets_every_register_is_not_variadic() {
    let mut code = vec![
        0xb9, 0x07, 0x00, 0x00, 0x00, 0xba, 0x08, 0x00, 0x00, 0x00, 0xe8, 0x11, 0x00, 0x00, 0x00,
        0xe8, 0x2c, 0x00, 0x00, 0x00, 0xc3,
    ];
    code.resize(0x20, 0xcc);
    code.extend_from_slice(&[
        0xb9, 0x01, 0x00, 0x00, 0x00, 0xba, 0x02, 0x00, 0x00, 0x00, 0x41, 0xb8, 0x03, 0x00, 0x00,
        0x00, 0x41, 0xb9, 0x04, 0x00, 0x00, 0x00, 0xe9, 0x05, 0x00, 0x00, 0x00,
    ]);
    code.resize(0x40, 0xcc);
    code.extend_from_slice(&[
        0x48, 0x8b, 0xc4, 0x48, 0x89, 0x48, 0x08, 0x48, 0x89, 0x50, 0x10, 0x4c, 0x89, 0x40, 0x18,
        0x4c, 0x89, 0x48, 0x20, 0x48, 0x8d, 0x40, 0x10, 0xc3,
    ]);
    let p = program64(&code);
    let text = decompiled(&p, 0x1_4000_1000);
    assert!(text.contains("sub_140001020()"), "{text}");
}

/// The register a virtual call goes through is no argument.
///
/// `mov rax,rcx; mov r9d,edx; mov rcx,rax; mov r8,[rax]; call qword
/// [r8]; ret` calls through `a1`'s vtable, a slot nothing states the
/// arity of: the receiver goes first, `rdx` still holds the caller's own
/// `a2` and was not written for the call, and neither the vtable pointer
/// in `r8` nor the copy in `r9` is an argument.
#[test]
fn the_register_a_call_goes_through_is_no_argument() {
    let code = [
        0x48, 0x8b, 0xc1, 0x44, 0x8b, 0xca, 0x48, 0x8b, 0xc8, 0x4c, 0x8b, 0x00, 0x41, 0xff, 0x10,
        0xc3,
    ];
    let p = program64(&code);
    let text = decompiled(&p, 0x1_4000_1000);
    assert!(text.contains("a1->vtable[0]();"), "{text}");
}

/// `main` renders both calls, a conditional, the `xor eax,eax` zero idiom as
/// `return 0;`, and no goto to the fall-through block after cleanup.
#[test]
fn main_calls_condition_and_zero_idiom() {
    let out = dc(0x1000);
    assert!(out.contains("sub_1020();"), "missing call A:\n{out}");
    assert!(out.contains("sub_1030();"), "missing call B:\n{out}");
    assert!(out.contains("if ("), "no conditional:\n{out}");
    assert!(
        out.contains("return 0;"),
        "xor-zero idiom not folded:\n{out}"
    );
    assert!(
        !out.contains("goto L_1009;"),
        "fallthrough goto survived:\n{out}"
    );
}

/// `P`: the argument registers flow into the call as `Base::vfunc_1(10, 20);`
/// without redundant assignments, and the signature is `void`.
#[test]
fn call_arguments_rendered() {
    let out = dc(0x11c0);
    assert!(
        out.contains("Base::vfunc_1(10, 20);"),
        "call args missing:
{out}"
    );
    assert!(
        !out.contains("rcx = 10;"),
        "redundant arg assignment survived:
{out}"
    );
    assert!(
        !out.contains("rdx = 20;"),
        "redundant arg assignment survived:
{out}"
    );
    assert!(
        out.contains("// signature: uint64_t exported_p()")
            && out.contains("return Base::vfunc_1(10, 20);"),
        "P passes Q's result through (Q's result is read by another caller):
{out}"
    );
}

/// `test ecx,ecx; jz` renders as a plain zero test on `rcx` (read after a call,
/// so not a parameter), not as an `and`.
#[test]
fn test_same_register_simplifies() {
    let out = dc(0x1000);
    assert!(
        out.contains("rcx == 0") || out.contains("rcx != 0"),
        "test-same not simplified:
{out}"
    );
    assert!(
        !out.contains("& rcx"),
        "test-same rendered as an and:\n{out}"
    );
}

/// `X`: a function address and a string address passed as arguments render
/// as the function's name and the literal.
#[test]
fn function_pointer_and_string_arguments_are_named() {
    let out = dc(0x1250);
    assert!(
        out.contains("Base::vfunc_1(sub_10e0, \"hello, borer world\");"),
        "{out}"
    );
}

/// `AC`: the callee reads only its first argument register, so the call shows
/// one argument even though two were set up.
#[test]
fn call_arguments_stop_at_the_callee_arity() {
    let out = dc(0x13b0);
    assert!(out.contains("Glob::vfunc_1(1);"), "{out}");
    assert!(!out.contains("Glob::vfunc_1(1, 2)"), "{out}");
}

/// `D1`: the copy of the parameter into `rdi` stays symbolic across the call
/// (the parameter is `a2`, not the volatile register), so nothing is written
/// and the return reads the parameter.
///
/// The callee is a bare `ret`, so nothing states its arity, and `rcx` and
/// `rdx` hold the caller's own parameters, not values written for the
/// call: it takes none.
#[test]
fn parameter_copy_stays_symbolic_across_a_call() {
    let out = dc(0x1380);
    assert!(!out.contains("rdi ="), "{out}");
    assert!(out.contains("return a2;"), "{out}");
    assert!(out.contains("Base::vfunc_1();"), "{out}");
}

/// `CS`: the prologue save of `rbx` and its epilogue restore never render,
/// and the parameter copied into `rbx` survives the call as `a1`.
#[test]
fn callee_saved_register_saves_are_hidden() {
    let out = dc(0x13d0);
    assert!(
        !out.contains("arg_0 = rbx;") && !out.contains("home_0 = rbx;"),
        "save rendered:
{out}"
    );
    assert!(
        !out.contains("rbx = arg_0;") && !out.contains("rbx = home_0;"),
        "restore rendered:
{out}"
    );
    assert!(
        !out.contains("rbx ="),
        "parameter copy rendered:
{out}"
    );
    assert!(out.contains("return a1;"), "{out}");
}

/// `ES`: the address of a local passed in `r9` escapes although the callee
/// reads only `rcx`, so the local is stored before the call and reloaded
/// after it instead of staying the constant `0`.
#[test]
fn stack_address_in_an_uncounted_argument_register_escapes() {
    let out = dc(0x1410);
    assert!(out.contains("local_0 = 0;"), "{out}");
    assert!(out.contains("return local_0;"), "{out}");
    assert!(!out.contains("return 0;"), "{out}");
}

/// `E2`: the fall-through edge of `test eax, eax; jne` makes `rax` zero, but
/// the block then loads `rax` and the store writes it out; the `lea` after
/// that reads the new `rax`, not the assumed zero.
#[test]
fn equality_assumption_ends_when_the_register_is_written_out() {
    let out = dc(0x14b0);
    assert!(out.contains("var1 + 25"), "{out}");
    assert!(!out.contains("return 25;"), "{out}");
}

/// `FS`: flags over a register the block rewrites reach the next block as a
/// truth temporary.
///
/// The `cmp` reads `rax` and the block then assigns `rax`, which the join
/// after it writes out at the block's end; the flags over the old `rax`
/// cannot cross into the `setl` block as they are.
#[test]
fn flags_over_a_rewritten_register_reach_the_next_block_as_a_truth() {
    let out = dc(0x14f0);
    assert!(!out.contains("/* setl"), "{out}");
    assert!(out.contains("var3 = var1 < 5;"), "{out}");
}

/// A call whose result only the branch after it reads is written inside
/// the condition, and a guard chain takes it in as one of its terms.
///
/// `test rcx,rcx; je N; call F; test eax,eax; je N; mov eax,7; ret; N: xor
/// eax,eax; ret` with `F: mov eax,1; ret`: neither side reads `eax` after
/// the test, so the call is the second term of the guard, after the test
/// of `a1` that skips it, and no line assigns its result.
#[test]
fn a_call_tested_once_is_written_in_its_condition() {
    let mut code = vec![
        0x48, 0x85, 0xc9, 0x74, 0x0f, 0xe8, 0x36, 0x00, 0x00, 0x00, 0x85, 0xc0, 0x74, 0x06, 0xb8,
        0x07, 0x00, 0x00, 0x00, 0xc3, 0x31, 0xc0, 0xc3,
    ];
    code.resize(0x40, 0xcc);
    code.extend_from_slice(&[0xb8, 0x01, 0x00, 0x00, 0x00, 0xc3]);
    let p = program64(&code);
    let text = decompiled(&p, 0x1_4000_1000);
    assert!(!text.contains("= sub_140001040("), "{text}");
    assert!(
        text.contains("if (a1 != 0 && sub_140001040() != 0) {")
            || text.contains("if (a1 == 0 || sub_140001040() == 0) {"),
        "{text}"
    );
}

/// A decompilation reads the tables of the functions it calls and no
/// others: `CE2` calls `EN2` alone, so one table is read of the fixture's
/// three.
#[test]
fn a_decompilation_reads_only_the_tables_it_calls() {
    let p = fixture();
    let a = Analysis::compute(&p);
    let o = Overlay {
        enum_source: EnumSource::Binary,
        ..Overlay::default()
    };
    assert_eq!(a.derived.held("enum_table"), 0);
    let pass = decompile(&p, &a, &o, 0x4a40).expect("decompile");
    assert!(pass.contains("sub_4830(Over)"), "{pass}");
    assert_eq!(a.derived.held("enum_table"), 1);
}

/// A parameter used only at one narrower width is declared at that width.
///
/// `TP` sign-extends `a1` from 32 bits before every use, so the header says
/// `int32_t a1` and the body drops the cast, but for the 64-bit product,
/// which an `int` would overflow; `TP2` masks `a1` to a byte, so it is
/// `uint8_t a1` and the mask goes.
#[test]
fn parameters_used_at_one_width_are_typed() {
    let out = dc(0x4c20);
    assert!(
        out.contains("// signature: uint64_t sub_4c20(int32_t a1)"),
        "{out}"
    );
    assert!(out.contains("return (int64_t)a1 * 3;"), "{out}");
    let out = dc(0x4c30);
    assert!(out.contains("(uint8_t a1)"), "{out}");
    assert!(out.contains("return a1 + 1;"), "{out}");
}

/// A declared narrow parameter type drops the casts that agree with it.
///
/// An assert-typed `int a1` needs no `(int64_t)(int32_t)` at its uses and
/// a `bool a2` no `& 0xff`; a `uint64_t a3` used whole stays as it is.
#[test]
fn declared_parameter_types_drop_their_casts() {
    let text = "// signature: void f(int a1, bool a2, uint64_t a3)\nif ((int64_t)(int32_t)a1 < 0) {\n  return;\n}\nrax = (a2 & 0xff) + a3;\n";
    let out = polish(text, 64, &borer_engine::pack::Packs::default());
    assert!(
        out.contains("// signature: void f(int a1, bool a2, uint64_t a3)"),
        "{out}"
    );
    assert!(out.contains("if (a1 < 0) {"), "{out}");
    assert!(out.contains("rax = a2 + a3;"), "{out}");
}

/// Stack-passed arguments are parameters, not stack slots.
///
/// `SP5` reads the two words above the shadow space: on the Microsoft
/// convention those are the fifth and sixth arguments, so the header
/// declares them, the body names them, and no local declaration repeats
/// them.
#[test]
fn stack_passed_arguments_are_named_parameters() {
    let out = dc(0x4c90);
    assert!(
        out.contains(
            "sub_4c90(uint64_t a1, uint64_t a2, uint64_t a3, uint64_t a4, uint64_t a5, uint64_t a6)"
        ),
        "{out}"
    );
    assert!(out.contains("return a5 + a6;"), "{out}");
    assert!(!out.contains("arg_"), "{out}");
    assert!(
        !out.contains("uint64_t a5, a6;"),
        "declared as a local:\n{out}"
    );
}

/// A callee that only passes its arguments on still takes them.
///
/// `FW2` reads no argument register in its own body, it makes room on the
/// stack and calls `FW3`, which reads `rcx`; counting only what `FW2` reads
/// would drop the `0x77` from the call and lose what was passed.
#[test]
fn a_forwarded_argument_survives_the_call_that_forwards_it() {
    let out = dc(0x4e90);
    assert!(out.contains("sub_4eb0(119)"), "{out}");
}

/// `U` (call through the thunk) and `V` (call through the IAT slot) both
/// render as `ReportAssertFailure();`, never as an indirect call.
#[test]
fn import_calls_render_by_name() {
    let u = dc(0x1220);
    assert!(
        u.contains("ReportAssertFailure();"),
        "thunk call not named:\n{u}"
    );
    let v = dc(0x1230);
    assert!(
        v.contains("ReportAssertFailure();"),
        "IAT call not named:\n{v}"
    );
    assert!(!v.contains("indirect"), "IAT call left indirect:\n{v}");
}

/// An import call stops at the arity its prototype declares.
///
/// A call to an import lands on a thunk or a table slot, so nothing in the
/// binary says how many arguments it takes and the renderer pads the call to
/// the four register slots with whatever the caller's own parameters hold.
/// `Y` sets one argument and calls `ExitProcess`, which takes one.
#[test]
fn an_import_call_stops_at_its_declared_arity() {
    let out = dc(0x1270);
    assert!(out.contains("ExitProcess(1)"), "{out}");
}

/// A callee nothing states the arity of takes the caller's own registers
/// up to the last one set for the call, so it is not shown taking nothing.
///
/// `sub rsp,0x28; mov rax,rcx; add rax,r8; mov edx,5; lea r9,[rsp+0x50];
/// call [frob]; add rsp,0x28; ret`, as `_vsnwprintf` is called: `rcx` and
/// `r8` still hold the caller's `a1` and `a3`, and `rdx` and `r9` were set
/// for the call. The text closed the list at `rcx`, which the caller did
/// not write, and showed `frob()`.
#[test]
fn an_unknown_arity_call_takes_the_registers_up_to_the_last_set() {
    let code = [
        0x48, 0x83, 0xec, 0x28, // ASM: sub rsp, 0x28
        0x48, 0x89, 0xc8, // ASM: mov rax, rcx
        0x4c, 0x01, 0xc0, // ASM: add rax, r8
        0xba, 0x05, 0x00, 0x00, 0x00, // ASM: mov edx, 5
        0x4c, 0x8d, 0x4c, 0x24, 0x50, // ASM: lea r9, [rsp+0x50]
        0xff, 0x15, 0xe6, 0x0f, 0x00, 0x00, // ASM: call [rip+0xfe6]
        0x48, 0x83, 0xc4, 0x28, // ASM: add rsp, 0x28
        0xc3, // ASM: ret
    ];
    let p = program64_with_imports(&code, &[0u8; 8], &[(0x1_4000_2000, "Foo.dll!frob")]);
    let text = decompiled(&p, 0x1_4000_1000);
    assert!(text.contains("frob(a1, 5, a3, "), "{text}");
}

/// An import call passes what the SDK declares: `SetLastError` takes one
/// argument though `edx` was set too, and `sin` takes its `double` in
/// `xmm0`.
///
/// `sub rsp,0x28; mov ecx,5; mov edx,7; call [SetLastError]; movsd
/// xmm0,[two]; call [sin]; add rsp,0x28; ret`.
#[test]
fn an_import_call_takes_its_declared_arity() {
    let code = [
        0x48, 0x83, 0xec, 0x28, 0xb9, 0x05, 0x00, 0x00, 0x00, 0xba, 0x07, 0x00, 0x00, 0x00, 0xff,
        0x15, 0xec, 0x0f, 0x00, 0x00, 0xf2, 0x0f, 0x10, 0x05, 0xf4, 0x0f, 0x00, 0x00, 0xff, 0x15,
        0xe6, 0x0f, 0x00, 0x00, 0x48, 0x83, 0xc4, 0x28, 0xc3,
    ];
    let mut data = vec![0u8; 0x10];
    data.extend_from_slice(&2.0f64.to_bits().to_le_bytes());
    let p = program64_with_imports(
        &code,
        &data,
        &[
            (0x1_4000_2000, "KERNEL32.dll!SetLastError"),
            (0x1_4000_2008, "api-ms-win-crt-math-l1-1-0.dll!sin"),
        ],
    );
    let text = decompiled(&p, 0x1_4000_1000);
    assert!(text.contains("SetLastError(5);"), "{text}");
    assert!(text.contains("sin(") && !text.contains("sin()"), "{text}");
}

/// A wrapper named like the import it forwards to calls the import's slot,
/// not itself: kernel32's `Beep` jumps to KERNELBASE's.
///
/// `jmp [Beep]` at the export `Beep`.
///
/// # Panics
///
/// When the call reads as recursion.
#[test]
fn a_wrapper_named_like_its_import_does_not_call_itself() {
    use borer_engine::program::{Symbol, SymbolKind};
    let code = [
        0xff, 0x25, 0xfa, 0x0f, 0x00, 0x00, // ASM: jmp [rip+0xffa]
    ];
    let mut p = program64_with_imports(
        &code,
        &[0u8; 0x10],
        &[(0x1_4000_2000, "api-ms-win-core-misc-l1-1-0.dll!Beep")],
    );
    p.symbols.push(Symbol {
        name: "Beep".to_owned(),
        addr: 0x1_4000_1000,
        kind: SymbolKind::Export,
    });
    let text = decompiled(&p, 0x1_4000_1000);
    assert!(text.contains("return __imp_Beep(a1, a2);"), "{text}");
    assert!(!text.contains("return Beep("), "{text}");
}

/// A register a call clobbered is no argument of a later call.
///
/// `mov rax,rdx; sub rsp,0x28; call leaf; mov ecx,87; call
/// [RtlSetLastWin32Error]; mov ecx,5; call [SetLastError]; add rsp,0x28;
/// ret`, the leaf `mov edx,5; ret`: `rdx` held the caller's own `a2` until
/// the leaf clobbered it, so the undocumented import gets the one register
/// written for it and `SetLastError` its one declared argument, where both
/// once rendered `(87, rdx)` and `(5, rdx)`.
#[test]
fn a_clobbered_register_is_no_argument() {
    let mut code = vec![
        0x48, 0x89, 0xd0, 0x48, 0x83, 0xec, 0x28, 0xe8, 0x34, 0x00, 0x00, 0x00, 0xb9, 0x57, 0x00,
        0x00, 0x00, 0xff, 0x15, 0xe9, 0x0f, 0x00, 0x00, 0xb9, 0x05, 0x00, 0x00, 0x00, 0xff, 0x15,
        0xe6, 0x0f, 0x00, 0x00, 0x48, 0x83, 0xc4, 0x28, 0xc3,
    ];
    code.resize(0x40, 0xcc);
    code.extend_from_slice(&[0xba, 0x05, 0x00, 0x00, 0x00, 0xc3]);
    let p = program64_with_imports(
        &code,
        &[0; 16],
        &[
            (0x1_4000_2000, "ntdll.dll!RtlSetLastWin32Error"),
            (0x1_4000_2008, "KERNEL32.dll!SetLastError"),
        ],
    );
    let text = decompiled(&p, 0x1_4000_1000);
    assert!(text.contains("RtlSetLastWin32Error(87);"), "{text}");
    assert!(text.contains("SetLastError(5);"), "{text}");
    assert!(!text.contains("rdx"), "{text}");
}

/// A forwarder passes its own parameters through.
///
/// `jmp [MultiByteToWideChar]` takes the import's six arguments, four in
/// registers and two on the stack above the return address the jump
/// leaves, and its signature lists the same six. The thunk is named for
/// the import, so the call goes through the slot's own name rather than
/// reading as a call to itself.
#[test]
fn a_forwarder_passes_its_parameters_through() {
    let code = [0xff, 0x25, 0xfa, 0x0f, 0x00, 0x00];
    let p = program64_with_imports(
        &code,
        &[0; 8],
        &[(0x1_4000_2000, "KERNEL32.dll!MultiByteToWideChar")],
    );
    let text = decompiled(&p, 0x1_4000_1000);
    assert!(
        text.contains("return __imp_MultiByteToWideChar(a1, a2, a3, a4, a5, a6);"),
        "{text}"
    );
    assert!(text.contains("int a6)"), "{text}");
}

/// A function's signature and every call to it print one arity.
///
/// The callee reads `r8` only on the path that skips its call: `test
/// ecx,ecx; je L; call leaf; ret; L: mov eax,r8d; ret`. Read in address
/// order up to the first call it seemed to take one argument, while its
/// own signature lists three; the caller, which sets four registers,
/// passes the three the signature lists. `ecx` and `r8d` are 32-bit uses,
/// so those two parameters are `uint32_t`; the unread `edx` stays
/// `uint64_t`.
#[test]
fn a_call_passes_what_the_callee_signature_lists() {
    let mut code = vec![
        0x48, 0x83, 0xec, 0x28, 0xb9, 0x01, 0x00, 0x00, 0x00, 0xba, 0x02, 0x00, 0x00, 0x00, 0x41,
        0xb8, 0x03, 0x00, 0x00, 0x00, 0x41, 0xb9, 0x04, 0x00, 0x00, 0x00, 0xe8, 0x21, 0x00, 0x00,
        0x00, 0x48, 0x83, 0xc4, 0x28, 0xc3,
    ];
    code.resize(0x40, 0xcc);
    code.extend_from_slice(&[
        0x85, 0xc9, 0x74, 0x06, 0xe8, 0x17, 0x00, 0x00, 0x00, 0xc3, 0x44, 0x89, 0xc0, 0xc3,
    ]);
    code.resize(0x60, 0xcc);
    code.extend_from_slice(&[0xb8, 0x01, 0x00, 0x00, 0x00, 0xc3]);
    let p = program64(&code);
    let caller = decompiled(&p, 0x1_4000_1000);
    assert!(caller.contains("sub_140001040(1, 2, 3);"), "{caller}");
    let callee = decompiled(&p, 0x1_4000_1040);
    assert!(
        callee.contains("sub_140001040(uint32_t a1, uint64_t a2, uint32_t a3)"),
        "{callee}"
    );
}

/// A register the body reads past an attributed signature stays a
/// parameter.
///
/// `void __cdecl Cls::Two(int,int)`, attributed from the text the body
/// references, lists two parameters, while the body reads `rdx`, `r8`,
/// `r9` and a stack argument: the attribution understates the arity, so
/// the signature lists all five positions, `this` first, and its caller
/// passes five, where the signature once stopped at three and the body
/// read `r9` and the stack argument as registers nothing defined.
#[test]
fn a_register_read_past_an_attributed_signature_stays_a_parameter() {
    let mut code = vec![
        0x48, 0x83, 0xec, 0x38, 0xb9, 0x01, 0x00, 0x00, 0x00, 0xba, 0x02, 0x00, 0x00, 0x00, 0x41,
        0xb8, 0x03, 0x00, 0x00, 0x00, 0x41, 0xb9, 0x04, 0x00, 0x00, 0x00, 0x48, 0xc7, 0x44, 0x24,
        0x20, 0x05, 0x00, 0x00, 0x00, 0xe8, 0x18, 0x00, 0x00, 0x00, 0x48, 0x83, 0xc4, 0x38, 0xc3,
    ];
    code.resize(0x40, 0xcc);
    code.extend_from_slice(&[
        0x4c, 0x8d, 0x15, 0xb9, 0x0f, 0x00, 0x00, 0x48, 0x8b, 0x44, 0x24, 0x28, 0x4c, 0x01, 0xc8,
        0x4c, 0x01, 0xc0, 0x48, 0x01, 0xd0, 0xc3,
    ]);
    let p = program64_with_data(&code, b"void __cdecl Cls::Two(int,int)\0");
    let callee = decompiled(&p, 0x1_4000_1040);
    assert!(
        callee.contains("Cls::Two(Cls *this, int a2, int a3, uint64_t a4, uint64_t a5)"),
        "{callee}"
    );
    let caller = decompiled(&p, 0x1_4000_1000);
    assert!(caller.contains("Cls::Two(1, 2, 3, 4, 5);"), "{caller}");
}

/// An export named after an API takes the API's arity.
///
/// Kernel32's `SetLastError` is one `jmp [RtlSetLastWin32Error]` to an
/// import no header declares, and it takes the one argument
/// `SetLastError` takes, which it passes on.
#[test]
fn an_export_named_after_an_api_takes_its_arity() {
    let code = [0xff, 0x25, 0xfa, 0x0f, 0x00, 0x00];
    let p = program64_with_imports(
        &code,
        &[0; 8],
        &[(0x1_4000_2000, "ntdll.dll!RtlSetLastWin32Error")],
    );
    let a = Analysis::compute(&p);
    let mut o = Overlay::default();
    o.names.insert(0x1_4000_1000, "SetLastError".to_owned());
    let text = decompile(&p, &a, &o, 0x1_4000_1000).unwrap_or_default();
    assert!(text.contains("SetLastError(uint64_t a1)"), "{text}");
    assert!(text.contains("return RtlSetLastWin32Error(a1);"), "{text}");
}

/// A register a leaf callee never writes keeps its value across the call.
///
/// `mov r8,rcx; xor edx,edx; call leaf; mov [r8+0xc0],dl; ret` with the
/// leaf `mov eax,1; ret` stores a zero into `a1`, where it once stored the
/// never-assigned `rdx` through the never-assigned `r8`.
#[test]
fn a_register_the_callee_leaves_alone_survives_the_call() {
    let mut code = vec![
        0x49, 0x89, 0xc8, 0x31, 0xd2, 0xe8, 0x36, 0x00, 0x00, 0x00, 0x41, 0x88, 0x90, 0xc0, 0x00,
        0x00, 0x00, 0xc3,
    ];
    code.resize(0x40, 0xcc);
    code.extend_from_slice(&[0xb8, 0x01, 0x00, 0x00, 0x00, 0xc3]);
    let p = program64(&code);
    let text = decompiled(&p, 0x1_4000_1000);
    assert!(text.contains("= 0;"), "{text}");
    assert!(!text.contains("r8"), "{text}");
    assert!(!text.contains("rdx"), "{text}");
}

/// An argument renders after the write-outs its call forces.
///
/// Once `rdi += rax;` is in the text, the argument that was `rdi + rax`
/// reads `rdi`, not `rdi + rax` a second time.
///
/// `push rdi; sub rsp,0x20; mov rdi,rcx; call f; add rdi,rax; mov rcx,rdi;
/// call g; add rdi,rax; mov rcx,rdi; call g; mov rax,rdi; add rsp,0x20;
/// pop rdi; ret`, `f` `mov eax,5; ret`, `g` `mov rax,rcx; ret`.
#[test]
fn an_argument_reads_the_text_its_call_leaves() {
    let mut code = vec![
        0x57, 0x48, 0x83, 0xec, 0x20, 0x48, 0x89, 0xcf, 0xe8, 0x33, 0x00, 0x00, 0x00, 0x48, 0x01,
        0xc7, 0x48, 0x89, 0xf9, 0xe8, 0x38, 0x00, 0x00, 0x00, 0x48, 0x01, 0xc7, 0x48, 0x89, 0xf9,
        0xe8, 0x2d, 0x00, 0x00, 0x00, 0x48, 0x89, 0xf8, 0x48, 0x83, 0xc4, 0x20, 0x5f, 0xc3,
    ];
    code.resize(0x40, 0xcc);
    code.extend_from_slice(&[0xb8, 0x05, 0x00, 0x00, 0x00, 0xc3]);
    code.resize(0x50, 0xcc);
    code.extend_from_slice(&[0x48, 0x89, 0xc8, 0xc3]);
    let p = program64(&code);
    let text = decompiled(&p, 0x1_4000_1000);
    assert!(text.contains("var2 += var3;"), "{text}");
    assert!(!text.contains("sub_140001050(var2 + var3)"), "{text}");
}

/// A stack parameter loaded through the stack pointer and dereferenced is
/// a pointer.
///
/// `mov rax,[rsp+0x28]; mov eax,[rax+8]; ret` reads a word through its
/// fifth parameter, the first on the stack: the signature calls it a
/// pointer, a `void *` since the word lies past its start.
#[test]
fn a_stack_parameter_loaded_through_the_stack_pointer_is_typed() {
    let code = [0x48, 0x8b, 0x44, 0x24, 0x28, 0x8b, 0x40, 0x08, 0xc3];
    let p = program64(&code);
    let text = decompiled(&p, 0x1_4000_1000);
    assert!(text.contains("void *a5)"), "{text}");
}

/// A parameter a `lea` only adds to is no pointer.
///
/// `lea eax,[rcx-0x30]; ret` is `c - '0'`: the sum names no memory, so the
/// parameter stays a number, where the signature once called it a `void *`.
#[test]
fn a_parameter_a_lea_only_adds_to_is_no_pointer() {
    let p = program64(&[0x8d, 0x41, 0xd0, 0xc3]);
    let text = decompiled(&p, 0x1_4000_1000);
    assert!(text.contains("(uint64_t a1)"), "{text}");
}

/// Parameters parked home are no variable argument list.
///
/// A function that parks its parameters home without taking an address
/// past them is not variadic: `mov [rsp+0x10],rdx; mov [rsp+0x18],r8; mov
/// [rsp+0x20],r9; mov rax,[rsp+0x18]; add rax,rcx; ret` takes four.
#[test]
fn parameters_parked_home_are_no_variable_list() {
    let code = [
        0x48, 0x89, 0x54, 0x24, 0x10, 0x4c, 0x89, 0x44, 0x24, 0x18, 0x4c, 0x89, 0x4c, 0x24, 0x20,
        0x48, 0x8b, 0x44, 0x24, 0x18, 0x48, 0x01, 0xc8, 0xc3,
    ];
    let p = program64(&code);
    let text = decompiled(&p, 0x1_4000_1000);
    assert!(text.contains("uint64_t a4)"), "{text}");
    assert!(!text.contains("..."), "{text}");
}

/// A stack argument read through a copy of the stack pointer counts.
///
/// `mov r11,rsp; sub rsp,0x28; mov eax,[r11+0x28]; add rsp,0x28; ret`
/// reads the first stack argument, as `push ebx; mov ebx,esp; and
/// esp,-16` code reads its arguments through `ebx`.
#[test]
fn a_stack_argument_read_through_a_copy_of_the_stack_pointer_counts() {
    let code = [
        0x4c, 0x8b, 0xdc, 0x48, 0x83, 0xec, 0x28, 0x41, 0x8b, 0x43, 0x28, 0x48, 0x83, 0xc4, 0x28,
        0xc3,
    ];
    let p = program64(&code);
    let a = Analysis::compute(&p);
    assert_eq!(a.function(0x1_4000_1000).map(|f| f.stack_args), Some(1));
}

/// Two folded checks name their callees in one header note, exactly once.
///
/// `f` runs a bounds check and a negation check, each diamond handing its
/// panic entry the operands and a `core::panic::Location`; the entries are
/// functions that load their message's template and call on without
/// returning, which names them. Both diamonds leave whole — the bounds one
/// onto the indexing it guards, the negation one onto the return that
/// negates `a2` — and the header's note line appears once, naming both
/// callees.
#[test]
fn two_folded_checks_name_both_callees_in_one_note() {
    let mut code: Vec<u8> = vec![
        0x48, 0x39, 0xd1, // ASM: cmp rcx,rdx
        0x0f, 0x83, 0x24, 0, 0, 0, // ASM: jae FAIL1
        0x49, 0x8b, 0x04, 0xc8, // ASM: mov rax,[r8+rcx*8]
        0x49, 0x89, 0x01, // ASM: mov [r9],rax
        0x49, 0xba, 0, 0, 0, 0, 0, 0, 0, 0x80, // ASM: mov r10,0x8000000000000000
        0x4c, 0x39, 0xd2, // ASM: cmp rdx,r10
        0x0f, 0x84, 0x1d, 0, 0, 0, // ASM: je FAIL2
        0x48, 0xf7, 0xda, // ASM: neg rdx
        0x48, 0x03, 0xd1, // ASM: add rdx,rcx
        0x48, 0x03, 0xc2, // ASM: add rax,rdx
        0xc3, // ASM: ret
        0x4c, 0x8d, 0x05, 0xcc, 0x11, 0, 0, // ASM: FAIL1: lea r8,[rip+LOC1]
        0xe8, 0x27, 0, 0, 0, // ASM: call panic_bounds_check
    ];
    code.resize(0x40, 0xcc);
    code.extend_from_slice(&[
        0x4c, 0x8d, 0x05, 0xd9, 0x11, 0, 0, // ASM: FAIL2: lea r8,[rip+LOC2]
        0xe8, 0x54, 0, 0, 0, // ASM: call panic_const_neg_overflow
    ]);
    code.resize(0xe0, 0xcc);
    for (base, call) in [(0x60usize, 0x60u32), (0xa0, 0x20)] {
        let mut helper = vec![
            0x55, // ASM: push rbp
            0x48, 0x83, 0xec, 0x50, // ASM: sub rsp,0x50
            0x48, 0x89, 0x4c, 0x24, 0x48, // ASM: mov [rsp+0x48],rcx
            0x48, 0x89, 0x54, 0x24, 0x40, // ASM: mov [rsp+0x40],rdx
            0x4c, 0x89, 0x44, 0x24, 0x38, // ASM: mov [rsp+0x38],r8
            0x48, 0x8d, 0x0d, 0x85, 0x10, 0, 0, // ASM: lea rcx,[rip+MSG]
        ];
        helper.extend_from_slice(&call.to_le_bytes()); // ASM: call ud2
        code[base..base + helper.len()].copy_from_slice(&helper);
    }
    code.extend_from_slice(&[0x0f, 0x0b]); // ASM: ud2
    let file = br"C:\Users\me\.cargo\registry\src\index.crates.io-1949cf8c6b5b557f\rhai-1.26.1\src\parser.rs";
    let mut data = vec![0u8; 0x240];
    data[0x10..0x10 + file.len()].copy_from_slice(file);
    let bounds = b"\x20index out of bounds: the len is \xc0\x12 but the index is ";
    data[0x100..0x100 + bounds.len()].copy_from_slice(bounds);
    let negate = b"\x1dattempt to negate with overflow";
    data[0x140..0x140 + negate.len()].copy_from_slice(negate);
    let len = u64::try_from(file.len()).expect("a short path");
    for (at, line, column) in [(0x200u64, 1015u32, 32u32), (0x220, 1016, 9)] {
        let at = usize::try_from(at).unwrap_or(0);
        data[at..at + 8].copy_from_slice(&0x1_4000_2010u64.to_le_bytes());
        data[at + 8..at + 16].copy_from_slice(&len.to_le_bytes());
        data[at + 16..at + 20].copy_from_slice(&line.to_le_bytes());
        data[at + 20..at + 24].copy_from_slice(&column.to_le_bytes());
    }
    let p = program64_with_data(&code, &data);
    let text = decompiled(&p, 0x1_4000_1000);
    let note = text
        .lines()
        .filter(|l| l.starts_with("// note: calls to "))
        .collect::<Vec<_>>();
    assert_eq!(
        note,
        vec![
            "// note: calls to panic_bounds_check, panic_const_neg_overflow are left out: rust overflow and bounds checks folded"
        ],
        "{text}"
    );
    assert!(
        text.contains("var1 = a3[a1];  /* bounds-checked */"),
        "{text}"
    );
    assert!(
        text.contains("return var1 + -a2 + a1;  /* checked */"),
        "{text}"
    );
    assert!(!text.contains("panic_bounds_check("), "{text}");
    assert!(!text.contains("panic_const_neg_overflow("), "{text}");
    assert_eq!(
        borer_engine::analysis::decompile::traces::check_structure(
            &p,
            &Analysis::compute(&p),
            &Overlay::default(),
            0x1_4000_1000,
            &text
        ),
        borer_engine::analysis::decompile::traces::Structure::Agrees,
        "{text}"
    );
}

/// A wrapper that reads one argument and calls on passes its callee the
/// others too.
///
/// `f: call g; ret`, `g: mov r8,rcx; call h; ret`, `h: mov rax,rdx; ret`:
/// `g` reads `rcx` and hands `h` the `rdx` it never wrote, so `f`, which
/// hands `g` both, takes two. The scan of `g` once stopped at its own read
/// of `rcx`, `f` took one, and its text called `g` without the `rdx` that
/// `h` returns.
#[test]
fn a_wrapper_passes_on_what_its_callee_reads_beyond_its_own() {
    let mut code = vec![
        0x48, 0x83, 0xec, 0x28, // ASM: sub rsp, 0x28
        0xe8, 0x37, 0x00, 0x00, 0x00, // ASM: call 0x140001040
        0x48, 0x83, 0xc4, 0x28, // ASM: add rsp, 0x28
        0xc3, // ASM: ret
    ];
    code.resize(0x40, 0xcc);
    code.extend_from_slice(&[
        0x48, 0x83, 0xec, 0x28, // ASM: sub rsp, 0x28
        0x49, 0x89, 0xc8, // ASM: mov r8, rcx
        0xe8, 0x34, 0x00, 0x00, 0x00, // ASM: call 0x140001080
        0x48, 0x83, 0xc4, 0x28, // ASM: add rsp, 0x28
        0xc3, // ASM: ret
    ]);
    code.resize(0x80, 0xcc);
    code.extend_from_slice(&[
        0x48, 0x89, 0xd0, // ASM: mov rax, rdx
        0xc3, // ASM: ret
    ]);
    let text = runs_agree(&program64(&code), 0x1_4000_1000);
    assert!(text.contains("sub_140001040(a1, a2)"), "{text}");
}

/// A fiber procedure handed to `CreateFiber` is seeded as a function by
/// the pointer that hands it over.
///
/// Nothing ever calls the fiber proc: `CreateFiber` receives its address
/// and the scheduler enters it, so the only evidence the binary carries
/// is the `lea` that loads it into the second argument slot. That pointer
/// into executable code is a witness on its own, so the proc is
/// discovered and decompiles even where it sits flush after its caller,
/// unaligned and behind no padding a gap seed could read. The seed is the
/// pointer, not the callee's name, so a threadpool callback handed to
/// `TrySubmitThreadpoolCallback` or `QueueUserWorkItem` rides the same
/// path, and the call renders the three arguments the prototype declares.
#[test]
fn a_fiber_proc_handed_to_createfiber_is_seeded() {
    let mut code = vec![
        0x48, 0x83, 0xec, 0x28, // ASM: sub rsp, 28h
        0x31, 0xc9, // ASM: xor ecx, ecx
        0x48, 0x8d, 0x15, 0x0e, 0x00, 0x00, 0x00, // ASM: lea rdx, [0x14000101b]
        0x45, 0x31, 0xc0, // ASM: xor r8d, r8d
        0xff, 0x15, 0xea, 0x0f, 0x00, 0x00, // ASM: call [0x140002000]
        0x48, 0x83, 0xc4, 0x28, // ASM: add rsp, 28h
        0xc3, // ASM: ret
    ];
    assert_eq!(code.len(), 0x1b);
    code.extend_from_slice(&[0xb8, 0x2a, 0x00, 0x00, 0x00, 0xc3]); // ASM: mov eax, 42; ret
    let p = program64_with_imports(
        &code,
        &[0; 0x20],
        &[(0x1_4000_2000, "kernel32.dll!CreateFiber")],
    );
    let a = Analysis::compute(&p);
    assert!(
        a.functions.iter().any(|f| f.entry == 0x1_4000_101b),
        "the fiber proc was not seeded: {:x?}",
        a.functions.iter().map(|f| f.entry).collect::<Vec<_>>()
    );
    let fiber = decompiled(&p, 0x1_4000_101b);
    assert!(fiber.contains("return 42;"), "{fiber}");
    let text = decompiled(&p, 0x1_4000_1000);
    assert!(
        text.contains("CreateFiber(0, sub_14000101b, NULL);"),
        "{text}"
    );
}

/// A call to a compiler runtime helper passes what the helper's prototype
/// takes, not every register the call happens to set, and the function's
/// header declares the helper with what it computes.
///
/// The caller sets `r8` and `r9` before calling a function named
/// `__umodti3` whose body reads all four argument registers; under the
/// Microsoft convention it takes two pointers, so the call passes two.
#[test]
fn a_runtime_helper_call_takes_its_prototype() {
    use borer_engine::analysis::decompile::decompile_named;
    let mut code = vec![
        0x48, 0x83, 0xec, 0x28, // ASM: sub rsp,0x28
        0x49, 0xc7, 0xc0, 0x07, 0x00, 0x00, 0x00, // ASM: mov r8,7
        0x49, 0xc7, 0xc1, 0x09, 0x00, 0x00, 0x00, // ASM: mov r9,9
        0xe8, 0x09, 0x00, 0x00, 0x00, // ASM: call 0x140001020
        0x48, 0x83, 0xc4, 0x28, // ASM: add rsp,0x28
        0xc3, // ASM: ret
    ];
    code.resize(0x20, 0xcc);
    code.extend([
        0x48, 0x89, 0xc8, // ASM: mov rax,rcx
        0x48, 0x01, 0xd0, // ASM: add rax,rdx
        0x4c, 0x01, 0xc0, // ASM: add rax,r8
        0x4c, 0x01, 0xc8, // ASM: add rax,r9
        0xc3, // ASM: ret
    ]);
    let p = program64(&code);
    let a = Analysis::compute(&p);
    let mut o = Overlay::default();
    o.names.insert(0x1_4000_1020, "__umodti3".to_owned());
    let text = decompile_named(&p, &a, &o, 0x1_4000_1000).unwrap_or_default();
    assert!(
        text.contains(
            "// runtime: uint128_t __umodti3(uint128_t a, uint128_t b); computes a % b, unsigned"
        ),
        "{text}"
    );
    assert!(text.contains("__umodti3(a1, a2)"), "{text}");
    o.names.insert(0x1_4000_1020, "plain_callee".to_owned());
    let plain = decompile_named(&p, &a, &o, 0x1_4000_1000).unwrap_or_default();
    assert!(plain.contains("plain_callee(a1, a2, 7, 9)"), "{plain}");
    assert!(!plain.contains("// runtime:"), "{plain}");
}
