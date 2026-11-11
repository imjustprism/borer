//! Stack arguments under cdecl, stdcall and thiscall, and `this` in `ecx`.

use super::*;

/// An argument read after a call has popped the caller's pushes is still a
/// parameter, though no prologue shape says so.
///
/// `push 7; call 0x401040; mov eax,[esp+4]; ret` calls `ret 4`: the frame
/// scan sees a push and counts the frame four bytes deep, but the callee
/// pops it, and `[esp+4]` is the first argument.
#[test]
fn an_argument_read_after_a_popping_call_is_a_parameter() {
    let mut code = vec![
        0x6a, 0x07, 0xe8, 0x39, 0x00, 0x00, 0x00, 0x8b, 0x44, 0x24, 0x04, 0xc3,
    ];
    code.resize(0x40, 0xcc);
    code.extend_from_slice(&[0xc2, 0x04, 0x00]);
    let text = dc(&code);
    assert!(text.contains("return a1;"), "{text}");
    assert!(text.contains("(uint32_t a1)"), "{text}");
}

/// The address of a pushed memory operand reads its registers.
///
/// `push ebp; mov ebp,esp; push dword [ecx+0x38]; call f; add esp,4; pop
/// ebp; ret` reads `ecx` though the push is only an argument of `f`, so
/// `ecx` is a parameter and not a register the body reads undefined.
#[test]
fn a_pushed_memory_operand_reads_its_address_registers() {
    let mut code = vec![
        0x55, 0x8b, 0xec, 0xff, 0x71, 0x38, 0xe8, 0x35, 0x00, 0x00, 0x00, 0x83, 0xc4, 0x04, 0x5d,
        0xc3,
    ];
    code.resize(0x40, 0xcc);
    code.extend_from_slice(&[0x8b, 0x44, 0x24, 0x04, 0xc3]);
    let text = dc(&code);
    assert!(text.contains("*this)"), "{text}");
    assert!(!text.contains("ecx"), "{text}");
}

/// A method read as a thiscall counts its stack arguments past `this`.
///
/// `C::m`, whose callers pass a `C` first, is `mov eax,[esp+4]; ret 4`: it
/// never reads `ecx`, so the registers say `cdecl`, but as a method `this`
/// travels in `ecx` and the word on the stack is its second parameter,
/// which the signature lists.
#[test]
fn a_thiscall_method_counts_its_stack_arguments_past_this() {
    let p = image(&[0x8b, 0x44, 0x24, 0x04, 0xc2, 0x04, 0x00]);
    let mut a = Analysis::compute(&p);
    if let Some(f) = a.functions.iter_mut().find(|f| f.entry == 0x401000) {
        f.param_hints.insert(0, "C".to_owned());
    }
    let mut o = Overlay::default();
    o.names.insert(0x401000, "C::m".to_owned());
    let text = decompile(&p, &a, &o, 0x401000).unwrap_or_default();
    assert!(text.contains("m(C *this, uint32_t a2)"), "{text}");
    assert!(text.contains("return a2;"), "{text}");
}

/// An argument read out of its own slot does not escape.
///
/// `push ebp; mov ebp,esp; cmp dword [ebp+8],0; je L; push -1; jmp M; L:
/// push 4; M: call f; pop ebp; ret` with `f` a `ret 4`: the word the two
/// paths push meets at the call and is passed as the slot's content, so
/// the slot's address goes nowhere and nothing is reloaded after calls.
#[test]
fn an_argument_read_out_of_its_own_slot_does_not_escape() {
    let mut code = vec![
        0x55, 0x8b, 0xec, 0x83, 0x7d, 0x08, 0x00, 0x74, 0x04, 0x6a, 0xff, 0xeb, 0x02, 0x6a, 0x04,
        0xe8, 0x2c, 0x00, 0x00, 0x00, 0x5d, 0xc3,
    ];
    code.resize(0x40, 0xcc);
    code.extend_from_slice(&[0x8b, 0x44, 0x24, 0x04, 0xc2, 0x04, 0x00]);
    let text = dc(&code);
    assert!(text.contains("= -1;") && text.contains("= 4;"), "{text}");
    assert!(text.contains("sub_401040(local_"), "{text}");
    assert!(!text.contains("escapes"), "{text}");
}

/// A stack parameter the body dereferences is a pointer.
///
/// `push ebp; mov ebp,esp; mov eax,[ebp+8]; mov eax,[eax+0x10]; pop ebp;
/// ret` loads its first stack argument through the frame pointer and reads
/// a word through it: the parameter is a pointer, a `void *` since the
/// word lies past its start, where the signature once called it a number.
#[test]
fn a_stack_parameter_the_body_dereferences_is_a_pointer() {
    let text = dc(&[
        0x55, 0x8b, 0xec, 0x8b, 0x45, 0x08, 0x8b, 0x40, 0x10, 0x5d, 0xc3,
    ]);
    assert!(text.contains("(void *a1)"), "{text}");
}

/// A call to an import whose mangled name states its parameters carries
/// them, in order, and the callee's pop of them is applied.
///
/// `push 2; push 1; call dword [0x402000]; mov eax,[esp-4]; ret` calls
/// `void __stdcall bar(int, int)`: the two pushes are its two arguments,
/// and the stack pointer after the call is back where it was before them.
#[test]
fn a_stdcall_import_takes_the_pushes_as_its_arguments() {
    let text = dc_with(
        &[
            0x6a, 0x02, 0x6a, 0x01, 0xff, 0x15, 0x00, 0x20, 0x40, 0x00, 0x8b, 0x44, 0x24, 0xfc,
            0xc3,
        ],
        &[(0x402000, "Foo.dll!?bar@@YGXHH@Z")],
    );
    assert!(text.contains("bar(1, 2);"), "{text}");
    assert!(text.contains("local_0"), "{text}");
    assert!(!text.contains("local_8"), "{text}");
    assert!(!text.contains("local_4 = 1;"), "{text}");
    assert!(!text.contains("local_0 = 2;"), "{text}");
}

/// A tail jump through an import is a call that returns its result, and it
/// carries its arguments like one: `mov ecx,[esp+4]; jmp dword [0x402000]`
/// to `void __thiscall C::m(void)` is `return C::m(a1);`.
#[test]
fn a_tail_jump_through_an_import_carries_its_arguments() {
    let text = dc_with(
        &[0x8b, 0x4c, 0x24, 0x04, 0xff, 0x25, 0x00, 0x20, 0x40, 0x00],
        &[(0x402000, "Foo.dll!?m@C@@QAEXXZ")],
    );
    assert!(text.contains("return C::m(a1);"), "{text}");
}

/// A `__thiscall` import takes `ecx` first, then the pushes.
///
/// `mov ecx,5; push 1; call dword [0x402000]; ret` calls
/// `void __thiscall C::m(int)`.
#[test]
fn a_thiscall_import_takes_ecx_first() {
    let text = dc_with(
        &[
            0xb9, 0x05, 0x00, 0x00, 0x00, 0x6a, 0x01, 0xff, 0x15, 0x00, 0x20, 0x40, 0x00, 0xc3,
        ],
        &[(0x402000, "Foo.dll!?m@C@@QAEXH@Z")],
    );
    assert!(text.contains("C::m(5, 1);"), "{text}");
}

/// A Win32 import outside the C runtime is `__stdcall` on a 32-bit target
/// and pops its arguments; a C runtime import is `__cdecl` and leaves them.
///
/// Five zero pushes then `call dword [0x402000]; mov eax,[esp-4]; ret`
/// against `WriteFile`: the callee pops its five arguments and `[esp-4]`
/// is the slot four below the entry. Three pushes against `memset`: the
/// `__cdecl` callee leaves them, and `[esp-4]` is sixteen below.
#[test]
fn win32_imports_pop_and_runtime_imports_do_not() {
    let tail = [
        0xff, 0x15, 0x00, 0x20, 0x40, 0x00, 0x8b, 0x44, 0x24, 0xfc, 0xc3,
    ];
    let mut five = vec![0x6a, 0x00, 0x6a, 0x00, 0x6a, 0x00, 0x6a, 0x00, 0x6a, 0x00];
    five.extend_from_slice(&tail);
    let win32 = dc_with(&five, &[(0x402000, "KERNEL32.dll!WriteFile")]);
    assert!(
        win32.contains("WriteFile(NULL, NULL, 0, NULL, NULL);"),
        "{win32}"
    );
    assert!(win32.contains("local_0"), "{win32}");
    let mut three = vec![0x6a, 0x00, 0x6a, 0x00, 0x6a, 0x00];
    three.extend_from_slice(&tail);
    let crt = dc_with(&three, &[(0x402000, "MSVCR100.dll!memset")]);
    assert!(crt.contains("memset(NULL, 0, 0);"), "{crt}");
    assert!(crt.contains("local_c"), "{crt}");
}

/// A function that reads `ecx` before writing it is a `__thiscall` method,
/// and `ecx` is `this`: `mov eax,[ecx+4]; ret`.
#[test]
fn a_function_reading_ecx_first_takes_this() {
    let text = dc(&[0x8b, 0x41, 0x04, 0xc3]);
    assert!(text.contains("(void *this)"), "{text}");
    assert!(!text.contains("ecx"), "{text}");
}

/// A `__thiscall` callee inside the image takes `ecx` at the call:
/// `mov ecx,5; call 0x401040; ret` to `mov eax,[ecx+4]; ret`.
#[test]
fn an_internal_thiscall_callee_takes_ecx() {
    let mut code = vec![
        0xb9, 0x05, 0x00, 0x00, 0x00, 0xe8, 0x36, 0x00, 0x00, 0x00, 0xc3,
    ];
    code.resize(0x40, 0xcc);
    code.extend_from_slice(&[0x8b, 0x41, 0x04, 0xc3]);
    let text = dc(&code);
    assert!(text.contains("sub_401040(5)"), "{text}");
}

/// A `__thiscall` callee whose `ecx` an earlier call clobbered still
/// takes `ecx` first, so its stack arguments keep their places.
///
/// `call 0x401060; push 7; push 9; call 0x401040; ret`, where 0x401040 is
/// `mov eax,[ecx]; add eax,[esp+4]; add eax,[esp+8]; ret 8` and 0x401060
/// `xor eax,eax; ret`: the text named the two pushes as the callee's
/// first two arguments, `this` and `a2`, where the machine passes them as
/// `a2` and `a3` with whatever `ecx` holds as `this`.
#[test]
fn a_clobbered_this_keeps_the_stack_arguments_in_place() {
    let mut code = vec![
        0xe8, 0x5b, 0x00, 0x00, 0x00, // ASM: call 0x401060
        0x6a, 0x07, // ASM: push 7
        0x6a, 0x09, // ASM: push 9
        0xe8, 0x32, 0x00, 0x00, 0x00, // ASM: call 0x401040
        0xc3, // ASM: ret
    ];
    code.resize(0x40, 0xcc);
    code.extend_from_slice(&[
        0x8b, 0x01, // ASM: mov eax, [ecx]
        0x03, 0x44, 0x24, 0x04, // ASM: add eax, [esp+4]
        0x03, 0x44, 0x24, 0x08, // ASM: add eax, [esp+8]
        0xc2, 0x08, 0x00, // ASM: ret 8
    ]);
    code.resize(0x60, 0xcc);
    code.extend_from_slice(&[
        0x31, 0xc0, // ASM: xor eax, eax
        0xc3, // ASM: ret
    ]);
    let text = dc(&code);
    assert!(text.contains("sub_401040(ecx, 9, 7)"), "{text}");
}

/// A word a push only made room for still reaches a callee stated to read
/// it, so the argument pushed above it keeps its place.
///
/// `call 0x401060; push ecx; push 5; push ecx; call 0x401040; ret`, where
/// 0x401040 is `mov eax,[esp+8]; ret 0xc` and 0x401060 `xor eax,eax;
/// ret`: `ecx` holds nothing after the first call, so each `push ecx`
/// only fills a word the callee ignores, the way MSVC passes a parameter
/// nobody reads. The text dropped all three arguments and left the `5` as
/// a dead store, where the machine passes it as the second.
#[test]
fn a_room_making_push_keeps_its_place_among_the_arguments() {
    let mut code = vec![
        0xe8, 0x5b, 0x00, 0x00, 0x00, // ASM: call 0x401060
        0x51, // ASM: push ecx
        0x6a, 0x05, // ASM: push 5
        0x51, // ASM: push ecx
        0xe8, 0x32, 0x00, 0x00, 0x00, // ASM: call 0x401040
        0xc3, // ASM: ret
    ];
    code.resize(0x40, 0xcc);
    code.extend_from_slice(&[
        0x8b, 0x44, 0x24, 0x08, // ASM: mov eax, [esp+8]
        0xc2, 0x0c, 0x00, // ASM: ret 0xc
    ]);
    code.resize(0x60, 0xcc);
    code.extend_from_slice(&[
        0x31, 0xc0, // ASM: xor eax, eax
        0xc3, // ASM: ret
    ]);
    let text = dc(&code);
    let call = text
        .lines()
        .find(|l| l.contains("sub_401040(") && !l.starts_with("static inline "))
        .unwrap_or_default();
    let args = call
        .split_once("sub_401040(")
        .and_then(|(_, rest)| rest.split_once(')'))
        .map(|(args, _)| args.split(", ").collect::<Vec<_>>())
        .unwrap_or_default();
    assert_eq!(args.len(), 3, "{text}");
    assert_eq!(args.get(1), Some(&"5"), "{text}");
}

/// A `__cdecl` call passes every word its caller cleans up after it, past
/// the ones the callee's body reads by name.
///
/// `push 3; push 2; push 1; call 0x401040; add esp,0xc; ret`, where
/// 0x401040 is `mov eax,[esp+4]; lea ecx,[esp+8]; add eax,[ecx]; ret`: a
/// variadic callee that names one argument and walks the rest through
/// its `va_start` pointer. The text passed it two and left the third push
/// as a dead store.
#[test]
fn a_cdecl_call_passes_what_its_caller_cleans_up() {
    let mut code = vec![
        0x6a, 0x03, // ASM: push 3
        0x6a, 0x02, // ASM: push 2
        0x6a, 0x01, // ASM: push 1
        0xe8, 0x35, 0x00, 0x00, 0x00, // ASM: call 0x401040
        0x83, 0xc4, 0x0c, // ASM: add esp, 0xc
        0xc3, // ASM: ret
    ];
    code.resize(0x40, 0xcc);
    code.extend_from_slice(&[
        0x8b, 0x44, 0x24, 0x04, // ASM: mov eax, [esp+4]
        0x8d, 0x4c, 0x24, 0x08, // ASM: lea ecx, [esp+8]
        0x03, 0x01, // ASM: add eax, [ecx]
        0xc3, // ASM: ret
    ]);
    let text = dc(&code);
    assert!(text.contains("sub_401040(1, 2, 3)"), "{text}");
}

/// A `__fastcall` or `__thiscall` function whose `ret` pops nothing takes
/// no stack argument, whatever the function it tail-jumps to reads.
///
/// `sub esp,8; mov dword [esp],9; mov ecx,5; call 0x401040; add esp,8;
/// ret` calls a `__security_check_cookie`: `cmp ecx,[0x402000]; jne F;
/// ret 0; F: jmp 0x401060`, where 0x401060 captures the frame like
/// `__report_gsfailure` (`push ebp; mov ebp,esp; mov [0x402004],ecx; lea
/// eax,[ebp+8]; mov [0x402008],eax; ud2`). Its address of the word above
/// the return address made the check take a stack argument, and the call
/// passed the caller's local at the top of the stack as one. The check is
/// the cookie check by its shape, which preserves every register and
/// takes `ecx` alone, and the text folds it.
#[test]
fn a_callee_popping_nothing_takes_no_stack_argument() {
    let mut code = vec![
        0x83, 0xec, 0x08, // ASM: sub esp, 8
        0xc7, 0x04, 0x24, 0x09, 0x00, 0x00, 0x00, // ASM: mov dword [esp], 9
        0xb9, 0x05, 0x00, 0x00, 0x00, // ASM: mov ecx, 5
        0xe8, 0x2c, 0x00, 0x00, 0x00, // ASM: call 0x401040
        0x83, 0xc4, 0x08, // ASM: add esp, 8
        0xc3, // ASM: ret
    ];
    code.resize(0x40, 0xcc);
    code.extend_from_slice(&[
        0x3b, 0x0d, 0x00, 0x20, 0x40, 0x00, // ASM: cmp ecx, [0x402000]
        0x75, 0x03, // ASM: jne 0x40104b
        0xc2, 0x00, 0x00, // ASM: ret 0
        0xe9, 0x10, 0x00, 0x00, 0x00, // ASM: jmp 0x401060
    ]);
    code.resize(0x60, 0xcc);
    code.extend_from_slice(&[
        0x55, // ASM: push ebp
        0x8b, 0xec, // ASM: mov ebp, esp
        0x89, 0x0d, 0x04, 0x20, 0x40, 0x00, // ASM: mov [0x402004], ecx
        0x8d, 0x45, 0x08, // ASM: lea eax, [ebp+8]
        0xa3, 0x08, 0x20, 0x40, 0x00, // ASM: mov [0x402008], eax
        0x0f, 0x0b, // ASM: ud2
    ]);
    let text = dc(&code);
    assert!(text.contains("// folded: /GS cookie, 1 check"), "{text}");
    assert!(!text.contains('9'), "{text}");
}

/// A 32-bit caller renders the `edx` a callee hands back only where it
/// reads it.
///
/// `mov eax,1; mov edx,2; ret` is called by the entry, which stores `edx`
/// after the call, and by a function that only reads `eax`: the first
/// shows `edx = sub_401040__rdx();`, the second no such line, where the
/// text read the `edx` a call clobbered by its stale name.
#[test]
fn a_32_bit_second_result_renders_where_it_is_read() {
    let mut code = vec![
        0xe8, 0x3b, 0x00, 0x00, 0x00, // ASM: call 0x401040
        0x89, 0x15, 0x00, 0x21, 0x40, 0x00, // ASM: mov [0x402100], edx
        0xe8, 0x10, 0x00, 0x00, 0x00, // ASM: call 0x401020
        0xc3, // ASM: ret
    ];
    code.resize(0x20, 0xcc);
    code.extend_from_slice(&[
        0xe8, 0x1b, 0x00, 0x00, 0x00, // ASM: call 0x401040
        0x40, // ASM: inc eax
        0xc3, // ASM: ret
    ]);
    code.resize(0x40, 0xcc);
    code.extend_from_slice(&[
        0xb8, 0x01, 0x00, 0x00, 0x00, // ASM: mov eax, 1
        0xba, 0x02, 0x00, 0x00, 0x00, // ASM: mov edx, 2
        0xc3, // ASM: ret
    ]);
    let p = image(&code);
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let text = |e| decompile(&p, &a, &o, e).unwrap_or_default();
    let reader = text(0x401000);
    assert!(reader.contains("var1 = sub_401040__rdx();"), "{reader}");
    let other = text(0x401020);
    assert!(!other.contains("__rdx"), "{other}");
}

/// A block whose call renders fewer stack words than its callee reads is
/// not counted as agreeing with the binary: the words the text leaves out
/// are compared with nothing.
///
/// `push esi; push 5; call 0x401040; pop esi; ret` against a callee that
/// reads two words, `mov eax,[esp+4]; add eax,[esp+8]; ret 8`: the word
/// above the `5` is `esi`'s save, which the text never passes, and the
/// header counted the block as checked all the same.
#[test]
fn a_call_dropping_an_argument_is_left_unchecked() {
    use borer_engine::analysis::decompile::checked_header;
    let mut code = vec![
        0x56, // ASM: push esi
        0x6a, 0x05, // ASM: push 5
        0xe8, 0x38, 0x00, 0x00, 0x00, // ASM: call 0x401040
        0x5e, // ASM: pop esi
        0xc3, // ASM: ret
    ];
    code.resize(0x40, 0xcc);
    code.extend_from_slice(&[
        0x8b, 0x44, 0x24, 0x04, // ASM: mov eax, [esp+4]
        0x03, 0x44, 0x24, 0x08, // ASM: add eax, [esp+8]
        0xc2, 0x08, 0x00, // ASM: ret 8
    ]);
    let p = image(&code);
    let a = Analysis::compute(&p);
    let header = checked_header(&p, &a, &Overlay::default(), 0x401000).unwrap_or_default();
    assert!(header.contains("1 call args dropped"), "{header}");
}

/// A read inside a stack parameter's word reaches those bytes of the
/// parameter.
///
/// msvcrt's `_finite` is `push ebp; mov ebp,esp; movzx ecx,word [ebp+0xe];
/// xor eax,eax; and ecx,0x7ff0; cmp ecx,0x7ff0; setne al; pop ebp; ret`:
/// the word is the top of its double's high half, the second stack word.
/// The text read it as `arg_6`, a variable of its own nothing set.
#[test]
fn a_read_inside_a_stack_parameter_reads_the_parameter() {
    let text = dc(&[
        0x55, // ASM: push ebp
        0x8b, 0xec, // ASM: mov ebp, esp
        0x0f, 0xb7, 0x4d, 0x0e, // ASM: movzx ecx, word [ebp+0xe]
        0x33, 0xc0, // ASM: xor eax, eax
        0x81, 0xe1, 0xf0, 0x7f, 0x00, 0x00, // ASM: and ecx, 0x7ff0
        0x81, 0xf9, 0xf0, 0x7f, 0x00, 0x00, // ASM: cmp ecx, 0x7ff0
        0x0f, 0x95, 0xc0, // ASM: setne al
        0x5d, // ASM: pop ebp
        0xc3, // ASM: ret
    ]);
    assert!(text.contains("*(uint16_t*)((uint8_t*)&a2 + 2)"), "{text}");
    assert!(!text.contains("arg_6"), "{text}");
}

/// A call chain reaches an import called through its slot, the call of
/// the import its last link: with no function at the slot it was refused.
#[test]
fn a_call_path_reaches_an_import_through_its_slot() {
    use borer_engine::analysis::render::call_path;
    let p = import_call_image();
    let a = Analysis::compute(&p);
    let out = call_path(&p, &a, &Overlay::default(), 0x401000, 0x402000, 24);
    assert!(
        out.starts_with("# sub_401000 reaches GetTickCount in 2 call(s)"),
        "{out}"
    );
    assert!(out.contains("  2  0x402000  GetTickCount\n"), "{out}");
}

/// A callgraph cut by its node budget counts every callee it left out,
/// those the first round refused included: three callees under a budget
/// of two nodes drew one and said nothing of the other two.
#[test]
fn a_callgraph_counts_every_callee_it_leaves_out() {
    use borer_engine::analysis::render::callgraph_mermaid;
    let mut code = vec![0xcc; 0x41];
    code[..0x10].copy_from_slice(&[
        0xe8, 0x1b, 0x00, 0x00, 0x00, 0xe8, 0x26, 0x00, 0x00, 0x00, 0xe8, 0x31, 0x00, 0x00, 0x00,
        0xc3,
    ]);
    for at in [0x20, 0x30, 0x40] {
        code[at] = 0xc3;
    }
    let p = image(&code);
    let a = Analysis::compute(&p);
    assert_eq!(a.function(0x401000).map(|f| f.callees.len()), Some(3));
    let out = callgraph_mermaid(&p, &a, &Overlay::default(), 0x401000, 2, false);
    assert!(
        out.contains("(callees of the root; cap 2, 2 callees not shown)"),
        "{out}"
    );
}

/// An argument pushed for a call through a register renders once, at the
/// call, not as a slot store before it as well.
///
/// `mov edi,[0x402100]; push 0x402000; call edi; ret`, the slot holding
/// `QString::contains(char const *)` and `"AID"` at 0x402000.
#[test]
fn an_argument_of_a_call_through_a_register_renders_once() {
    let mut data = vec![0u8; 0x110];
    data[..4].copy_from_slice(b"AID\0");
    let mut p = image_with_data(
        &[
            0x8b, 0x3d, 0x00, 0x21, 0x40, 0x00, 0x68, 0x00, 0x20, 0x40, 0x00, 0xff, 0xd7, 0xc3,
        ],
        &data,
    );
    p.symbols = vec![Symbol {
        name: "Qt5Core.dll!?contains@QString@@QBE_NPBD@Z".to_owned(),
        addr: 0x402100,
        kind: SymbolKind::Import,
    }];
    let text = decompiled(&p, 0x401000);
    assert!(text.contains("contains("), "{text}");
    assert_eq!(text.matches("\"AID\"").count(), 1, "{text}");
}

/// Once a local's address has escaped, an argument pushed for a later
/// call still renders once, at the call, not as a slot store first.
///
/// `push ebp; mov ebp,esp; sub esp,0x10; lea eax,[ebp-0x10]; push eax;
/// call 0x401030; add esp,4; push 0x402000; push 1; call 0x401040; add
/// esp,8; leave; ret`, with `"AID"` at 0x402000, a callee reading one
/// argument at 0x401030 and one adding its two at 0x401040.
#[test]
fn an_argument_after_an_escape_renders_once() {
    let mut code = vec![
        0x55, 0x8b, 0xec, 0x83, 0xec, 0x10, 0x8d, 0x45, 0xf0, 0x50, 0xe8, 0x21, 0x00, 0x00, 0x00,
        0x83, 0xc4, 0x04, 0x68, 0x00, 0x20, 0x40, 0x00, 0x6a, 0x01, 0xe8, 0x22, 0x00, 0x00, 0x00,
        0x83, 0xc4, 0x08, 0xc9, 0xc3,
    ];
    code.resize(0x30, 0xcc);
    code.extend_from_slice(&[0x8b, 0x44, 0x24, 0x04, 0xc3]);
    code.resize(0x40, 0xcc);
    code.extend_from_slice(&[0x8b, 0x44, 0x24, 0x04, 0x03, 0x44, 0x24, 0x08, 0xc3]);
    let p = image_with_data(&code, b"AID\0");
    let text = decompiled(&p, 0x401000);
    assert!(text.contains("sub_401040(1, \"AID\")"), "{text}");
    assert_eq!(text.matches("\"AID\"").count(), 1, "{text}");
}

/// A copy into `ecx` made for a callee that reads it survives the write
/// to the register it copied, in a function whose own convention passes
/// nothing in registers.
///
/// A loop over an array of objects, calling a method on each non-null
/// one: `push ebp; mov ebp,esp; push esi; mov esi,[ebp+8]; jmp L2; L1:
/// mov ecx,esi; add esi,16; test ecx,ecx; je L2; call 0x401040; L2: cmp
/// esi,[ebp+12]; jne L1; pop esi; pop ebp; ret 8`, with the callee `mov
/// eax,[ecx]; ret`.
#[test]
fn a_copy_into_ecx_for_a_thiscall_callee_survives_the_sources_write() {
    let mut code = vec![
        0x55, 0x8b, 0xec, 0x56, 0x8b, 0x75, 0x08, 0xeb, 0x0e, 0x8b, 0xce, 0x83, 0xc6, 0x10, 0x85,
        0xc9, 0x74, 0x05, 0xe8, 0x29, 0x00, 0x00, 0x00, 0x3b, 0x75, 0x0c, 0x75, 0xed, 0x5e, 0x5d,
        0xc2, 0x08, 0x00,
    ];
    code.resize(0x40, 0xcc);
    code.extend_from_slice(&[0x8b, 0x01, 0xc3]);
    let p = image(&code);
    let text = decompiled(&p, 0x401000);
    assert!(
        text.lines()
            .any(|l| l.trim().starts_with("var2 = ") && l.trim().ends_with("= var1;")),
        "{text}"
    );
    assert!(text.contains("sub_401040(var2)"), "{text}");
}

/// `push ecx` after a call, the register clobbered and holding nothing,
/// makes room for a local and is not a store of `ecx`; the local's
/// address is what the next call gets.
///
/// `push ebp; mov ebp,esp; sub esp,8; call 0x401030; push ecx; lea
/// eax,[esp]; push eax; call 0x401040; add esp,8; leave; ret`, with the
/// callees `xor eax,eax; ret` and `mov eax,[esp+4]; mov eax,[eax]; ret`.
#[test]
fn a_push_of_a_clobbered_register_makes_room_and_stores_nothing() {
    let mut code = vec![
        0x55, 0x8b, 0xec, 0x83, 0xec, 0x08, 0xe8, 0x25, 0x00, 0x00, 0x00, 0x51, 0x8d, 0x04, 0x24,
        0x50, 0xe8, 0x2b, 0x00, 0x00, 0x00, 0x83, 0xc4, 0x08, 0xc9, 0xc3,
    ];
    code.resize(0x30, 0xcc);
    code.extend_from_slice(&[0x33, 0xc0, 0xc3]);
    code.resize(0x40, 0xcc);
    code.extend_from_slice(&[0x8b, 0x44, 0x24, 0x04, 0x8b, 0x00, 0xc3]);
    let text = dc(&code);
    assert!(!text.contains("= ecx"), "{text}");
    assert!(text.contains("sub_401040(&local_"), "{text}");
}

/// A push of `ecx` the function set is the argument it is, even once the
/// value was written out under the register's own name and the register
/// holds nothing pending.
///
/// `mov eax,[esp+4]; mov ebx,[esp+8]; mov ecx,[eax+ebx*4+8]; mov edx,[ecx];
/// push ecx; push edx; call 0x401030; add esp,8; ret`: the load into `ecx`
/// is too long to inline twice, so it is written out before its two
/// reads; the callee adds its two arguments.
#[test]
fn a_push_of_a_written_out_register_is_an_argument() {
    let mut code = vec![
        0x8b, 0x44, 0x24, 0x04, 0x8b, 0x5c, 0x24, 0x08, 0x8b, 0x4c, 0x98, 0x08, 0x8b, 0x11, 0x51,
        0x52, 0xe8, 0x1b, 0x00, 0x00, 0x00, 0x83, 0xc4, 0x08, 0xc3,
    ];
    code.resize(0x30, 0xcc);
    code.extend_from_slice(&[0x8b, 0x44, 0x24, 0x04, 0x03, 0x44, 0x24, 0x08, 0xc3]);
    let text = dc(&code);
    assert!(text.contains("var1 = ((uint32_t*)(a1 + 8))[a2];"), "{text}");
    assert!(
        text.contains("sub_401030(*(uint32_t*)var1, var1)"),
        "{text}"
    );
}

/// A function that passes `ecx` on untouched is a method.
///
/// Whether it passes it to a callee that reads it or to an import whose
/// prototype takes `this`, `this` is its first parameter, named at the
/// call it forwards to, and a jump through the import's slot passes the
/// stack arguments on as well.
///
/// `push ebp; mov ebp,esp; push ecx; push [ebp+8]; and [ebp-4],0; call
/// 0x401030; mov eax,[ebp+8]; leave; ret 4` with the callee `mov
/// eax,[ecx]; add eax,[esp+4]; ret 4`; and `push ebp; mov ebp,esp; pop
/// ebp; jmp [0x402000]` with `QWidget::setWindowTitle` at that slot.
#[test]
fn a_wrapper_forwarding_ecx_untouched_takes_this() {
    let mut code = vec![
        0x55, 0x8b, 0xec, 0x51, 0xff, 0x75, 0x08, 0x83, 0x65, 0xfc, 0x00, 0xe8, 0x20, 0x00, 0x00,
        0x00, 0x8b, 0x45, 0x08, 0xc9, 0xc2, 0x04, 0x00,
    ];
    code.resize(0x30, 0xcc);
    code.extend_from_slice(&[0x8b, 0x01, 0x03, 0x44, 0x24, 0x04, 0xc2, 0x04, 0x00]);
    let text = dc(&code);
    assert!(text.contains("(void *this, uint32_t a2)"), "{text}");
    assert!(text.contains("sub_401030(this, a2)"), "{text}");
    let text = dc_with(
        &[0x55, 0x8b, 0xec, 0x5d, 0xff, 0x25, 0x00, 0x20, 0x40, 0x00],
        &[(
            0x402000,
            "Qt5Widgets.dll!?setWindowTitle@QWidget@@QAEXABVQString@@@Z",
        )],
    );
    assert!(text.contains("(void *this, uint32_t a2)"), "{text}");
    assert!(text.contains("QWidget::setWindowTitle(this, a2)"), "{text}");
}

/// A `push ecx` the next call takes as an argument reads `this`, so a
/// signal emitter is a method and its pushes are the call's arguments.
///
/// `push 0; push 0; push 0x402000; push ecx; call [0x402100]; add
/// esp,0x10; ret` with `QMetaObject::activate(QObject *, const
/// QMetaObject *, int, void **)` at the slot.
#[test]
fn a_push_the_call_consumes_reads_this() {
    let code = [
        0x6a, 0x00, 0x6a, 0x00, 0x68, 0x00, 0x20, 0x40, 0x00, 0x51, 0xff, 0x15, 0x00, 0x21, 0x40,
        0x00, 0x83, 0xc4, 0x10, 0xc3,
    ];
    let mut p = image_with_data(&code, &[0u8; 0x110]);
    p.symbols = vec![Symbol {
        name: "Qt5Core.dll!?activate@QMetaObject@@SAXPAVQObject@@PBU1@HPAPAX@Z".to_owned(),
        addr: 0x402100,
        kind: SymbolKind::Import,
    }];
    let text = decompiled(&p, 0x401000);
    assert!(text.contains("(void *this)"), "{text}");
    assert!(text.contains("QMetaObject::activate(this, "), "{text}");
    assert!(!text.contains("= ecx"), "{text}");
}

/// A function's stack arguments are counted from where the stack pointer
/// stood at each read, so the pushes its body makes for its own calls do
/// not turn its arguments into locals.
///
/// The callee at 0x401040, `push ebp; mov ebp,esp; mov ecx,[ebp+0xc];
/// push 1; push [ebp+8]; call 0x401060; add esp,8; pop ebp; ret`, reads
/// two arguments; the caller `push 2; push 1; call 0x401040; add esp,8;
/// ret` shows both.
#[test]
fn body_pushes_do_not_hide_a_callees_arguments() {
    let mut code = vec![
        0x6a, 0x02, 0x6a, 0x01, 0xe8, 0x37, 0x00, 0x00, 0x00, 0x83, 0xc4, 0x08, 0xc3,
    ];
    code.resize(0x40, 0xcc);
    code.extend_from_slice(&[
        0x55, 0x8b, 0xec, 0x8b, 0x4d, 0x0c, 0x6a, 0x01, 0xff, 0x75, 0x08, 0xe8, 0x10, 0x00, 0x00,
        0x00, 0x83, 0xc4, 0x08, 0x5d, 0xc3,
    ]);
    code.resize(0x60, 0xcc);
    code.extend_from_slice(&[0x8b, 0x44, 0x24, 0x04, 0x03, 0x44, 0x24, 0x08, 0xc3]);
    let p = image(&code);
    let a = Analysis::compute(&p);
    assert_eq!(a.function(0x401040).map(|f| f.stack_args), Some(2));
    let text = decompile(&p, &a, &Overlay::default(), 0x401000).unwrap_or_default();
    assert!(text.contains("sub_401040(1, 2)"), "{text}");
}

/// A caller passes `this` to a signal emitter, whose only read of `ecx`
/// is the push its call to `activate` consumes.
///
/// The caller `mov ecx,[esp+4]; call 0x401040; ret` calls the emitter
/// `push 0; push 0; push 0x402000; push ecx; call [0x402100]; add
/// esp,0x10; ret`, with `QMetaObject::activate` at the slot.
#[test]
fn a_caller_passes_this_to_an_emitter() {
    let mut code = vec![0x8b, 0x4c, 0x24, 0x04, 0xe8, 0x37, 0x00, 0x00, 0x00, 0xc3];
    code.resize(0x40, 0xcc);
    code.extend_from_slice(&[
        0x6a, 0x00, 0x6a, 0x00, 0x68, 0x00, 0x20, 0x40, 0x00, 0x51, 0xff, 0x15, 0x00, 0x21, 0x40,
        0x00, 0x83, 0xc4, 0x10, 0xc3,
    ]);
    let mut p = image_with_data(&code, &[0u8; 0x110]);
    p.symbols = vec![Symbol {
        name: "Qt5Core.dll!?activate@QMetaObject@@SAXPAVQObject@@PBU1@HPAPAX@Z".to_owned(),
        addr: 0x402100,
        kind: SymbolKind::Import,
    }];
    let text = decompiled(&p, 0x401000);
    assert!(text.contains("sub_401040(a1)"), "{text}");
}

/// A call to an import nothing declares a prototype for takes what the
/// caller pushed for it, as a call to an unknown callee does.
///
/// `push 3; push 2; push 1; call [0x402100]; ret` with `WinVerifyTrust`
/// at the slot, a `stdcall` import no table declares.
#[test]
fn an_undeclared_import_takes_what_was_pushed() {
    let text = dc_with(
        &[
            0x6a, 0x03, 0x6a, 0x02, 0x6a, 0x01, 0xff, 0x15, 0x00, 0x21, 0x40, 0x00, 0xc3,
        ],
        &[(0x402100, "wintrust.dll!WinVerifyTrust")],
    );
    assert!(text.contains("WinVerifyTrust(1, 2, 3)"), "{text}");
}

/// A function that loads `ecx` itself before a call to a method takes no
/// `this`, and the `push ecx` making room after the frame helper stores
/// nothing.
///
/// `mov eax,0; call 0x401040; push ecx; mov ecx,[ebp+8]; call 0x401060;
/// mov ecx,[ebp-0xc]; mov fs:[0],ecx; leave; ret 4`, with the helper at
/// 0x401040 and the callee `mov eax,[ecx]; ret` at 0x401060.
#[test]
fn a_function_loading_ecx_for_a_method_takes_no_this() {
    let mut code = vec![
        0xb8, 0x00, 0x00, 0x00, 0x00, 0xe8, 0x36, 0x00, 0x00, 0x00, 0x51, 0x8b, 0x4d, 0x08, 0xe8,
        0x4d, 0x00, 0x00, 0x00, 0x8b, 0x4d, 0xf4, 0x64, 0x89, 0x0d, 0x00, 0x00, 0x00, 0x00, 0xc9,
        0xc2, 0x04, 0x00,
    ];
    code.resize(0x40, 0xcc);
    code.extend_from_slice(&SEH_PROLOG4);
    code.resize(0x60, 0xcc);
    code.extend_from_slice(&[0x8b, 0x01, 0xc3]);
    let p = image(&code);
    let text = decompiled(&p, 0x401000);
    assert!(text.contains("sub_401000(uint32_t a1)"), "{text}");
    assert!(text.contains("sub_401060(a1)"), "{text}");
    assert!(!text.contains("= ecx;"), "{text}");
}

/// An indirect call to an unknown callee takes and pops what was pushed
/// for it.
///
/// With no `add esp` after the call the callee popped its arguments, so a
/// join after it agrees on the stack pointer and the next call keeps its
/// arguments; and the pointer a parameter holds is called as that pointer,
/// not as a method of the parameter's slot.
///
/// `push ebp; mov ebp,esp; sub esp,0x20; mov esi,[ebp+8]; test esi,esi;
/// jz L; lea eax,[ebp-8]; push eax; call [esi]; L: push 0x402000;
/// lea eax,[ebp-0x10]; push eax; call 0x401040; add esp,8; leave; ret 4`,
/// with `push ebp; mov ebp,esp; mov eax,[ebp+8]; add eax,[ebp+0xc]; pop
/// ebp; ret` at 0x401040 and `"AID"` at 0x402000.
#[test]
fn an_unknown_callee_pops_its_arguments_so_the_join_keeps_the_stack() {
    let mut code = vec![
        0x55, 0x8b, 0xec, 0x83, 0xec, 0x20, 0x8b, 0x75, 0x08, 0x85, 0xf6, 0x74, 0x06, 0x8d, 0x45,
        0xf8, 0x50, 0xff, 0x16, 0x68, 0x00, 0x20, 0x40, 0x00, 0x8d, 0x45, 0xf0, 0x50, 0xe8, 0x1f,
        0x00, 0x00, 0x00, 0x83, 0xc4, 0x08, 0xc9, 0xc2, 0x04, 0x00,
    ];
    code.resize(0x40, 0xcc);
    code.extend_from_slice(&[
        0x55, 0x8b, 0xec, 0x8b, 0x45, 0x08, 0x03, 0x45, 0x0c, 0x5d, 0xc3,
    ]);
    let p = image_with_data(&code, b"AID\0");
    let text = decompiled(&p, 0x401000);
    assert!(text.contains("sub_401040(&local_"), "{text}");
    assert!(text.contains("\"AID\")"), "{text}");
    assert!(text.contains("(&local_8)"), "{text}");
    assert!(!text.contains("(&a1)"), "{text}");
}

/// A method returning a class by value takes a hidden pointer the caller
/// pushes and the callee pops; counted, the stack pointer agrees at the
/// join after the call and the next call keeps its arguments.
///
/// `push ebp; mov ebp,esp; sub esp,0x10; mov eax,[ebp+8]; test eax,eax;
/// jz L; lea ecx,[ebp-4]; push ecx; mov ecx,eax; call [0x402100]; L: push 2;
/// push 1; call 0x401040; add esp,8; leave; ret 4`, the slot holding
/// `QString QVariant::toString() const`, and `mov eax,[ebp+8]; add
/// eax,[ebp+0xc]` behind a frame at 0x401040.
#[test]
fn a_hidden_return_pointer_is_a_stack_argument_the_callee_pops() {
    let mut code = vec![
        0x55, 0x8b, 0xec, 0x83, 0xec, 0x10, 0x8b, 0x45, 0x08, 0x85, 0xc0, 0x74, 0x0c, 0x8d, 0x4d,
        0xfc, 0x51, 0x8b, 0xc8, 0xff, 0x15, 0x00, 0x21, 0x40, 0x00, 0x6a, 0x02, 0x6a, 0x01, 0xe8,
        0x1e, 0x00, 0x00, 0x00, 0x83, 0xc4, 0x08, 0xc9, 0xc2, 0x04, 0x00,
    ];
    code.resize(0x40, 0xcc);
    code.extend_from_slice(&[
        0x55, 0x8b, 0xec, 0x8b, 0x45, 0x08, 0x03, 0x45, 0x0c, 0x5d, 0xc3,
    ]);
    let text = dc_with(
        &code,
        &[(
            0x402100,
            "Qt5Core.dll!?toString@QVariant@@QBE?AVQString@@XZ",
        )],
    );
    assert!(text.contains("sub_401040(1, 2)"), "{text}");
    assert!(text.contains("toString(a1, &local_"), "{text}");
}

/// A tail jump forwards the caller's own stack arguments: the callee's
/// first argument is the word above the return address the jump leaves.
///
/// The caller: `push ebp; mov ebp,esp; mov byte [ecx+8],1; pop ebp;
/// jmp 0x401010`; the callee: `mov eax,[esp+4]; ret 4`, made a function
/// of its own by a `call` from 0x401020.
#[test]
fn a_tail_jump_forwards_the_callers_stack_argument() {
    let mut code = vec![
        0x55, 0x8b, 0xec, 0xc6, 0x41, 0x08, 0x01, 0x5d, 0xe9, 0x03, 0x00, 0x00, 0x00,
    ];
    code.resize(0x10, 0xcc);
    code.extend_from_slice(&[0x8b, 0x44, 0x24, 0x04, 0xc2, 0x04, 0x00]);
    code.resize(0x20, 0xcc);
    code.extend_from_slice(&[0xe8, 0xeb, 0xff, 0xff, 0xff, 0xc3]);
    let text = dc(&code);
    assert!(text.contains("return sub_401010(a2);"), "{text}");
}

/// A function adding its two stack arguments names both as parameters.
///
/// `push ebp; mov ebp,esp; mov eax,[ebp+8]; add eax,[ebp+0xc]; pop ebp; ret`.
/// The first argument sits four bytes above the entry stack pointer, not
/// eight, so it is the first parameter and not a slot named by a negative
/// offset.
#[test]
fn cdecl_stack_arguments_are_parameters() {
    let text = dc(&[
        0x55, 0x8b, 0xec, 0x8b, 0x45, 0x08, 0x03, 0x45, 0x0c, 0x5d, 0xc3,
    ]);
    assert!(text.contains("return a1 + a2;"), "{text}");
    assert!(text.contains("a1, "), "{text}");
    assert!(text.contains("a2)"), "{text}");
    assert!(!text.contains("arg_"), "{text}");
}

/// A word pushed before an unknown call that the next call pops is that
/// call's argument: the unknown callee takes nothing, the stack pointer
/// agrees at the join, and the call after it keeps its argument.
///
/// `push esi; mov esi,ecx; test esi,esi; jz L; push 0x402000; mov ecx,esi;
/// mov eax,[esi]; call [eax]; mov ecx,eax; call 0x401040; L: push 7;
/// call 0x401050; pop ecx; pop esi; ret`, where 0x401040 is `mov eax,
/// [esp+4]; cmp eax,[ecx]; sete al; ret 4` and 0x401050 `mov eax,[esp+4];
/// ret`.
#[test]
fn a_word_the_next_call_pops_is_not_the_unknown_callees() {
    let mut code = vec![
        0x56, 0x8b, 0xf1, 0x85, 0xf6, 0x74, 0x12, 0x68, 0x00, 0x20, 0x40, 0x00, 0x8b, 0xce, 0x8b,
        0x06, 0xff, 0x10, 0x8b, 0xc8, 0xe8, 0x27, 0x00, 0x00, 0x00, 0x6a, 0x07, 0xe8, 0x30, 0x00,
        0x00, 0x00, 0x59, 0x5e, 0xc3,
    ];
    code.resize(0x40, 0xcc);
    code.extend_from_slice(&[
        0x8b, 0x44, 0x24, 0x04, 0x3b, 0x01, 0x0f, 0x94, 0xc0, 0xc2, 0x04, 0x00,
    ]);
    code.resize(0x50, 0xcc);
    code.extend_from_slice(&[0x8b, 0x44, 0x24, 0x04, 0xc3]);
    let text = dc(&code);
    assert!(text.contains("sub_401050(7)"), "{text}");
    assert!(!text.contains("asm"), "{text}");
}

/// A `__cdecl` call through a pointer whose arguments the caller pops
/// together with the next call's keeps them: it pops nothing itself, and
/// the stack pointer agrees at the join.
///
/// `push ebp; mov ebp,esp; mov eax,[ebp+8]; test eax,eax; jz L; push 2;
/// push 1; call eax; push 3; call 0x401050; add esp,0xc; L: push 5;
/// call 0x401050; pop ecx; pop ebp; ret`, with `mov eax,[esp+4]; ret` at
/// 0x401050.
#[test]
fn a_cdecl_cleanup_after_the_next_call_keeps_the_stack() {
    let mut code = vec![
        0x55, 0x8b, 0xec, 0x8b, 0x45, 0x08, 0x85, 0xc0, 0x74, 0x10, 0x6a, 0x02, 0x6a, 0x01, 0xff,
        0xd0, 0x6a, 0x03, 0xe8, 0x39, 0x00, 0x00, 0x00, 0x83, 0xc4, 0x0c, 0x6a, 0x05, 0xe8, 0x2f,
        0x00, 0x00, 0x00, 0x59, 0x5d, 0xc3,
    ];
    code.resize(0x50, 0xcc);
    code.extend_from_slice(&[0x8b, 0x44, 0x24, 0x04, 0xc3]);
    let text = dc(&code);
    assert!(text.contains("(1, 2)"), "{text}");
    assert!(text.contains("sub_401050(3)"), "{text}");
    assert!(text.contains("sub_401050(5)"), "{text}");
}

/// A callee that ends in a jump to another function pops what that
/// function's `ret` pops.
///
/// `push esi; mov esi,ecx; test esi,esi; jz L; push 1; mov ecx,esi;
/// call 0x401040; L: push 9; call 0x401060; pop ecx; pop esi; ret`, with
/// `mov eax,ecx; jmp 0x401050` at 0x401040, `mov eax,[esp+4]; ret 4` at
/// 0x401050 (a function of its own by the `call` at 0x401070) and
/// `mov eax,[esp+4]; ret` at 0x401060.
#[test]
fn a_callee_ending_in_a_jump_pops_what_its_target_pops() {
    let mut code = vec![
        0x56, 0x8b, 0xf1, 0x85, 0xf6, 0x74, 0x09, 0x6a, 0x01, 0x8b, 0xce, 0xe8, 0x30, 0x00, 0x00,
        0x00, 0x6a, 0x09, 0xe8, 0x49, 0x00, 0x00, 0x00, 0x59, 0x5e, 0xc3,
    ];
    code.resize(0x40, 0xcc);
    code.extend_from_slice(&[0x8b, 0xc1, 0xe9, 0x09, 0x00, 0x00, 0x00]);
    code.resize(0x50, 0xcc);
    code.extend_from_slice(&[0x8b, 0x44, 0x24, 0x04, 0xc2, 0x04, 0x00]);
    code.resize(0x60, 0xcc);
    code.extend_from_slice(&[0x8b, 0x44, 0x24, 0x04, 0xc3]);
    code.resize(0x70, 0xcc);
    code.extend_from_slice(&[0xe8, 0xdb, 0xff, 0xff, 0xff, 0xc3]);
    let text = dc(&code);
    assert!(text.contains("sub_401060(9)"), "{text}");
}

/// Room a `sub esp` makes before an unknown call is that call's to pop,
/// as a structure passed by value is.
///
/// `push esi; mov esi,ecx; test esi,esi; jz L; sub esp,8; mov dword
/// [esp],1; mov dword [esp+4],2; mov ecx,esi; mov eax,[esi]; call [eax];
/// L: push 9; call 0x401060; pop ecx; pop esi; ret`, with `mov eax,
/// [esp+4]; ret` at 0x401060.
#[test]
fn room_made_for_an_argument_is_the_calls_to_pop() {
    let mut code = vec![
        0x56, 0x8b, 0xf1, 0x85, 0xf6, 0x74, 0x18, 0x83, 0xec, 0x08, 0xc7, 0x04, 0x24, 0x01, 0x00,
        0x00, 0x00, 0xc7, 0x44, 0x24, 0x04, 0x02, 0x00, 0x00, 0x00, 0x8b, 0xce, 0x8b, 0x06, 0xff,
        0x10, 0x6a, 0x09, 0xe8, 0x3a, 0x00, 0x00, 0x00, 0x59, 0x5e, 0xc3,
    ];
    code.resize(0x60, 0xcc);
    code.extend_from_slice(&[0x8b, 0x44, 0x24, 0x04, 0xc3]);
    let text = dc(&code);
    assert!(text.contains("sub_401060(9)"), "{text}");
}

/// `push 8; pop eax` loads a constant: the word it pushed is no argument
/// of the next call.
///
/// `push esi; mov esi,ecx; test esi,esi; jz L; push 1; push 8; pop eax;
/// mov ecx,esi; mov edx,[esi]; call [edx]; L: push 9; call 0x401060;
/// pop ecx; pop esi; ret`, with `mov eax,[esp+4]; ret` at 0x401060.
#[test]
fn a_push_popped_into_a_register_is_no_argument() {
    let mut code = vec![
        0x56, 0x8b, 0xf1, 0x85, 0xf6, 0x74, 0x0b, 0x6a, 0x01, 0x6a, 0x08, 0x58, 0x8b, 0xce, 0x8b,
        0x16, 0xff, 0x12, 0x6a, 0x09, 0xe8, 0x47, 0x00, 0x00, 0x00, 0x59, 0x5e, 0xc3,
    ];
    code.resize(0x60, 0xcc);
    code.extend_from_slice(&[0x8b, 0x44, 0x24, 0x04, 0xc3]);
    let text = dc(&code);
    assert!(text.contains("](1)"), "{text}");
    assert!(text.contains("sub_401060(9)"), "{text}");
}

/// A compare that drops the last value on the x87 stack reads nothing the
/// caller handed over.
///
/// `fcomp` after a minimum pops what is left against an empty `st1`, so
/// the function below takes nothing off the stack and returns the byte it
/// sets, never a float: `fld dword [esp+4]; fld dword [esp+8]; fcomi st1;
/// fcmovnb st1; mov eax,[esp+12]; fstp dword [eax]; fcomp st1; mov al,1;
/// ret`, a shape seen in a real 32-bit game client.
#[test]
fn a_compare_that_pops_takes_nothing_off_the_stack() {
    let text = dc(&[
        0xd9, 0x44, 0x24, 0x04, // ASM: fld dword [esp+4]
        0xd9, 0x44, 0x24, 0x08, // ASM: fld dword [esp+8]
        0xdb, 0xf1, // ASM: fcomi st1
        0xdb, 0xd1, // ASM: fcmovnb st1
        0x8b, 0x44, 0x24, 0x0c, // ASM: mov eax,[esp+12]
        0xd9, 0x18, // ASM: fstp dword [eax]
        0xd8, 0xd9, // ASM: fcomp st1
        0xb0, 0x01, // ASM: mov al,1
        0xc3, // ASM: ret
    ]);
    assert!(!text.contains("double sub_401000"), "{text}");
    assert!(text.contains("return 1;"), "{text}");
}

/// A compare whose status is read after a call compares against the
/// call's result, and keeps it bound.
///
/// `mov ecx,[esp+4]; mov eax,[ecx]; call [eax+8]; fld dword [esp+8]; fcom;
/// fnstsw ax; fstp st1; fstp st0; test ah,0x41; sete al; ret`, the shape
/// of d3dx9's 0x1002f977, tests the value against what the virtual call
/// returned.
#[test]
fn a_compare_after_a_call_reads_its_result() {
    let text = dc(&[
        0x8b, 0x4c, 0x24, 0x04, // ASM: mov ecx,[esp+4]
        0x8b, 0x01, // ASM: mov eax,[ecx]
        0xff, 0x50, 0x08, // ASM: call [eax+8]
        0xd9, 0x44, 0x24, 0x08, // ASM: fld dword [esp+8]
        0xd8, 0xd1, // ASM: fcom
        0xdf, 0xe0, // ASM: fnstsw ax
        0xdd, 0xd9, // ASM: fstp st1
        0xdd, 0xd8, // ASM: fstp st0
        0xf6, 0xc4, 0x41, // ASM: test ah,0x41
        0x0f, 0x94, 0xc0, // ASM: sete al
        0xc3, // ASM: ret
    ]);
    assert!(text.contains("st0 = (a1)->vtable[2]("), "{text}");
}

/// A word read of a slot a dword store wrote reads the low half of that
/// store, written out first: never the slot's unassigned variable, nor
/// the whole dword.
///
/// `sub esp,8; mov eax,[esp+0xc]; mov [esp],eax; movzx eax,word [esp];
/// add eax,[esp+0xc]; add esp,8; ret`.
#[test]
fn a_narrow_read_of_a_pending_slot_store_masks_it() {
    let text = dc(&[
        0x83, 0xec, 0x08, 0x8b, 0x44, 0x24, 0x0c, 0x89, 0x04, 0x24, 0x0f, 0xb7, 0x04, 0x24, 0x03,
        0x44, 0x24, 0x0c, 0x83, 0xc4, 0x08, 0xc3,
    ]);
    assert!(text.contains("local_4 = a1;"), "{text}");
    assert!(text.contains("return (local_4 & 0xffff) + a1;"), "{text}");
}

/// The zeros pushed for a bitmap that only a computed address reads are
/// stored.
///
/// msvcrt's `strcspn` zeroes 32 bytes with eight `push eax` and sets and
/// tests bits of them through `bts [esp], eax` and `bt [esp], eax`. No
/// slot is read by name, so the pushes were dead stores, and the text set
/// bits of a bitmap it never cleared. The eight words are one array the
/// index reads across, `uint32_t local_28[8]`.
#[test]
fn zeros_pushed_for_a_bitmap_read_through_its_address_are_stored() {
    let code = [
        0x55, // ASM: push ebp
        0x8b, 0xec, // ASM: mov ebp, esp
        0x56, // ASM: push esi
        0x33, 0xc0, // ASM: xor eax, eax
        0x50, 0x50, 0x50, 0x50, 0x50, 0x50, 0x50, 0x50, // ASM: push eax (eight times)
        0x8b, 0x55, 0x0c, // ASM: mov edx, [ebp+0xc]
        0x8d, 0x49, 0x00, // ASM: lea ecx, [ecx]
        0x8a, 0x02, // ASM: mov al, [edx]
        0x0a, 0xc0, // ASM: or al, al
        0x74, 0x09, // ASM: je 0x401023
        0x83, 0xc2, 0x01, // ASM: add edx, 1
        0x0f, 0xab, 0x04, 0x24, // ASM: bts [esp], eax
        0xeb, 0xf1, // ASM: jmp 0x401014
        0x8b, 0x75, 0x08, // ASM: mov esi, [ebp+8]
        0x83, 0xc9, 0xff, // ASM: or ecx, -1
        0x8d, 0x49, 0x00, // ASM: lea ecx, [ecx]
        0x83, 0xc1, 0x01, // ASM: add ecx, 1
        0x8a, 0x06, // ASM: mov al, [esi]
        0x0a, 0xc0, // ASM: or al, al
        0x74, 0x09, // ASM: je 0x40103e
        0x83, 0xc6, 0x01, // ASM: add esi, 1
        0x0f, 0xa3, 0x04, 0x24, // ASM: bt [esp], eax
        0x73, 0xee, // ASM: jae 0x40102c
        0x8b, 0xc1, // ASM: mov eax, ecx
        0x83, 0xc4, 0x20, // ASM: add esp, 0x20
        0x5e, // ASM: pop esi
        0xc9, // ASM: leave
        0xc3, // ASM: ret
    ];
    let text = runs_agree(&image(&code), 0x401000);
    assert!(text.contains("uint32_t local_24[8];"), "{text}");
    assert!(text.contains("local_24[7] = 0"), "{text}");
}

/// A stack parameter read as a word is its low half.
///
/// `mov cx,[ebp+8]; movzx eax,cx; mov ecx,0xffff; cmp ax,cx; je L` tests
/// the low 16 bits of `a1`, as msvcrt's `_putwc_nolock` tests for `WEOF`;
/// the text once named the slot whole, `a1 != 0xffff` of a `uint32_t`,
/// and a word of 0xffff under nonzero high bits took the other branch.
#[test]
fn a_stack_parameter_read_as_a_word_is_its_low_half() {
    let code = [
        0x55, // ASM: push ebp
        0x8b, 0xec, // ASM: mov ebp, esp
        0x66, 0x8b, 0x4d, 0x08, // ASM: mov cx, [ebp+8]
        0x0f, 0xb7, 0xc1, // ASM: movzx eax, cx
        0xb9, 0xff, 0xff, 0x00, 0x00, // ASM: mov ecx, 0xffff
        0x66, 0x3b, 0xc1, // ASM: cmp ax, cx
        0x74, 0x07, // ASM: je 0x40101b
        0xb8, 0x01, 0x00, 0x00, 0x00, // ASM: mov eax, 1
        0x5d, // ASM: pop ebp
        0xc3, // ASM: ret
        0x31, 0xc0, // ASM: xor eax, eax
        0x5d, // ASM: pop ebp
        0xc3, // ASM: ret
    ];
    let text = runs_agree(&image(&code), 0x401000);
    assert!(text.contains("uint16_t a1"), "{text}");
}
