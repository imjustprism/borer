//! 32-bit x86 decompilation.
//!
//! The frame, the arguments and the calls of a `cdecl`/`stdcall`/`thiscall`
//! program, where every argument travels on the
//! stack, the return address is four bytes and `ecx` may be `this`.
//!
//! Every fixture is hand-assembled and lives in a raw image, so each test
//! states the exact instructions it decompiles.

#![expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]

use crate::decompiled;
use crate::raw;

use borer_engine::analysis::decompile::{decompile, decompile_named};
use borer_engine::analysis::{Analysis, Overlay, RefKind, name_of};
use borer_engine::program::{Arch, BinaryFormat, Program, Section, Symbol, SymbolKind};
use decompiled::decompiled;

/// Builds a raw 32-bit image with `code` in `.text` at 0x401000, entered
/// there, and `data` in a read-only `.rdata` at 0x402000.
///
/// # Arguments
///
/// * `code` - The bytes of `.text`.
/// * `data` - The bytes of `.rdata`.
fn image_with_data(code: &[u8], data: &[u8]) -> Program {
    raw::image(Arch::X86, code, data)
}

/// Builds a raw 32-bit image with `code` at 0x401000 and no data.
///
/// # Arguments
///
/// * `code` - The bytes of `.text`.
fn image(code: &[u8]) -> Program {
    image_with_data(code, &[])
}

/// Decompiles `code` at 0x401000 with imports at the slots `imports` name.
///
/// # Arguments
///
/// * `code` - The bytes of `.text`.
/// * `imports` - `(slot, name)` pairs, each an import symbol.
fn dc_with(code: &[u8], imports: &[(u64, &str)]) -> String {
    let mut p = image(code);
    p.symbols = imports
        .iter()
        .map(|(addr, name)| Symbol {
            name: (*name).to_owned(),
            addr: *addr,
            kind: SymbolKind::Import,
        })
        .collect();
    decompiled(&p, 0x401000)
}

/// Decompiles the function at 0x401000 of a raw image holding `code`.
///
/// # Arguments
///
/// * `code` - The bytes of `.text`.
fn dc(code: &[u8]) -> String {
    decompiled(&image(code), 0x401000)
}

/// Decompiles `code` at 0x401000 with `data` at 0x402000 and the overlay
/// names given.
///
/// # Arguments
///
/// * `code` - The bytes of `.text`.
/// * `data` - The bytes of `.rdata`.
/// * `names` - `(address, name)` pairs the overlay names.
fn dc_data(code: &[u8], data: &[u8], names: &[(u64, &str)]) -> String {
    let p = image_with_data(code, data);
    let a = Analysis::compute(&p);
    let mut o = Overlay::default();
    for (addr, name) in names {
        o.names.insert(*addr, (*name).to_owned());
    }
    decompile(&p, &a, &o, 0x401000).unwrap_or_default()
}

/// `fld a; fld b; fcomi st1; fcmovb st1; fstp st1` is `max(a, b)`.
///
/// The compare sets the flags, the conditional move selects on them, and no
/// x87 instruction is left as asm. `fcmovb` moves on below or unordered,
/// so the select tests `!(b >= a)`, which a NaN satisfies, never `b < a`,
/// which it does not.
#[test]
fn x87_compare_and_conditional_move_select() {
    let text = dc(&[
        0xdd, 0x44, 0x24, 0x04, // fld qword [esp+4]
        0xdd, 0x44, 0x24, 0x0c, // fld qword [esp+12]
        0xdb, 0xf1, // fcomi st,st(1)
        0xda, 0xc1, // fcmovb st,st(1)
        0xdd, 0xd9, // fstp st(1)
        0xdd, 0x19, // fstp qword [ecx]
        0xc3, // ret
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

/// A frame aligned with `and esp, -16` keeps its stack pointer: the locals
/// are locals, the argument is read through the entry pointer's copy, and
/// the `pop ecx` after the call is stack cleanup, not asm.
#[test]
fn an_aligned_frame_keeps_its_stack_pointer() {
    let text = dc(&[
        0x53, // push ebx
        0x8b, 0xdc, // mov ebx,esp
        0x83, 0xe4, 0xf0, // and esp,-16
        0x55, // push ebp
        0x8b, 0xec, // mov ebp,esp
        0x83, 0xec, 0x10, // sub esp,16
        0x8b, 0x43, 0x08, // mov eax,[ebx+8]
        0x89, 0x45, 0xfc, // mov [ebp-4],eax
        0xff, 0x75, 0xfc, // push dword [ebp-4]
        0xe8, 0x08, 0x00, 0x00, 0x00, // call f
        0x59, // pop ecx
        0x8b, 0xe5, // mov esp,ebp
        0x5d, // pop ebp
        0x8b, 0xe3, // mov esp,ebx
        0x5b, // pop ebx
        0xc3, // ret
        0x8b, 0x44, 0x24, 0x04, // f: mov eax,[esp+4]
        0x83, 0xc0, 0x01, // add eax,1
        0xc3, // ret
    ]);
    assert!(!text.contains("/* asm"), "{text}");
    assert!(!text.contains("esp"), "{text}");
    assert!(text.contains("(a1)"), "{text}");
}

/// A frame opened with `add esp, -0x2d0` is a frame, not a jump four
/// gigabytes up.
///
/// The 32-bit immediate is signed at its width, so the push after it lands
/// in the frame and the function decompiles at once; the unsigned reading
/// once sent the lifter walking the gap until memory ran out.
#[test]
fn a_negative_add_to_the_stack_pointer_opens_a_frame() {
    let text = dc(&[
        0x55, // push ebp
        0x8b, 0xec, // mov ebp,esp
        0x81, 0xc4, 0x30, 0xfd, 0xff, 0xff, // add esp,-0x2d0
        0x53, // push ebx
        0x8d, 0x85, 0x38, 0xfd, 0xff, 0xff, // lea eax,[ebp-0x2c8]
        0x50, // push eax
        0xe8, 0x06, 0x00, 0x00, 0x00, // call stub
        0x83, 0xc4, 0x04, // add esp,4
        0x5b, // pop ebx
        0xc9, // leave
        0xc3, // ret
        0xc3, // stub: ret
    ]);
    assert!(text.contains("&local_"), "{text}");
    assert!(!text.contains("arg_ff"), "{text}");
}

/// A small 32-bit frame is a frame: `sub esp, 8` sizes it, so the read
/// above it is the first argument and not the third.
///
/// The frame facts took `sub esp, N` only at the immediate widths the
/// decoder gives 64-bit code; an 8-bit immediate in 32-bit code is another
/// width, so the frame went unrecorded and every `[esp+K]` read was placed
/// as if the frame were empty: `[esp+0xc]` over an 8-byte frame counted as
/// the third argument.
#[test]
fn a_small_32_bit_frame_is_a_frame() {
    let code = [
        0x83, 0xec, 0x08, // sub esp,8
        0x8b, 0x44, 0x24, 0x0c, // mov eax,[esp+0xc]
        0x83, 0xc4, 0x08, // add esp,8
        0xc3, // ret
    ];
    let a = Analysis::compute(&image(&code));
    let f = a.function_at(0x401000).expect("the function is discovered");
    assert_eq!(f.stack_args, 1, "{f:?}");
    let text = dc(&code);
    assert!(text.contains("a1"), "{text}");
    assert!(!text.contains("a3"), "{text}");
}

/// A guarded assert names the variable it tests: `if (a1 == 0) {
/// assert("reader.isvalid()", "x.cc", 7); }` makes `a1` `reader` in the
/// signature and the body.
#[test]
fn asserts_name_the_variables_they_test() {
    let p = image_with_data(
        &[
            0x8b, 0x44, 0x24, 0x04, // mov eax,[esp+4]
            0x85, 0xc0, // test eax,eax
            0x75, 0x14, // jnz ok
            0x6a, 0x07, // push 7
            0x68, 0x12, 0x20, 0x40, 0x00, // push 0x402012 (the source path)
            0x68, 0x00, 0x20, 0x40, 0x00, // push 0x402000 (the condition)
            0xe8, 0x06, 0x00, 0x00, 0x00, // call fail
            0x83, 0xc4, 0x0c, // add esp,12
            0x8b, 0x00, // ok: mov eax,[eax]
            0xc3, // ret
            0xc3, // fail: ret
        ],
        b"reader.isvalid()\0\0src/reader.cc\0",
    );
    let a = Analysis::compute(&p);
    let text = decompile_named(&p, &a, &Overlay::default(), 0x401000).unwrap_or_default();
    assert!(text.contains("eax = reader;"), "{text}");
    assert!(
        text.contains(
            "reader)
"
        ),
        "{text}"
    );
    assert!(!text.contains("a1"), "{text}");
}

/// A table whose first entry is zero is an address, not the empty string:
/// `mov eax,[ecx*4+0x402000]; ret` over sixteen zero bytes.
#[test]
fn a_zero_led_table_is_an_address_not_an_empty_string() {
    let text = dc_data(
        &[0x8b, 0x04, 0x8d, 0x00, 0x20, 0x40, 0x00, 0xc3],
        &[0u8; 16],
        &[],
    );
    assert!(text.contains("0x402000"), "{text}");
    assert!(!text.contains("\"\""), "{text}");
}

/// The empty string in a string pool still reads as `""`:
/// `lea eax,[0x402003]; ret` over `"ab\0" "" "cd\0"`.
#[test]
fn an_empty_string_in_a_pool_is_still_a_literal() {
    let text = dc_data(
        &[0x8d, 0x05, 0x03, 0x20, 0x40, 0x00, 0xc3],
        b"ab\0\0cd\0",
        &[],
    );
    assert!(text.contains("return \"\";"), "{text}");
}

/// A global the user named keeps its name where `lea` takes its address,
/// even when a literal could be read there: `lea eax,[0x402000]; ret`
/// over `"abc\0"` with 0x402000 named `greeting`.
#[test]
fn a_named_global_beats_the_literal_at_its_address() {
    let text = dc_data(
        &[0x8d, 0x05, 0x00, 0x20, 0x40, 0x00, 0xc3],
        b"abc\0",
        &[(0x402000, "greeting")],
    );
    assert!(text.contains("&greeting"), "{text}");
}

/// A callee that pops its arguments leaves the caller's stack pointer
/// where it was before the pushes.
///
/// The caller `push 7; call 0x401040; mov eax,[esp-4]; ret` calls
/// `mov eax,[esp+4]; ret 4`. After the call the stack pointer is back at
/// the entry, so `[esp-4]` is the slot four below it, not eight; and the
/// callee's `ret 4` states that it takes one argument.
#[test]
fn a_callee_popping_its_arguments_moves_the_stack_pointer() {
    let mut code = vec![
        0x6a, 0x07, 0xe8, 0x39, 0x00, 0x00, 0x00, 0x8b, 0x44, 0x24, 0xfc, 0xc3,
    ];
    code.resize(0x40, 0xcc);
    code.extend_from_slice(&[0x8b, 0x44, 0x24, 0x04, 0xc2, 0x04, 0x00]);
    let p = image(&code);
    let a = Analysis::compute(&p);
    let callee = a.function(0x401040).expect("callee discovered");
    assert_eq!((callee.stack_pop, callee.stack_args), (4, 1));
    let text = decompile(&p, &a, &Overlay::default(), 0x401000).unwrap_or_default();
    assert!(text.contains("local_4"), "{text}");
    assert!(!text.contains("local_8"), "{text}");
}

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

/// A read far above the frame is not the hundred-millionth argument.
///
/// `mov eax, [esp+0x7ffffff0]; ret` reads a slot half a gigabyte above the
/// return address; the stack-argument count the body shows stops at the
/// cap discovery's frame scan applies, so the signature declares a few
/// dozen parameters at most, not one per word up to the read (a mutant
/// read one at six hundred thousand words, and the parameter list alone
/// was gigabytes).
#[test]
fn a_read_far_above_the_frame_is_not_an_argument() {
    let text = dc(&[0x8b, 0x84, 0x24, 0xf0, 0xff, 0xff, 0x7f, 0xc3]);
    let sig = text
        .lines()
        .find(|l| l.starts_with("// signature: "))
        .unwrap_or_default();
    assert!(sig.matches(',').count() < 40, "{sig}");
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
    assert!(text.contains("local_4"), "{text}");
    assert!(!text.contains("local_c"), "{text}");
    assert!(!text.contains("local_8 = 1;"), "{text}");
    assert!(!text.contains("local_4 = 2;"), "{text}");
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
    assert!(win32.contains("WriteFile(0, 0, 0, 0, 0);"), "{win32}");
    assert!(win32.contains("local_4"), "{win32}");
    let mut three = vec![0x6a, 0x00, 0x6a, 0x00, 0x6a, 0x00];
    three.extend_from_slice(&tail);
    let crt = dc_with(&three, &[(0x402000, "MSVCR100.dll!memset")]);
    assert!(crt.contains("memset(0, 0, 0);"), "{crt}");
    assert!(crt.contains("local_10"), "{crt}");
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

/// An instruction the lifter does not model keeps the `asm` marker on its
/// comment, so a count of unmodeled instructions counts it: the port read
/// `in al,dx; ret`.
#[test]
fn an_unmodeled_instruction_carries_the_asm_marker() {
    // ASM: mov eax, 1; in al, dx; ret: a port read no compiler emits is
    // left as asm, past an opening that makes the entry a function.
    let text = dc(&[0xb8, 0x01, 0x00, 0x00, 0x00, 0xec, 0xc3]);
    assert!(text.contains("/* asm: in al"), "{text}");
}

/// The value passes speak the registers a 32-bit program has: `taint`
/// follows `eax` by default and accepts `ecx`, and `layout` reads through
/// `ecx` by default, on `mov eax,[ecx+4]; mov ebx,eax; ret`.
#[test]
fn taint_and_layout_speak_32_bit_registers() {
    use borer_engine::analysis::render::{layout_tsv, taint_tsv};
    let p = image(&[0x8b, 0x41, 0x04, 0x8b, 0xd8, 0xc3]);
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let taint = taint_tsv(&p, &a, &o, "0x401000").unwrap();
    assert!(taint.starts_with("# eax from"), "{taint}");
    let explicit = taint_tsv(&p, &a, &o, "0x401000,ecx").unwrap();
    assert!(!explicit.contains("not a general register"), "{explicit}");
    let refused = taint_tsv(&p, &a, &o, "0x401000,r8").unwrap_err();
    assert!(refused.contains("use eax..edi"), "{refused}");
    let layout = layout_tsv(&p, &a, &o, "0x401000").unwrap();
    assert!(layout.contains("through ecx"), "{layout}");
    assert!(layout.contains("0x4 "), "{layout}");
}

/// A function a data pointer names is found even when another function's
/// span reaches over it.
///
/// The entry `jmp 0x401100` tail-jumps into a block far below, so its span
/// runs from 0x401000 to 0x401101 and covers 0x401040; the function there,
/// `mov eax,1; ret`, is named only by a pointer in `.rdata`. Its bytes lie
/// in no block of the entry, and a pointer into unclaimed code is a
/// function.
#[test]
fn a_pointer_into_another_functions_span_still_seeds_a_function() {
    let mut code = vec![0xe9, 0xfb, 0x00, 0x00, 0x00];
    code.resize(0x40, 0xcc);
    code.extend_from_slice(&[0xb8, 0x01, 0x00, 0x00, 0x00, 0xc3]);
    code.resize(0x100, 0xcc);
    code.push(0xc3);
    let p = image_with_data(&code, &[0x40, 0x10, 0x40, 0x00]);
    let a = Analysis::compute(&p);
    assert!(
        a.function(0x401040).is_some(),
        "the pointed-to function is missing"
    );
    let text = decompile(&p, &a, &Overlay::default(), 0x401040).unwrap_or_default();
    assert!(text.contains("return 1;"), "{text}");
}

/// A table read through a scaled index, `mov eax,[ecx*4+0x402000]; ret`,
/// is a reference to the table, of the `index` kind: `xrefs` on the table
/// finds the instruction.
#[test]
fn an_indexed_table_read_is_a_reference_to_the_table() {
    use borer_engine::analysis::render::xrefs_tsv;
    let p = image_with_data(
        &[0x8b, 0x04, 0x8d, 0x00, 0x20, 0x40, 0x00, 0xc3],
        &[0u8; 16],
    );
    let a = Analysis::compute(&p);
    let refs = xrefs_tsv(&a, &Overlay::default(), 0x402000, 0, 60, false);
    assert!(refs.contains("# 1 xrefs to 0x402000"), "{refs}");
    assert!(refs.contains("sub_401000: 0x401000 index\n"), "{refs}");
}

/// A conditional tail call, `jne` into another function, is a reference to
/// that function, like the `call` beside it.
///
/// `call 0x401010; test ecx,ecx; jne 0x401010; ret`, padding, then
/// `xor eax,eax; ret` at 0x401010: only the call was listed.
#[test]
fn a_conditional_tail_call_is_a_reference() {
    use borer_engine::analysis::render::xrefs_tsv;
    let mut code = vec![0xe8, 0x0b, 0x00, 0x00, 0x00, 0x85, 0xc9, 0x75, 0x07, 0xc3];
    code.extend_from_slice(&[0xcc; 6]);
    code.extend_from_slice(&[0x31, 0xc0, 0xc3]);
    let a = Analysis::compute(&image(&code));
    assert!(a.function(0x401010).is_some(), "the callee is missing");
    let refs = xrefs_tsv(&a, &Overlay::default(), 0x401010, 0, 60, false);
    assert!(
        refs.contains("0x401000 call, 0x401007 jmp"),
        "the conditional tail call is missing: {refs}"
    );
}

/// An operand naming the mapped headers is a reference to them: `mov eax,
/// 0x400000` names the image base, which no section maps.
#[test]
fn an_operand_naming_the_headers_is_a_reference() {
    use borer_engine::analysis::render::xrefs_tsv;
    let mut bytes = vec![0u8; 0x400];
    bytes.extend_from_slice(&[0xb8, 0x00, 0x00, 0x40, 0x00, 0xc3]);
    let mut p = Program::raw(
        bytes,
        Arch::X86,
        0x400000,
        Some(0x401000),
        vec![Section::mapped(".text", 0x401000, 0x400, 6, false, true)],
    );
    p.format = BinaryFormat::Pe;
    let a = Analysis::compute(&p);
    let refs = xrefs_tsv(&a, &Overlay::default(), 0x400000, 0, 60, false);
    assert!(
        refs.contains("sub_401000: 0x401000 imm/mem"),
        "the header reference is missing: {refs}"
    );
}

/// Builds an image whose 0x401000 references `"alpha one"` and `"beta two"`
/// and calls 0x401020, which references the middle of `L"widestring"`.
fn strings_image() -> Program {
    let mut code = vec![0u8; 0x26];
    code[..0x10].copy_from_slice(&[
        0xb8, 0x00, 0x20, 0x40, 0x00, 0xb9, 0x10, 0x20, 0x40, 0x00, 0xe8, 0x11, 0x00, 0x00, 0x00,
        0xc3,
    ]);
    code[0x20..0x26].copy_from_slice(&[0xba, 0x24, 0x20, 0x40, 0x00, 0xc3]);
    let mut data = vec![0u8; 0x40];
    data[..9].copy_from_slice(b"alpha one");
    data[0x10..0x18].copy_from_slice(b"beta two");
    for (k, b) in b"widestring".iter().enumerate() {
        data[0x20 + k * 2] = *b;
    }
    image_with_data(&code, &data)
}

/// A reference into the middle of a wide string reads the whole string, as
/// one into an ASCII string does, and the filter matches a string's text,
/// not the quotes it is printed in.
#[test]
fn a_string_search_reads_wide_strings_whole_and_ignores_quotes() {
    use borer_engine::analysis::render::functions_by_string_tsv;
    let p = strings_image();
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let wide = functions_by_string_tsv(&p, &a, &o, "widestring", 0, 50);
    assert!(wide.contains("L\"widestring\""), "{wide}");
    assert!(wide.contains("sub_401020: 1"), "{wide}");
    let quote = functions_by_string_tsv(&p, &a, &o, "\"", 0, 50);
    assert!(quote.contains(": 0 function/string pairs"), "{quote}");
    let broken = functions_by_string_tsv(&p, &a, &o, "x\ny", 0, 50);
    let head = broken.lines().next().unwrap_or_default();
    assert!(
        head.contains("match 'x") && head.contains("across"),
        "the echoed filter broke the header line: {broken}"
    );
}

/// A string search pages its rows and numbers at most `limit` strings,
/// the first row included, counting what it leaves out.
#[test]
fn a_string_search_pages_and_keeps_its_legend_within_the_limit() {
    use borer_engine::analysis::render::functions_by_string_tsv;
    let p = strings_image();
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let one = functions_by_string_tsv(&p, &a, &o, "a", 0, 1);
    assert!(
        one.starts_with("# showing 1 of 1 row: 2 function/string pairs"),
        "{one}"
    );
    assert!(one.contains("# strings: 1=\"alpha one\"\n"), "{one}");
    assert!(one.contains("sub_401000: 1 (+1 more strings)"), "{one}");
    let all = functions_by_string_tsv(&p, &a, &o, "", 0, 1);
    assert!(all.starts_with("# showing 1 of 2 rows"), "{all}");
    assert!(
        all.contains("# 1 more rows; offset=1 for the next page"),
        "{all}"
    );
    let second = functions_by_string_tsv(&p, &a, &o, "", 1, 50);
    assert!(second.starts_with("# showing 1 of 2 rows"), "{second}");
    assert!(second.contains("sub_401020: 1\n"), "{second}");
    assert!(!second.contains("sub_401000"), "{second}");
}

/// Builds an image whose 0x401000 calls 0x401010, which calls the import
/// `GetTickCount` through its slot at 0x402000, with no thunk.
fn import_call_image() -> Program {
    let mut code = vec![0xcc; 0x17];
    code[..6].copy_from_slice(&[0xe8, 0x0b, 0x00, 0x00, 0x00, 0xc3]);
    code[0x10..0x17].copy_from_slice(&[0xff, 0x15, 0x00, 0x20, 0x40, 0x00, 0xc3]);
    let mut p = image_with_data(&code, &[0u8; 4]);
    p.symbols = vec![Symbol {
        name: "KERNEL32.dll!GetTickCount".to_owned(),
        addr: 0x402000,
        kind: SymbolKind::Import,
    }];
    p
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

/// Walking the callers of an import labels the root by the import, drawn
/// as the stadium an import is, where it read `sub_<slot>`; the count line
/// is a mermaid comment.
#[test]
fn a_callgraph_over_an_import_names_its_root() {
    use borer_engine::analysis::render::callgraph_mermaid;
    let p = import_call_image();
    let a = Analysis::compute(&p);
    let out = callgraph_mermaid(&p, &a, &Overlay::default(), 0x402000, 30, true);
    assert!(out.contains("  n0([\"GetTickCount\"])\n"), "{out}");
    assert!(!out.contains("sub_402000"), "{out}");
    assert!(out.lines().all(|l| !l.starts_with('#')), "{out}");
    assert!(
        out.lines().last().unwrap_or_default().starts_with("%% "),
        "{out}"
    );
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

/// A control-flow graph pages its blocks by offset and says which it drew
/// on a mermaid comment line.
///
/// `test ecx,ecx; je +1; nop; ret` is three blocks; from the second, two
/// are drawn.
#[test]
fn a_cfg_pages_its_blocks_on_a_mermaid_comment() {
    use borer_engine::analysis::render::cfg_mermaid;
    let p = image(&[0x85, 0xc9, 0x74, 0x01, 0x90, 0xc3]);
    let a = Analysis::compute(&p);
    let out = cfg_mermaid(&a, &Overlay::default(), 0x401000, 1).unwrap_or_default();
    assert!(out.contains("%% showing 2 of 3 blocks from 1\n"), "{out}");
    assert!(out.contains("[\"0x401004 "), "{out}");
    assert!(!out.contains("[\"0x401000 "), "{out}");
    assert!(out.lines().all(|l| !l.starts_with('#')), "{out}");
}

/// A pointer in data to data a linker merged into `.text` is a reference,
/// as one to data in a data section is: the word at 0x402000 names zero
/// bytes at 0x401100 that no block covers.
#[test]
fn a_pointer_to_data_in_an_executable_section_is_a_reference() {
    use borer_engine::analysis::render::xrefs_tsv;
    let p = image_with_data(&[0xc3], &[0x00, 0x11, 0x40, 0x00]);
    let a = Analysis::compute(&p);
    assert!(a.function_at(0x401100).is_none(), "the data became code");
    let refs = xrefs_tsv(&a, &Overlay::default(), 0x401100, 0, 60, false);
    assert!(
        refs.contains("-: 0x402000 ptr"),
        "the pointer is missing: {refs}"
    );
}

/// Two reads of one table from one function are two sites on the
/// function's row, not one site folded with "1 more running the same code":
/// `mov eax,[ecx*4+0x402000]; add eax,[edx*4+0x402000]; ret`.
#[test]
fn two_reads_from_one_function_are_two_reference_rows() {
    use borer_engine::analysis::render::xrefs_tsv;
    let p = image_with_data(
        &[
            0x8b, 0x04, 0x8d, 0x00, 0x20, 0x40, 0x00, 0x03, 0x04, 0x95, 0x00, 0x20, 0x40, 0x00,
            0xc3,
        ],
        &[0u8; 16],
    );
    let a = Analysis::compute(&p);
    let refs = xrefs_tsv(&a, &Overlay::default(), 0x402000, 0, 60, false);
    assert!(
        refs.contains("sub_401000: 0x401000 index, 0x401007 index\n"),
        "{refs}"
    );
    assert!(!refs.contains("running the same code"), "{refs}");
}

/// A function whose only reference is an immediate stored into an object,
/// `mov dword [esi+0x2c],0x401040; ret`, a callback slot being filled, is
/// discovered from that immediate.
#[test]
fn a_callback_stored_by_immediate_is_a_function() {
    let mut code = vec![0xc7, 0x46, 0x2c, 0x40, 0x10, 0x40, 0x00, 0xc3];
    code.resize(0x40, 0xcc);
    code.extend_from_slice(&[0xb8, 0x01, 0x00, 0x00, 0x00, 0xc3]);
    let p = image(&code);
    let a = Analysis::compute(&p);
    assert!(
        a.function(0x401040).is_some(),
        "the stored callback is missing"
    );
}

/// A callback stored by a function that padding found late is still discovered.
///
/// `ret` at the entry, `int3` padding, then at 0x401010
/// `mov dword [esi+0x2c],0x401040; ret` naming `mov eax,1; ret` at
/// 0x401040, which nothing else mentions.
#[test]
fn a_callback_stored_by_a_late_function_is_still_seeded() {
    let mut code = vec![0xc3];
    code.resize(0x10, 0xcc);
    code.extend_from_slice(&[0xc7, 0x46, 0x2c, 0x40, 0x10, 0x40, 0x00, 0xc3]);
    code.resize(0x40, 0xcc);
    code.extend_from_slice(&[0xb8, 0x01, 0x00, 0x00, 0x00, 0xc3]);
    let p = image(&code);
    let a = Analysis::compute(&p);
    assert!(
        a.function(0x401010).is_some(),
        "the padding-seeded function is missing"
    );
    assert!(
        a.function(0x401040).is_some(),
        "the stored callback is missing"
    );
}

/// A 32-bit switch, `cmp eax,2; ja default; jmp dword [eax*4+table]` over a
/// table of four-byte case addresses, is resolved and structured.
#[test]
fn a_32_bit_jump_table_becomes_a_switch() {
    let mut code = vec![
        0x8b, 0x44, 0x24, 0x04, 0x83, 0xf8, 0x02, 0x77, 0x44, 0xff, 0x24, 0x85, 0x00, 0x20, 0x40,
        0x00,
    ];
    code.resize(0x20, 0xcc);
    code.extend_from_slice(&[0xb8, 0x0a, 0x00, 0x00, 0x00, 0xc3]);
    code.resize(0x30, 0xcc);
    code.extend_from_slice(&[0xb8, 0x14, 0x00, 0x00, 0x00, 0xc3]);
    code.resize(0x40, 0xcc);
    code.extend_from_slice(&[0xb8, 0x1e, 0x00, 0x00, 0x00, 0xc3]);
    code.resize(0x50, 0xcc);
    code.extend_from_slice(&[0x33, 0xc0, 0xc3]);
    let table = [
        0x20, 0x10, 0x40, 0x00, 0x30, 0x10, 0x40, 0x00, 0x40, 0x10, 0x40, 0x00,
    ];
    let p = image_with_data(&code, &table);
    let a = Analysis::compute(&p);
    assert!(
        a.jump_tables.contains_key(&0x401009),
        "the dispatch is not a jump table"
    );
    let text = decompile(&p, &a, &Overlay::default(), 0x401000).unwrap_or_default();
    assert!(text.contains("switch ("), "{text}");
    assert!(text.contains("case 1:"), "{text}");
    assert!(text.contains("return 20;"), "{text}");
}

/// A compare ladder that steps with `dec` folds like one that steps with
/// `sub`: `sub eax,0x1e1; dec eax; je` tests `a1 == 0x1e2`, in the same
/// radix as its siblings.
#[test]
fn a_dec_step_in_a_compare_ladder_folds_to_an_equality() {
    let text = dc(&[
        0x8b, 0x44, 0x24, 0x04, 0x2d, 0xe1, 0x01, 0x00, 0x00, 0x48, 0x74, 0x03, 0x33, 0xc0, 0xc3,
        0xb8, 0x01, 0x00, 0x00, 0x00, 0xc3,
    ]);
    assert!(
        text.contains("a1 == 0x1e2") || text.contains("a1 != 0x1e2"),
        "{text}"
    );
    assert!(!text.contains("== 0)"), "{text}");
}

/// A program that talks through Qt's network classes is networking, and one
/// that calls `WinVerifyTrust` checks code integrity, whatever the raw API
/// names look like.
#[test]
fn framework_imports_reach_the_capability_map() {
    use borer_engine::analysis::render::capability_map_tsv;
    let mut p = image(&[0xc3]);
    p.symbols = [
        (0x402000, "Qt5Network.dll!?get@QNetworkAccessManager@@QAEPAVQNetworkReply@@ABVQNetworkRequest@@@Z"),
        (0x402004, "WINTRUST.dll!WinVerifyTrust"),
    ]
    .into_iter()
    .map(|(addr, name)| Symbol {
        name: name.to_owned(),
        addr,
        kind: SymbolKind::Import,
    })
    .collect();
    let text = capability_map_tsv(&p);
    assert!(text.contains("networking"), "{text}");
    assert!(text.contains("code integrity"), "{text}");
    assert!(text.contains("of 16 capabilities"), "{text}");
}

/// `read` walks the strings of a pool: `"ab\0\0cd\0"` read as three
/// C strings gives `"ab"` and `"cd"`, stepping over the padding between
/// them, and stops when the pool ends.
#[test]
fn reading_several_strings_walks_the_pool() {
    use borer_engine::memory::{Kind, read_values};
    let p = image_with_data(&[0xc3], b"ab\0\0cd\0");
    let v = read_values(&p, 0x402000, Kind::CStr, 3).expect("strings read");
    let texts: Vec<&str> = v.iter().map(|x| x.text.as_str()).collect();
    assert_eq!(texts, ["\"ab\" (len 2)", "\"cd\" (len 2)"]);
    assert_eq!(v[1].at, 0x402004);
}

/// An address inside an instruction resolves to the instruction's start:
/// byte 3 of `mov eax,[ecx*4+0x402000]` (seven bytes) is 0x401000, and the
/// `ret` after it is its own boundary.
#[test]
fn an_address_inside_an_instruction_snaps_to_its_start() {
    use borer_engine::analysis::render::instruction_at_or_before;
    let p = image(&[0x8b, 0x04, 0x8d, 0x00, 0x20, 0x40, 0x00, 0xc3]);
    let a = Analysis::compute(&p);
    assert_eq!(instruction_at_or_before(&p, &a, 0x401003), Some(0x401000));
    assert_eq!(instruction_at_or_before(&p, &a, 0x401007), Some(0x401007));
    assert_eq!(instruction_at_or_before(&p, &a, 0x401100), None);
}

/// A class with MSVC run-time type information is named from it, its
/// virtual methods after it, and its parent from the hierarchy descriptor.
///
/// The constructor at 0x401000 stores the vtable at 0x402018, whose
/// locator one word before it (the twenty-byte record at 0x402000) leads
/// to `.?AVFoo@@` and to a base array naming `.?AVBase@@` second; the two
/// slots are `mov eax,1; ret` and `mov eax,2; ret`.
#[test]
fn a_vtable_with_rtti_names_its_class_and_parent() {
    let mut code = vec![0xc7, 0x01, 0x18, 0x20, 0x40, 0x00, 0xc3];
    code.resize(0x20, 0xcc);
    code.extend_from_slice(&[0xb8, 0x01, 0x00, 0x00, 0x00, 0xc3]);
    code.resize(0x30, 0xcc);
    code.extend_from_slice(&[0xb8, 0x02, 0x00, 0x00, 0x00, 0xc3]);
    let le = |v: u32| v.to_le_bytes();
    let mut data = vec![0u8; 0x100];
    let put = |data: &mut Vec<u8>, at: usize, bytes: &[u8]| {
        data[at..at + bytes.len()].copy_from_slice(bytes);
    };
    for (k, v) in [0u32, 0, 0, 0x402040, 0x402070].into_iter().enumerate() {
        put(&mut data, k * 4, &le(v));
    }
    put(&mut data, 0x14, &le(0x402000));
    put(&mut data, 0x18, &le(0x401020));
    put(&mut data, 0x1c, &le(0x401030));
    put(&mut data, 0x48, b".?AVFoo@@\0");
    for (k, v) in [0u32, 0, 2, 0x402080].into_iter().enumerate() {
        put(&mut data, 0x70 + k * 4, &le(v));
    }
    put(&mut data, 0x80, &le(0x402090));
    put(&mut data, 0x84, &le(0x4020b0));
    put(&mut data, 0x90, &le(0x402040));
    put(&mut data, 0xb0, &le(0x4020d0));
    put(&mut data, 0xd8, b".?AVBase@@\0");
    let p = image_with_data(&code, &data);
    let a = Analysis::compute(&p);
    let name = |va: u64| a.function(va).and_then(|f| f.name.clone());
    assert_eq!(name(0x401020).as_deref(), Some("Foo::vfunc_0"));
    assert_eq!(name(0x401030).as_deref(), Some("Foo::vfunc_1"));
    let foo = a.classes.by_name.get("Foo").expect("Foo is a class");
    assert_eq!(foo.vtable, Some(0x402018));
    assert_eq!(foo.parent.as_deref(), Some("Base"));
}

/// A global singleton's loaded pointer resolves the virtual call made
/// through it, and a global nothing registered does not.
///
/// The constructor at 0x401000 stores the RTTI-named table of `G2` at
/// `[ecx]` and registers `this` in the global at 0x4020e0, the only
/// global-addressing form 32-bit code has; `GU2` 0x401030 loads that
/// global's word and calls slot 1, which resolves to `G2::vfunc_1`.
/// `GU3` 0x401040 does the same through 0x4020e4, which no constructor
/// registered, so its call names the slot only.
/// A further base's table, stored at `[this+8]` by an inlined base
/// constructor, types the embedded subobject there, and a call through
/// that field resolves to the base's method.
///
/// The constructor at 0x401000 stores `Foo`'s table at `[ecx]` and the
/// further base's table 0x402108 at `[ecx+8]`; `Bar`'s own constructor at
/// 0x401070 stores its table 0x402158, so the embedded subobject at 8 is
/// a `Bar`. `Foo::vfunc_2` 0x401050 calls slot 1 of the vtable at
/// `[ecx+8]`, which resolves to `Bar::vfunc_1`; `Foo::vfunc_3` 0x401060
/// does the same through the field at 0xc, which nothing types, and its
/// call names the slot only.
#[test]
fn embedded_base_fields_resolve_their_calls() {
    let mut code = vec![
        0xc7, 0x01, 0x18, 0x20, 0x40, 0x00, // ASM: mov dword [ecx],0x402018
        0xc7, 0x41, 0x08, 0x08, 0x21, 0x40, 0x00, // ASM: mov dword [ecx+8],0x402108
        0xc3, // ASM: ret
    ];
    code.resize(0x10, 0xcc);
    code.extend_from_slice(&[0xb8, 0x01, 0x00, 0x00, 0x00, 0xc3]);
    code.resize(0x20, 0xcc);
    code.extend_from_slice(&[0xb8, 0x02, 0x00, 0x00, 0x00, 0xc3]);
    code.resize(0x30, 0xcc);
    code.extend_from_slice(&[0xb8, 0x03, 0x00, 0x00, 0x00, 0xc3]);
    code.resize(0x40, 0xcc);
    code.extend_from_slice(&[0xb8, 0x04, 0x00, 0x00, 0x00, 0xc3]);
    code.resize(0x50, 0xcc);
    // Foo::vfunc_2 0x401050: mov eax,[ecx+8]; call [eax+4]; ret
    code.extend_from_slice(&[0x8b, 0x41, 0x08, 0xff, 0x50, 0x04, 0xc3]);
    code.resize(0x60, 0xcc);
    // Foo::vfunc_3 0x401060: the same over the field at 0xc
    code.extend_from_slice(&[0x8b, 0x41, 0x0c, 0xff, 0x50, 0x04, 0xc3]);
    code.resize(0x70, 0xcc);
    // Bar's constructor 0x401070: mov dword [ecx],0x402158
    code.extend_from_slice(&[0xc7, 0x01, 0x58, 0x21, 0x40, 0x00, 0xc3]);
    let le = |v: u32| v.to_le_bytes();
    let mut data = vec![0u8; 0x170];
    let put = |data: &mut Vec<u8>, at: usize, bytes: &[u8]| {
        data[at..at + bytes.len()].copy_from_slice(bytes);
    };
    for (k, v) in [0u32, 0, 0, 0x402040, 0x402070].into_iter().enumerate() {
        put(&mut data, k * 4, &le(v));
    }
    put(&mut data, 0x14, &le(0x402000));
    put(&mut data, 0x18, &le(0x401030));
    put(&mut data, 0x1c, &le(0x401040));
    put(&mut data, 0x20, &le(0x401050));
    put(&mut data, 0x24, &le(0x401060));
    put(&mut data, 0x48, b".?AVFoo@@\0");
    for (k, v) in [0u32, 0, 2, 0x402080].into_iter().enumerate() {
        put(&mut data, 0x70 + k * 4, &le(v));
    }
    put(&mut data, 0x80, &le(0x402090));
    put(&mut data, 0x84, &le(0x4020a0));
    put(&mut data, 0x90, &le(0x402040));
    for (k, v) in [0x4020c0u32, 0, 8, u32::MAX, 0].into_iter().enumerate() {
        put(&mut data, 0xa0 + k * 4, &le(v));
    }
    put(&mut data, 0xc8, b".?AVBar@@\0");
    for (k, v) in [0u32, 8, 0, 0x402040, 0x402070].into_iter().enumerate() {
        put(&mut data, 0xf0 + k * 4, &le(v));
    }
    put(&mut data, 0x104, &le(0x4020f0));
    put(&mut data, 0x108, &le(0x401010));
    put(&mut data, 0x10c, &le(0x401020));
    for (k, v) in [0u32, 0, 0, 0x4020c0, 0x402070].into_iter().enumerate() {
        put(&mut data, 0x140 + k * 4, &le(v));
    }
    put(&mut data, 0x154, &le(0x402140));
    put(&mut data, 0x158, &le(0x401010));
    put(&mut data, 0x15c, &le(0x401020));
    let p = image_with_data(&code, &data);
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    assert_eq!(
        a.classes
            .secondary_vtables
            .get(&0x402108)
            .map(String::as_str),
        Some("Foo::vftable_Bar")
    );
    let call = decompile(&p, &a, &o, 0x401050).unwrap_or_default();
    assert!(call.contains("Bar::vfunc_1(this);"), "{call}");
    assert!(!call.contains("->vtable["), "{call}");
    assert_eq!(
        borer_engine::analysis::decompile::virtual_callees(&p, &a, &o, 0x401050),
        vec![0x401020]
    );
    let miss = decompile(&p, &a, &o, 0x401060).unwrap_or_default();
    assert!(miss.contains("->vtable[1]()"), "{miss}");
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
    // GU2 0x401030: mov ecx,[0x4020e0]; mov eax,[ecx]; call [eax+4]; ret
    code.extend_from_slice(&[
        0x8b, 0x0d, 0xe0, 0x20, 0x40, 0x00, 0x8b, 0x01, 0xff, 0x50, 0x04, 0xc3,
    ]);
    code.resize(0x40, 0xcc);
    // GU3 0x401040: the same over the unregistered global at 0x4020e4
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

/// A slot holding an import thunk does not name the class after the
/// import's class: the table is this image's, the class the thunk names
/// lives in the DLL.
///
/// The constructor at 0x401000 stores the table at 0x402010, whose first
/// slot is the thunk `jmp [0x402100]` at 0x401010 through the import
/// `QNetworkCookieJar::insertCookie` and whose second is `mov eax,1; ret`
/// at 0x401020. Without run-time type information the class is
/// `class_402010`, not `Qt5Network.dll!QNetworkCookieJar`.
#[test]
fn an_import_thunk_in_a_slot_does_not_name_the_class_after_the_import() {
    let mut code = vec![0xc7, 0x01, 0x10, 0x20, 0x40, 0x00, 0xc3];
    code.resize(0x10, 0xcc);
    code.extend_from_slice(&[0xff, 0x25, 0x00, 0x21, 0x40, 0x00]);
    code.resize(0x20, 0xcc);
    code.extend_from_slice(&[0xb8, 0x01, 0x00, 0x00, 0x00, 0xc3]);
    let mut data = vec![0u8; 0x110];
    data[0x10..0x14].copy_from_slice(&0x401010u32.to_le_bytes());
    data[0x14..0x18].copy_from_slice(&0x401020u32.to_le_bytes());
    let mut p = image_with_data(&code, &data);
    p.symbols = vec![Symbol {
        name: "Qt5Network.dll!?insertCookie@QNetworkCookieJar@@UAE_NABVQNetworkCookie@@@Z"
            .to_owned(),
        addr: 0x402100,
        kind: SymbolKind::Import,
    }];
    let a = Analysis::compute(&p);
    let names: Vec<&String> = a.classes.by_name.keys().collect();
    assert!(a.classes.by_name.contains_key("class_402010"), "{names:?}");
    assert!(names.iter().all(|n| !n.contains('!')), "{names:?}");
}

/// A word in data that lands in data is a `ptr` reference from its slot,
/// a word that lands on a function is a `table` one, and a small constant
/// is neither.
///
/// The words at 0x402000: 0x402010 (into `.rdata`), 0x401000 (the
/// function), and 5.
#[test]
fn a_pointer_stored_in_data_is_a_reference_to_what_it_points_at() {
    let mut data = vec![0u8; 0x20];
    data[..4].copy_from_slice(&0x402010u32.to_le_bytes());
    data[4..8].copy_from_slice(&0x401000u32.to_le_bytes());
    data[8..12].copy_from_slice(&5u32.to_le_bytes());
    let p = image_with_data(&[0xc3], &data);
    let a = Analysis::compute(&p);
    let ptr: Vec<(u64, RefKind, Option<u64>)> = a
        .xrefs_to(0x402010)
        .iter()
        .map(|s| (s.va, s.kind, s.from_entry))
        .collect();
    assert_eq!(ptr, [(0x402000, RefKind::Ptr, None)]);
    assert!(
        a.xrefs_to(0x401000)
            .iter()
            .any(|s| s.va == 0x402004 && s.kind == RefKind::Table),
        "{:?}",
        a.xrefs_to(0x401000)
    );
    assert!(a.xrefs_to(5).is_empty());
}

/// A near call to an address outside executable memory seeds no function.
///
/// `call 0x10000; ret` at the entry calls below the image base, where nothing
/// is mapped. An obfuscated operand or a byte of decrypted data read as code
/// can encode a call to anywhere, and following it once seeded a phantom empty
/// function that nothing could walk. Discovery keeps only the entry.
#[test]
fn a_call_outside_executable_memory_seeds_no_function() {
    // call rel32 -> 0x10000 (0x401005 + 0xffc0effb); ret
    let p = image(&[0xe8, 0xfb, 0xef, 0xc0, 0xff, 0xc3]);
    let a = Analysis::compute(&p);
    assert!(
        a.function(0x0001_0000).is_none(),
        "a call below the image base seeded a phantom function"
    );
    assert!(a.function(0x0040_1000).is_some(), "the entry was lost");
    let outside: Vec<u64> = a
        .functions
        .iter()
        .map(|f| f.entry)
        .filter(|e| !p.sections.iter().any(|s| *e >= s.va && *e < s.va + s.vsize))
        .collect();
    assert!(
        outside.is_empty(),
        "functions seeded outside every section: {outside:#x?}"
    );
}

/// A seed that decodes to nothing produces no empty function.
///
/// A data pointer into `.text` points at `ff ff`, which does not decode. The
/// pointer scan seeds it, the walk finds no instruction, and the result is not
/// a function: discovery drops it rather than list a zero-instruction body,
/// the noise a decrypted image otherwise fills with.
#[test]
fn a_seed_that_decodes_to_nothing_is_not_a_function() {
    let mut code = vec![0xc3u8; 0x20]; // ret at the entry, then filler
    code[0x10] = 0xff; // ff ff: an invalid opcode
    code[0x11] = 0xff;
    // A pointer at .rdata (0x402000) into .text at the invalid bytes.
    let data = 0x0040_1010u32.to_le_bytes();
    let p = image_with_data(&code, &data);
    let a = Analysis::compute(&p);
    assert!(
        a.function(0x0040_1010).is_none(),
        "an undecodable seed became a function"
    );
    let empty: Vec<u64> = a
        .functions
        .iter()
        .filter(|f| f.instr_count == 0)
        .map(|f| f.entry)
        .collect();
    assert!(
        empty.is_empty(),
        "zero-instruction functions listed: {empty:#x?}"
    );
}

/// A listing that starts in read-only data says so, one that starts in
/// `.text` outside every function says that, and one inside a function
/// says nothing.
#[test]
fn a_listing_outside_code_carries_a_caveat() {
    use borer_engine::analysis::render::listing_caveat;
    let p = image_with_data(&[0xc3], &[0x0f, 0xa2, 0xc3]);
    let a = Analysis::compute(&p);
    let data = listing_caveat(&p, &a, 0x402000);
    assert!(data.contains(".rdata (r--)"), "{data}");
    assert!(data.contains("never executes"), "{data}");
    let gap = listing_caveat(&p, &a, 0x401800);
    assert!(gap.contains("outside every discovered function"), "{gap}");
    assert_eq!(listing_caveat(&p, &a, 0x401000), "");
}

/// An import a function calls through its slot is a leaf of its callgraph,
/// named after the import without its DLL and drawn as a stadium; a near
/// callee is a box.
///
/// 0x401000: `call [0x402100]; call 0x401010; ret`, with `QString::QString`
/// behind the slot and `mov eax,1; ret` at 0x401010.
#[test]
fn an_import_is_a_leaf_of_the_callgraph() {
    use borer_engine::analysis::render::callgraph_mermaid;
    let mut code = vec![
        0xff, 0x15, 0x00, 0x21, 0x40, 0x00, 0xe8, 0x05, 0x00, 0x00, 0x00, 0xc3,
    ];
    code.resize(0x10, 0xcc);
    code.extend_from_slice(&[0xb8, 0x01, 0x00, 0x00, 0x00, 0xc3]);
    let mut p = image_with_data(&code, &[0u8; 0x110]);
    p.symbols = vec![Symbol {
        name: "Qt5Core.dll!??0QString@@QAE@XZ".to_owned(),
        addr: 0x402100,
        kind: SymbolKind::Import,
    }];
    let a = Analysis::compute(&p);
    let out = callgraph_mermaid(&p, &a, &Overlay::default(), 0x401000, 30, false);
    assert!(out.contains("([\"QString::QString\"])"), "{out}");
    assert!(out.contains("[\"sub_401010\"]"), "{out}");
    assert!(out.contains("%% 3 nodes, 1 imports"), "{out}");
    assert_eq!(out.matches(" --> ").count(), 2, "{out}");
    let mut o = Overlay::default();
    o.names
        .insert(0x401010, "Core::Ptr<UI::Canvas>::operator ->".to_owned());
    let out = callgraph_mermaid(&p, &a, &o, 0x401000, 30, false);
    assert!(
        out.contains("[\"Core::Ptr#lt;UI::Canvas#gt;::operator -#gt;\"]"),
        "{out}"
    );
}

/// An import thunk is marked with the slot it jumps through, left out of
/// the function listing with a note, and listed alone under `thunk`.
///
/// 0x401000: `call 0x401010; ret`; 0x401010: `jmp [0x402100]` through
/// `QString::QString`.
#[test]
fn an_import_thunk_is_listed_apart_from_the_functions() {
    use borer_engine::analysis::render::{FunctionOrder, function_detail, functions_tsv};
    let mut code = vec![0xe8, 0x0b, 0x00, 0x00, 0x00, 0xc3];
    code.resize(0x10, 0xcc);
    code.extend_from_slice(&[0xff, 0x25, 0x00, 0x21, 0x40, 0x00]);
    let mut p = image_with_data(&code, &[0u8; 0x110]);
    p.symbols = vec![Symbol {
        name: "Qt5Core.dll!??0QString@@QAE@XZ".to_owned(),
        addr: 0x402100,
        kind: SymbolKind::Import,
    }];
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    assert_eq!(a.function(0x401010).and_then(|f| f.thunk), Some(0x402100));
    let (_, total, all) = functions_tsv(&a, &o, None, FunctionOrder::Address, 0, 50);
    assert_eq!(total, 1, "{all}");
    assert!(all.contains("1 import thunks left out"), "{all}");
    assert!(!all.contains("0x401010"), "{all}");
    let (_, only, page) = functions_tsv(&a, &o, Some("thunk"), FunctionOrder::Address, 0, 50);
    assert_eq!(only, 1, "{page}");
    assert!(page.contains("0x401010"), "{page}");
    let detail = function_detail(&a, &o, 0x401010, 0).unwrap_or_default();
    assert!(detail.contains("thunk:   jmp [0x402100]"), "{detail}");
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
    // mov eax,[esp+4]; movlpd xmm0,[esp+8]; movlpd [eax],xmm0; ret
    // The store goes through the pointer argument, so the value is observable
    // and the load is not dead.
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
    // mov eax,[esp+4]; movhpd xmm0,[esp+8]; movlpd [eax],xmm0; ret
    let text = dc(&[
        0x8b, 0x44, 0x24, 0x04, 0x66, 0x0f, 0x16, 0x44, 0x24, 0x08, 0x66, 0x0f, 0x13, 0x00, 0xc3,
    ]);
    assert!(
        text.contains("movhpd("),
        "the high-lane move read as a whole-register assignment: {text}"
    );
}

/// A comparison against a Windows status code reads the code's name:
/// `cmp eax, 0x800b0100` is `TRUST_E_NOSIGNATURE`, and `0xc0000005` in a
/// return is `STATUS_ACCESS_VIOLATION`.
#[test]
fn a_status_code_is_named_where_it_is_compared_or_returned() {
    let text = dc(&[
        0x8b, 0x44, 0x24, 0x04, 0x3d, 0x00, 0x01, 0x0b, 0x80, 0x75, 0x03, 0x33, 0xc0, 0xc3, 0xb8,
        0x05, 0x00, 0x00, 0xc0, 0xc3,
    ]);
    assert!(text.contains("TRUST_E_NOSIGNATURE"), "{text}");
    assert!(text.contains("STATUS_ACCESS_VIOLATION"), "{text}");
}

/// On a program with no protection signal the reading list still names
/// the function that references the most strings and imports, and says
/// that is the ranking.
///
/// 0x401000 pushes three string addresses and calls `GetTickCount`
/// through its slot.
#[test]
fn triage_ranks_by_strings_and_imports_when_nothing_else_stands_out() {
    use borer_engine::analysis::render::triage_tsv;
    let code = [
        0x68, 0x00, 0x20, 0x40, 0x00, 0x68, 0x08, 0x20, 0x40, 0x00, 0x68, 0x10, 0x20, 0x40, 0x00,
        0xff, 0x15, 0x00, 0x21, 0x40, 0x00, 0x83, 0xc4, 0x0c, 0xc3,
    ];
    let mut data = vec![0u8; 0x110];
    data[..6].copy_from_slice(b"alpha\0");
    data[8..14].copy_from_slice(b"bravo\0");
    data[0x10..0x18].copy_from_slice(b"charlie\0");
    let mut p = image_with_data(&code, &data);
    p.symbols = vec![Symbol {
        name: "KERNEL32.dll!GetTickCount".to_owned(),
        addr: 0x402100,
        kind: SymbolKind::Import,
    }];
    let a = Analysis::compute(&p);
    let text = triage_tsv(&p, &a, &Overlay::default());
    assert!(text.contains("no protection signal fired"), "{text}");
    assert!(
        text.contains("references 3 strings and 1 imports"),
        "{text}"
    );
}

/// A typed read that finds nothing says which of two things went wrong:
/// the address maps to no bytes, or the bytes are not the kind asked for.
#[test]
fn a_failed_read_says_whether_the_address_is_mapped() {
    use borer_engine::memory::{Kind, read_values};
    let p = image_with_data(&[0xc3], &[0xa2, 0x2b, 0x04, 0x00]);
    let unmapped = read_values(&p, 0x900000, Kind::CStr, 1)
        .err()
        .unwrap_or_default();
    assert!(unmapped.contains("not mapped"), "{unmapped}");
    let wrong = read_values(&p, 0x402000, Kind::CStr, 1)
        .err()
        .unwrap_or_default();
    assert!(wrong.contains("no CStr at 0x402000"), "{wrong}");
    assert!(wrong.contains("0xa2"), "{wrong}");
}

/// A read through `fs` is a field of the thread environment block:
/// `mov eax,fs:[0x18]` is the TEB's own address, `fs:[0x30]` the PEB.
#[test]
fn a_read_through_fs_names_the_teb_field() {
    let text = dc(&[0x64, 0xa1, 0x18, 0x00, 0x00, 0x00, 0xc3]);
    assert!(
        text.contains("return NtCurrentTeb()->NtTib.Self;"),
        "{text}"
    );
    let text = dc(&[0x64, 0xa1, 0x30, 0x00, 0x00, 0x00, 0xc3]);
    assert!(
        text.contains("NtCurrentTeb()->ProcessEnvironmentBlock"),
        "{text}"
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
        text.contains("a1->field_0x8 = a1->field_0x0 * a1->field_0x4;"),
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

/// An operator with a `!` in its name keeps it: `QString::operator!=`
/// called through its slot is not `=`.
#[test]
fn an_operator_with_a_bang_keeps_its_name() {
    use borer_engine::analysis::bare_name;
    assert_eq!(
        bare_name("Qt5Core.dll!QString::operator!="),
        "QString::operator!="
    );
    assert_eq!(bare_name("QString::operator!="), "QString::operator!=");
    assert_eq!(bare_name("KERNEL32.dll!CreateFileW"), "CreateFileW");
    let text = dc_with(
        &[
            0x8b, 0x4c, 0x24, 0x04, 0x68, 0x00, 0x20, 0x40, 0x00, 0xff, 0x15, 0x00, 0x21, 0x40,
            0x00, 0xc3,
        ],
        &[(0x402100, "Qt5Core.dll!??9QString@@QBE_NPBD@Z")],
    );
    assert!(text.contains("QString::operator!=("), "{text}");
}

/// An empty string that follows another literal in the pool is `""` even
/// when padding zeros follow it, the way the compiler lays `"/aid_"`, `""`
/// and `"."` out.
///
/// `push 0x402006; call 0x401010; ret`, with `mov eax,[esp+4]; ret 4` at
/// 0x401010 and the pool `"/aid_\0" "\0" "\0" ".\0"` at 0x402000.
#[test]
fn an_empty_string_after_a_literal_is_a_literal() {
    let mut code = vec![
        0x68, 0x06, 0x20, 0x40, 0x00, 0xe8, 0x06, 0x00, 0x00, 0x00, 0xc3,
    ];
    code.resize(0x10, 0xcc);
    code.extend_from_slice(&[0x8b, 0x44, 0x24, 0x04, 0xc2, 0x04, 0x00]);
    let p = image_with_data(&code, b"/aid_\0\0\0.\0");
    let text = decompiled(&p, 0x401000);
    assert!(text.contains("sub_401010(\"\")"), "{text}");
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

/// A further base's vtable, stored at `[this+8]` and named by a locator
/// with subobject offset 8, renders as the class's table for the base the
/// hierarchy places at that offset.
///
/// The constructor at 0x401000 stores 0x402018 at `[ecx]` and 0x402108 at
/// `[ecx+8]`; the second table's locator at 0x4020f0 names `Foo` at
/// offset 8, and `Foo`'s base array lists `Bar` with displacement 8.
#[test]
fn a_further_bases_vtable_is_named_after_its_base() {
    let mut code = vec![
        0xc7, 0x01, 0x18, 0x20, 0x40, 0x00, 0xc7, 0x41, 0x08, 0x08, 0x21, 0x40, 0x00, 0xc3,
    ];
    code.resize(0x20, 0xcc);
    code.extend_from_slice(&[0xb8, 0x01, 0x00, 0x00, 0x00, 0xc3]);
    code.resize(0x30, 0xcc);
    code.extend_from_slice(&[0xb8, 0x02, 0x00, 0x00, 0x00, 0xc3]);
    let le = |v: u32| v.to_le_bytes();
    let mut data = vec![0u8; 0x120];
    let put = |data: &mut Vec<u8>, at: usize, bytes: &[u8]| {
        data[at..at + bytes.len()].copy_from_slice(bytes);
    };
    for (k, v) in [0u32, 0, 0, 0x402040, 0x402070].into_iter().enumerate() {
        put(&mut data, k * 4, &le(v));
    }
    put(&mut data, 0x14, &le(0x402000));
    put(&mut data, 0x18, &le(0x401020));
    put(&mut data, 0x1c, &le(0x401030));
    put(&mut data, 0x48, b".?AVFoo@@\0");
    for (k, v) in [0u32, 0, 2, 0x402080].into_iter().enumerate() {
        put(&mut data, 0x70 + k * 4, &le(v));
    }
    put(&mut data, 0x80, &le(0x402090));
    put(&mut data, 0x84, &le(0x4020a0));
    put(&mut data, 0x90, &le(0x402040));
    for (k, v) in [0x4020c0u32, 0, 8, u32::MAX, 0].into_iter().enumerate() {
        put(&mut data, 0xa0 + k * 4, &le(v));
    }
    put(&mut data, 0xc8, b".?AVBar@@\0");
    for (k, v) in [0u32, 8, 0, 0x402040, 0x402070].into_iter().enumerate() {
        put(&mut data, 0xf0 + k * 4, &le(v));
    }
    put(&mut data, 0x104, &le(0x4020f0));
    put(&mut data, 0x108, &le(0x401020));
    put(&mut data, 0x10c, &le(0x401030));
    let p = image_with_data(&code, &data);
    let a = Analysis::compute(&p);
    assert_eq!(
        a.classes
            .secondary_vtables
            .get(&0x402108)
            .map(String::as_str),
        Some("Foo::vftable_Bar")
    );
    let text = decompile(&p, &a, &Overlay::default(), 0x401000).unwrap_or_default();
    assert!(text.contains("&Foo::vftable_Bar"), "{text}");
    assert!(
        text.contains("&Foo::vftable;") || text.contains("&Foo::vftable,"),
        "{text}"
    );
}

/// The static data a `QStringLiteral` or `QByteArrayLiteral` expands to,
/// a `QArrayData` header before the text, renders as the literal, and the
/// lambda storing it is named after the macro and the text.
///
/// Two lambdas of the kind the macros produce: `mov dword [ecx], 0x402000;
/// mov eax, ecx; ret` at 0x401000 with `{-1, 5, 0, 16}` and `u"Hello"`
/// at 0x402000, and the same at 0x401010 storing 0x402030, where
/// `{-1, 3, 0, 16}` and `"abc"` lie.
#[test]
fn a_qt_literals_static_data_renders_as_the_literal() {
    let mut code = vec![0xc7, 0x01, 0x00, 0x20, 0x40, 0x00, 0x8b, 0xc1, 0xc3];
    code.resize(0x10, 0xcc);
    code.extend_from_slice(&[0xc7, 0x01, 0x30, 0x20, 0x40, 0x00, 0x8b, 0xc1, 0xc3]);
    let mut data = vec![0u8; 0x40];
    let header = |len: u32| {
        let mut h = Vec::new();
        for v in [u32::MAX, len, 0, 16] {
            h.extend_from_slice(&v.to_le_bytes());
        }
        h
    };
    data[..16].copy_from_slice(&header(5));
    for (k, c) in "Hello".encode_utf16().enumerate() {
        data[16 + k * 2..18 + k * 2].copy_from_slice(&c.to_le_bytes());
    }
    data[0x30..0x40].copy_from_slice(&header(3));
    data.extend_from_slice(b"abc\0");
    let p = image_with_data(&code, &data);
    let a = Analysis::compute(&p);
    let text = decompile(&p, &a, &Overlay::default(), 0x401000).unwrap_or_default();
    assert!(text.contains("= QStringLiteral(\"Hello\");"), "{text}");
    let text = decompile(&p, &a, &Overlay::default(), 0x401010).unwrap_or_default();
    assert!(text.contains("= QByteArrayLiteral(\"abc\");"), "{text}");
    let name = |va: u64| a.function(va).and_then(|f| f.name.clone());
    assert_eq!(name(0x401000).as_deref(), Some("QStringLiteral_Hello"));
    assert_eq!(name(0x401010).as_deref(), Some("QByteArrayLiteral_abc"));
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
            .any(|l| l.trim().starts_with("ecx = ") && l.trim().ends_with("= esi;")),
        "{text}"
    );
    assert!(text.contains("sub_401040(ecx)"), "{text}");
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
    assert!(text.contains("ecx = ((uint32_t*)(a1 + 8))[a2];"), "{text}");
    assert!(text.contains("sub_401030(*(uint32_t*)ecx, ecx)"), "{text}");
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

/// The 32-bit stack probe is known by its body.
///
/// A call to it then neither ends the parameter scan nor clobbers `this`,
/// which is read after it, and the call renders with the frame size it was
/// handed.
///
/// `push ebp; mov ebp,esp; mov eax,0x1000; call 0x401020; mov eax,[ecx];
/// pop ebp; ret` with the probe's opening at 0x401020, `push ecx; lea
/// ecx,[esp+4]; sub ecx,eax; …; ret`.
#[test]
fn a_call_to_the_stack_probe_keeps_this_a_parameter() {
    let mut code = vec![
        0x55, 0x8b, 0xec, 0xb8, 0x00, 0x10, 0x00, 0x00, 0xe8, 0x13, 0x00, 0x00, 0x00, 0x8b, 0x01,
        0x5d, 0xc3,
    ];
    code.resize(0x20, 0xcc);
    code.extend_from_slice(&[
        0x51, 0x8d, 0x4c, 0x24, 0x04, 0x2b, 0xc8, 0x1b, 0xc0, 0xf7, 0xd0, 0x23, 0xc8, 0x8b, 0xc1,
        0x59, 0x94, 0x8b, 0x00, 0x89, 0x04, 0x24, 0xc3,
    ]);
    let p = image(&code);
    let a = Analysis::compute(&p);
    assert_eq!(
        a.function(0x401020).and_then(|f| f.name.as_deref()),
        Some("__chkstk")
    );
    let text = decompile(&p, &a, &Overlay::default(), 0x401000).unwrap_or_default();
    assert!(text.contains("(void *this)"), "{text}");
    assert!(text.contains("return *(uint32_t*)this;"), "{text}");
    assert!(text.contains("__chkstk(0x1000);"), "{text}");
}

/// Builds a parent at 0x401000 with exception funclets.
///
/// The parent takes the address of its handler thunk at 0x401030, `mov
/// eax, 0x402000; jmp 0x401040`, whose `FuncInfo` at 0x402000 has two
/// unwind states, actions at 0x401050 and 0x401060, and one try block with
/// one catch clause at 0x401070.
///
/// # Arguments
///
/// * `handler` - The code at 0x401040, where the thunk jumps.
fn funclet_image(handler: &[u8]) -> Program {
    let mut code = vec![
        0x55, 0x8b, 0xec, 0x83, 0xec, 0x08, 0xb8, 0x30, 0x10, 0x40, 0x00, 0x89, 0x45, 0xf8, 0x8b,
        0x45, 0xfc, 0xc9, 0xc3,
    ];
    code.resize(0x30, 0xcc);
    code.extend_from_slice(&[0xb8, 0x00, 0x20, 0x40, 0x00, 0xe9, 0x06, 0x00, 0x00, 0x00]);
    code.resize(0x40, 0xcc);
    code.extend_from_slice(handler);
    code.resize(0x50, 0xcc);
    code.extend_from_slice(&[0x8b, 0x45, 0xfc, 0xc3]);
    code.resize(0x60, 0xcc);
    code.extend_from_slice(&[0x8d, 0x4d, 0xf8, 0xc3]);
    code.resize(0x70, 0xcc);
    code.extend_from_slice(&[0x8b, 0x45, 0xf8, 0xc3]);
    let le = |v: u32| v.to_le_bytes();
    let mut data = vec![0u8; 0x110];
    let words = |data: &mut Vec<u8>, at: usize, values: &[u32]| {
        for (k, v) in values.iter().enumerate() {
            data[at + k * 4..at + k * 4 + 4].copy_from_slice(&le(*v));
        }
    };
    words(
        &mut data,
        0,
        &[0x1993_0522, 2, 0x402030, 1, 0x402040, 0, 0, 0, 1],
    );
    words(&mut data, 0x30, &[0xffff_ffff, 0x401050, 0, 0x401060]);
    words(&mut data, 0x40, &[0, 1, 1, 1, 0x402060]);
    words(&mut data, 0x60, &[0x40, 0, 0, 0x401070]);
    image_with_data(&code, &data)
}

/// The funclets a function's exception metadata describes belong to it.
///
/// They are named after it, left out of the function listing, and
/// decompiled on its frame, so a read of `[ebp-4]` is the parent's
/// `local_8`. The parent at 0x401000 takes the address of its handler
/// thunk at 0x401030, `mov eax, 0x402000; jmp 0x401040`, where 0x401040
/// jumps through the import slot of `__CxxFrameHandler3`; the `FuncInfo`
/// at 0x402000 has two unwind states, actions at 0x401050 and 0x401060,
/// and one try block with one catch clause at 0x401070.
#[test]
fn an_exception_funclet_belongs_to_its_parent() {
    use borer_engine::analysis::render::{FunctionOrder, functions_tsv};
    use borer_engine::analysis::{Funclet, FuncletRole};
    let mut p = funclet_image(&[0xff, 0x25, 0x00, 0x21, 0x40, 0x00]);
    p.symbols = vec![Symbol {
        name: "MSVCR100.dll!__CxxFrameHandler3".to_owned(),
        addr: 0x402100,
        kind: SymbolKind::Import,
    }];
    let a = Analysis::compute(&p);
    let funclet = |va: u64| a.function(va).and_then(|f| f.funclet);
    assert_eq!(
        funclet(0x401050),
        Some(Funclet {
            parent: 0x401000,
            role: FuncletRole::Unwind(0)
        })
    );
    assert_eq!(
        funclet(0x401070),
        Some(Funclet {
            parent: 0x401000,
            role: FuncletRole::Catch(0, 0)
        })
    );
    let name = |va: u64| a.function(va).and_then(|f| f.name.clone());
    assert_eq!(name(0x401030).as_deref(), Some("sub_401000::__ehhandler"));
    assert_eq!(name(0x401050).as_deref(), Some("sub_401000::__unwind_0"));
    assert_eq!(name(0x401060).as_deref(), Some("sub_401000::__unwind_1"));
    assert_eq!(name(0x401070).as_deref(), Some("sub_401000::__catch_0_0"));
    let listing = functions_tsv(
        &a,
        &Overlay::default(),
        None,
        FunctionOrder::Address,
        0,
        100,
    )
    .2;
    assert!(
        listing.contains("4 exception funclets left out, filter=funclet lists them"),
        "{listing}"
    );
    assert!(!listing.contains("__unwind_0"), "{listing}");
    let text = decompile(&p, &a, &Overlay::default(), 0x401050).unwrap_or_default();
    assert!(
        text.contains("// note: the unwind action of state 0 of sub_401000;"),
        "{text}"
    );
    assert!(text.contains("return local_8;"), "{text}");
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

/// A read through a recognized constant table names the table, and the
/// slicing tables laid out after a CRC-32 table are named after it.
///
/// `mov eax,[esp+4]; mov eax,[eax*4+0x402000]; ret` with a CRC-32 table
/// at 0x402000 and its first slicing table at 0x402400.
#[test]
fn a_known_constant_table_renders_by_name() {
    let code = [
        0x8b, 0x44, 0x24, 0x04, 0x8b, 0x04, 0x85, 0x00, 0x20, 0x40, 0x00, 0xc3,
    ];
    let mut t0 = [0u32; 256];
    for (i, slot) in t0.iter_mut().enumerate() {
        let mut c = u32::try_from(i).unwrap_or(0);
        for _ in 0..8 {
            c = if c & 1 == 1 {
                0xedb8_8320 ^ (c >> 1)
            } else {
                c >> 1
            };
        }
        *slot = c;
    }
    let mut data = Vec::new();
    for c in t0 {
        data.extend_from_slice(&c.to_le_bytes());
    }
    for c in t0 {
        data.extend_from_slice(&((c >> 8) ^ t0[(c & 0xff) as usize]).to_le_bytes());
    }
    let p = image_with_data(&code, &data);
    let a = Analysis::compute(&p);
    assert_eq!(
        a.crypto.get(&0x402000).copied(),
        Some("CRC-32 (IEEE 802.3) table")
    );
    assert_eq!(
        a.crypto.get(&0x402400).copied(),
        Some("CRC-32 slicing table 1")
    );
    let text = decompile(&p, &a, &Overlay::default(), 0x401000).unwrap_or_default();
    assert!(text.contains("crc_32_table"), "{text}");
}

/// The address of a variable in writable data passed to a call renders as
/// the variable's address, not as a number.
///
/// `push 0x402000; call 0x401020; add esp,4; ret`, with 0x402000 in a
/// writable `.data` section holding zeros and a callee reading its one
/// argument.
#[test]
fn a_writable_data_address_renders_as_a_globals_address() {
    let mut code = vec![
        0x68, 0x00, 0x20, 0x40, 0x00, 0xe8, 0x16, 0x00, 0x00, 0x00, 0x83, 0xc4, 0x04, 0xc3,
    ];
    code.resize(0x20, 0xcc);
    code.extend_from_slice(&[0x8b, 0x44, 0x24, 0x04, 0xc3]);
    let mut p = image_with_data(&code, &[0u8; 16]);
    p.sections[1].name = ".data".to_owned();
    p.sections[1].writable = true;
    let text = decompiled(&p, 0x401000);
    assert!(text.contains("sub_401020(&g32_402000)"), "{text}");
}

/// A `test r, r` whose operand changes before the jump copies the value
/// into one temporary, not two, and the condition reads `t == 0`.
///
/// The loop of the thiscall-copy test: `mov ecx,esi; add esi,16; test
/// ecx,ecx; je` with `ecx` holding `esi` when the test runs.
#[test]
fn a_test_of_a_value_against_itself_copies_it_once() {
    let mut code = vec![
        0x55, 0x8b, 0xec, 0x56, 0x8b, 0x75, 0x08, 0xeb, 0x0e, 0x8b, 0xce, 0x83, 0xc6, 0x10, 0x85,
        0xc9, 0x74, 0x05, 0xe8, 0x29, 0x00, 0x00, 0x00, 0x3b, 0x75, 0x0c, 0x75, 0xed, 0x5e, 0x5d,
        0xc2, 0x08, 0x00,
    ];
    code.resize(0x40, 0xcc);
    code.extend_from_slice(&[0x8b, 0x01, 0xc3]);
    let text = dc(&code);
    assert!(!text.contains("tmp_4"), "{text}");
    assert!(!text.contains(" & "), "{text}");
    assert!(text.contains("== 0) continue;"), "{text}");
}

/// A word in the resource section that spells a code address seeds no
/// function, while the same word in `.rdata` does.
///
/// Three functions back to back with no padding between them, `ret` at
/// 0x401000 and `mov eax,N; ret` at 0x401001 and 0x401007: `.rdata`
/// holds 0x401007 and `.rsrc` holds 0x401001, and only the first becomes
/// a function.
#[test]
fn a_resource_word_seeds_no_function() {
    let code = [
        0xc3, 0xb8, 0x01, 0x00, 0x00, 0x00, 0xc3, 0xb8, 0x02, 0x00, 0x00, 0x00, 0xc3,
    ];
    let mut p = image_with_data(&code, &0x401007u32.to_le_bytes());
    p.bytes.resize(0x3000, 0);
    p.bytes[0x2000..0x2004].copy_from_slice(&0x401001u32.to_le_bytes());
    p.sections.push(Section::mapped(
        ".rsrc", 0x403000, 0x2000, 0x1000, false, false,
    ));
    let a = Analysis::compute(&p);
    let entries: Vec<u64> = a.functions.iter().map(|f| f.entry).collect();
    assert!(entries.contains(&0x401007), "{entries:x?}");
    assert!(!entries.contains(&0x401001), "{entries:x?}");
}

/// A jump table in `.text` is referenced as a table, and its base is no
/// function.
///
/// `mov eax,[esp+4]; cmp eax,1; ja 0x401010; jmp [eax*4+0x401011]; ret`
/// with the table right after the `ret`, naming the two `ret`s that
/// follow it; nothing is padded, so no gap walk reaches the table.
#[test]
fn a_jump_tables_base_is_no_function() {
    let mut code = vec![
        0x8b, 0x44, 0x24, 0x04, 0x83, 0xf8, 0x01, 0x77, 0x07, 0xff, 0x24, 0x85, 0x11, 0x10, 0x40,
        0x00, 0xc3,
    ];
    code.extend_from_slice(&0x401019u32.to_le_bytes());
    code.extend_from_slice(&0x40101au32.to_le_bytes());
    code.extend_from_slice(&[0xc3, 0xc3]);
    let p = image(&code);
    let a = Analysis::compute(&p);
    let entries: Vec<u64> = a.functions.iter().map(|f| f.entry).collect();
    assert!(!entries.contains(&0x401011), "{entries:x?}");
    assert_eq!(
        a.xrefs_to(0x401011).first().map(|s| s.kind),
        Some(RefKind::Index)
    );
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

/// A PE's image base renders as `&__ImageBase`, the linker's name for it.
///
/// `mov ax,[0x400000]; ret` in a PE based at 0x400000.
#[test]
fn a_pes_image_base_renders_as_image_base() {
    let mut p = image(&[0x66, 0xa1, 0x00, 0x00, 0x40, 0x00, 0xc3]);
    p.format = BinaryFormat::Pe;
    let text = decompiled(&p, 0x401000);
    assert!(text.contains("*(uint16_t*)&__ImageBase"), "{text}");
}

/// A callee that sets `ecx` with `or ecx, -1` reads no argument in it, so
/// its caller passes none.
///
/// The caller `mov ecx,5; call 0x401020; ret` calls `or ecx,-1; mov
/// eax,ecx; ret`.
#[test]
fn an_or_with_minus_one_sets_the_register_without_reading_it() {
    let mut code = vec![
        0xb9, 0x05, 0x00, 0x00, 0x00, 0xe8, 0x16, 0x00, 0x00, 0x00, 0xc3,
    ];
    code.resize(0x20, 0xcc);
    code.extend_from_slice(&[0x83, 0xc9, 0xff, 0x8b, 0xc1, 0xc3]);
    let p = image(&code);
    let a = Analysis::compute(&p);
    let text = decompile(&p, &a, &Overlay::default(), 0x401000).unwrap_or_default();
    assert!(text.contains("sub_401020()"), "{text}");
    let callee = decompile(&p, &a, &Overlay::default(), 0x401020).unwrap_or_default();
    assert!(callee.contains("sub_401020()"), "{callee}");
    assert!(
        callee.contains("return -1;") || callee.contains("return 0xffffffff;"),
        "{callee}"
    );
}

/// A countdown `sub ebx, 1; jne` reads the counter it just wrote, not a
/// copy of what it held.
///
/// `mov ebx,2; L: call 0x401020; sub ebx,1; jne L; ret`, the callee `mov
/// eax,1; ret`.
#[test]
fn a_countdown_reads_the_counter_it_just_wrote() {
    let mut code = vec![
        0xbb, 0x02, 0x00, 0x00, 0x00, 0xe8, 0x16, 0x00, 0x00, 0x00, 0x83, 0xeb, 0x01, 0x75, 0xf6,
        0xc3,
    ];
    code.resize(0x20, 0xcc);
    code.extend_from_slice(&[0xb8, 0x01, 0x00, 0x00, 0x00, 0xc3]);
    let text = dc(&code);
    assert!(text.contains("while (ebx != 0)"), "{text}");
    assert!(!text.contains("tmp_"), "{text}");
}

/// A one-slot table a constructor stores at `[this]` is the class's
/// vtable: `mov dword [ecx],0x402000; ret` over a table whose one slot is
/// `mov eax,1; ret` at 0x401010.
#[test]
fn a_one_slot_table_a_constructor_stores_is_a_vtable() {
    let mut code = vec![0xc7, 0x01, 0x00, 0x20, 0x40, 0x00, 0xc3];
    code.resize(0x10, 0xcc);
    code.extend_from_slice(&[0xb8, 0x01, 0x00, 0x00, 0x00, 0xc3]);
    let mut data = vec![0x10, 0x10, 0x40, 0x00];
    data.resize(16, 0);
    let text = dc_data(&code, &data, &[]);
    assert!(text.contains("&class_402000::vftable"), "{text}");
}

/// A table an object on the stack points at is a class's vtable: `sub
/// esp,8; mov dword [esp],0x402000; mov eax,[esp]; add esp,8; ret` over a
/// two-slot table, `mov eax,1; ret` at 0x401020 twice.
#[test]
fn a_table_a_stack_object_points_at_is_a_vtable() {
    let mut code = vec![
        0x83, 0xec, 0x08, 0xc7, 0x04, 0x24, 0x00, 0x20, 0x40, 0x00, 0x8b, 0x04, 0x24, 0x83, 0xc4,
        0x08, 0xc3,
    ];
    code.resize(0x20, 0xcc);
    code.extend_from_slice(&[0xb8, 0x01, 0x00, 0x00, 0x00, 0xc3]);
    let mut data = vec![0x20, 0x10, 0x40, 0x00, 0x20, 0x10, 0x40, 0x00];
    data.resize(16, 0);
    let text = dc_data(&code, &data, &[]);
    assert!(text.contains("&class_402000::vftable"), "{text}");
}

/// A constant spelling four printable characters is the multi-character
/// literal the source wrote.
///
/// `mov eax,0x41554556; ret` returns `'AUEV'`, while `mov
/// eax,0x3f800000; ret` (a float's bits) stays a number.
#[test]
fn a_four_character_code_renders_as_its_literal() {
    let text = dc(&[0xb8, 0x56, 0x45, 0x55, 0x41, 0xc3]);
    assert!(text.contains("return 'AUEV';"), "{text}");
    let text = dc(&[0xb8, 0x00, 0x00, 0x80, 0x3f, 0xc3]);
    assert!(text.contains("return 0x3f800000;"), "{text}");
}

/// The CRT's `__SEH_prolog4`, byte for byte: `push -1; push eax;
/// mov eax,fs:[0]; push eax; mov eax,[esp+0xc]; mov fs:[0],esp;
/// mov [esp+0xc],ebp; lea ebp,[esp+0xc]; push eax; ret`.
const SEH_PROLOG4: [u8; 31] = [
    0x6a, 0xff, 0x50, 0x64, 0xa1, 0x00, 0x00, 0x00, 0x00, 0x50, 0x8b, 0x44, 0x24, 0x0c, 0x64, 0x89,
    0x25, 0x00, 0x00, 0x00, 0x00, 0x89, 0x6c, 0x24, 0x0c, 0x8d, 0x6c, 0x24, 0x0c, 0x50, 0xc3,
];

/// A function whose frame `__SEH_prolog4` builds still reads its arguments
/// through `ebp` and still saves its registers in its prologue.
///
/// The caller: `mov eax,0; call 0x401040; push ecx; push ebx; push esi;
/// push edi; mov eax,[ebp+8]; add eax,[ebp+0xc]; mov ecx,[ebp-0xc];
/// mov fs:[0],ecx; pop edi; pop esi; pop ebx; leave; ret 8`, with the helper
/// at 0x401040. The helper is named, its call is not rendered, `[ebp+8]` is
/// the first parameter, and the four pushes after it are register saves
/// rather than stores.
#[test]
fn seh_prolog_helper_builds_the_frame() {
    let mut code = vec![
        0xb8, 0x00, 0x00, 0x00, 0x00, 0xe8, 0x36, 0x00, 0x00, 0x00, 0x51, 0x53, 0x56, 0x57, 0x8b,
        0x45, 0x08, 0x03, 0x45, 0x0c, 0x8b, 0x4d, 0xf4, 0x64, 0x89, 0x0d, 0x00, 0x00, 0x00, 0x00,
        0x5f, 0x5e, 0x5b, 0xc9, 0xc2, 0x08, 0x00,
    ];
    code.resize(0x40, 0xcc);
    code.extend_from_slice(&SEH_PROLOG4);
    let p = image(&code);
    let a = Analysis::compute(&p);
    let helper = a.function(0x401040).and_then(|f| f.name.as_deref());
    assert_eq!(helper, Some("__SEH_prolog4"));
    let text = decompile(&p, &a, &Overlay::default(), 0x401000).unwrap_or_default();
    assert!(text.contains("return a1 + a2;"), "{text}");
    assert!(!text.contains("__SEH_prolog4("), "{text}");
    assert!(!text.contains("ebp->"), "{text}");
    assert!(!text.contains("= esi;"), "{text}");
}

/// The block after the frame helper's call starts with the handler
/// registered, so an argument pushed there reaches the call.
///
/// The caller: `mov eax,0; call 0x401040; push ecx; push 0x14; call
/// 0x401060; pop ecx; mov ecx,[ebp-0xc]; mov fs:[0],ecx; leave; ret`,
/// with the helper at 0x401040 and a callee reading one argument at
/// 0x401060. The `push ecx` makes room; the `push 0x14` is the argument.
#[test]
fn a_push_after_the_frame_helper_is_an_argument() {
    let mut code = vec![
        0xb8, 0x00, 0x00, 0x00, 0x00, 0xe8, 0x36, 0x00, 0x00, 0x00, 0x51, 0x6a, 0x14, 0xe8, 0x4e,
        0x00, 0x00, 0x00, 0x59, 0x8b, 0x4d, 0xf4, 0x64, 0x89, 0x0d, 0x00, 0x00, 0x00, 0x00, 0xc9,
        0xc3,
    ];
    code.resize(0x40, 0xcc);
    code.extend_from_slice(&SEH_PROLOG4);
    code.resize(0x60, 0xcc);
    code.extend_from_slice(&[0x8b, 0x44, 0x24, 0x04, 0xc3]);
    let p = image(&code);
    let text = decompiled(&p, 0x401000);
    assert!(text.contains("sub_401060(20)"), "{text}");
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

/// The CRT's `__SEH_prolog4` as later CRTs build it.
///
/// Byte for byte as `d3dx9_43` links it: `push __except_handler4; push
/// dword fs:[0]; mov eax,[esp+0x10]; mov [esp+0x10],ebp; lea
/// ebp,[esp+0x10]; sub esp,eax; push ebx; push esi; push edi; mov
/// eax,[__security_cookie]; xor [ebp-4],eax; xor eax,ebp; push eax; mov
/// [ebp-0x18],esp; push dword [ebp-8]; mov eax,[ebp-4]; mov dword
/// [ebp-4],-2; mov [ebp-8],eax; lea eax,[ebp-0x10]; mov fs:[0],eax; ret`,
/// the handler at 0x401100 and the cookie at 0x402000.
const SEH_PROLOG4_HANDLER: [u8; 69] = [
    0x68, 0x00, 0x11, 0x40, 0x00, 0x64, 0xff, 0x35, 0x00, 0x00, 0x00, 0x00, 0x8b, 0x44, 0x24, 0x10,
    0x89, 0x6c, 0x24, 0x10, 0x8d, 0x6c, 0x24, 0x10, 0x2b, 0xe0, 0x53, 0x56, 0x57, 0xa1, 0x00, 0x20,
    0x40, 0x00, 0x31, 0x45, 0xfc, 0x33, 0xc5, 0x50, 0x89, 0x65, 0xe8, 0xff, 0x75, 0xf8, 0x8b, 0x45,
    0xfc, 0xc7, 0x45, 0xfc, 0xfe, 0xff, 0xff, 0xff, 0x89, 0x45, 0xf8, 0x8d, 0x45, 0xf0, 0x64, 0xa3,
    0x00, 0x00, 0x00, 0x00, 0xc3,
];

/// The prologue helper that pushes its handler's address before the head
/// of the handler chain builds the frame too.
///
/// Its caller's `[ebp+8]` is the argument its own callers push, and the
/// stack is known after it.
///
/// The caller at 0x401000: `push 0x14; call 0x401020; pop ecx; ret`; the
/// function at 0x401020: `push 0xc; push 0x402010; call 0x401060; push
/// dword [ebp+8]; call 0x401120; pop ecx; mov ecx,[ebp-0x10]; mov
/// fs:[0],ecx; pop ecx; pop edi; pop esi; pop ebx; leave; ret`, with the
/// helper at 0x401060 and `mov eax,[esp+4]; ret` at 0x401120. An operator
/// `new` wrapper of this shape, unread, took no argument, and each of its
/// callers called it with none; read, the frame the helper sized with
/// `sub esp, eax` lost the stack, and the push after it was no argument.
#[test]
fn a_prolog_helper_pushing_its_handler_builds_the_frame() {
    let mut code = vec![0x6a, 0x14, 0xe8, 0x19, 0x00, 0x00, 0x00, 0x59, 0xc3];
    code.resize(0x20, 0xcc);
    code.extend_from_slice(&[
        0x6a, 0x0c, 0x68, 0x10, 0x20, 0x40, 0x00, 0xe8, 0x34, 0x00, 0x00, 0x00, 0xff, 0x75, 0x08,
        0xe8, 0xec, 0x00, 0x00, 0x00, 0x59, 0x8b, 0x4d, 0xf0, 0x64, 0x89, 0x0d, 0x00, 0x00, 0x00,
        0x00, 0x59, 0x5f, 0x5e, 0x5b, 0xc9, 0xc3,
    ]);
    code.resize(0x60, 0xcc);
    code.extend_from_slice(&SEH_PROLOG4_HANDLER);
    code.resize(0x120, 0xcc);
    code.extend_from_slice(&[0x8b, 0x44, 0x24, 0x04, 0xc3]);
    let p = image_with_data(&code, &[0; 0x20]);
    let a = Analysis::compute(&p);
    assert_eq!(
        a.function(0x401060).and_then(|f| f.name.as_deref()),
        Some("__SEH_prolog4")
    );
    let o = Overlay::default();
    let callee = decompile(&p, &a, &o, 0x401020).unwrap_or_default();
    assert!(callee.contains("sub_401020(uint32_t a1)"), "{callee}");
    assert!(callee.contains("return sub_401120(a1);"), "{callee}");
    assert!(!callee.contains("asm"), "{callee}");
    let caller = decompile(&p, &a, &o, 0x401000).unwrap_or_default();
    assert!(caller.contains("sub_401020(20)"), "{caller}");
}

/// The CRT's `__SEH_epilog4`, byte for byte: `mov ecx,[ebp-0x10]; mov
/// fs:[0],ecx; pop ecx; pop edi; pop edi; pop esi; pop ebx; mov esp,ebp;
/// pop ebp; push ecx; ret`.
const SEH_EPILOG4: [u8; 20] = [
    0x8b, 0x4d, 0xf0, 0x64, 0x89, 0x0d, 0x00, 0x00, 0x00, 0x00, 0x59, 0x5f, 0x5f, 0x5e, 0x5b, 0x8b,
    0xe5, 0x5d, 0x51, 0xc3,
];

/// A call to the epilogue helper right before `ret` is the return: the
/// helper is named, the call is not rendered, and `eax` survives it.
///
/// The caller: `mov eax,0; call 0x401040; push ebx; push esi; push edi;
/// mov eax,[ebp+8]; call 0x401060; ret`, with the prologue helper at
/// 0x401040 and the epilogue helper at 0x401060.
#[test]
fn seh_epilog_helper_is_the_return() {
    let mut code = vec![
        0xb8, 0x00, 0x00, 0x00, 0x00, 0xe8, 0x36, 0x00, 0x00, 0x00, 0x53, 0x56, 0x57, 0x8b, 0x45,
        0x08, 0xe8, 0x4b, 0x00, 0x00, 0x00, 0xc3,
    ];
    code.resize(0x40, 0xcc);
    code.extend_from_slice(&SEH_PROLOG4);
    code.resize(0x60, 0xcc);
    code.extend_from_slice(&SEH_EPILOG4);
    let p = image(&code);
    let a = Analysis::compute(&p);
    assert_eq!(
        a.function(0x401060).and_then(|f| f.name.as_deref()),
        Some("__SEH_epilog4")
    );
    let text = decompile(&p, &a, &Overlay::default(), 0x401000).unwrap_or_default();
    assert!(text.contains("return a1;"), "{text}");
    assert!(!text.contains("__SEH_epilog4("), "{text}");
}

/// The handler's bookkeeping in a function with a registered handler
/// renders as nothing: the try-level stores at `[ebp-4]` and the unlink of
/// `fs:[0]` before the return.
///
/// The caller of the helper: `mov eax,0; call 0x401040; mov dword
/// [ebp-4],0; mov eax,[ebp+8]; or dword [ebp-4],-1; mov ecx,[ebp-0xc];
/// mov fs:[0],ecx; leave; ret 4`.
#[test]
fn handler_bookkeeping_renders_as_nothing() {
    let mut code = vec![
        0xb8, 0x00, 0x00, 0x00, 0x00, 0xe8, 0x36, 0x00, 0x00, 0x00, 0xc7, 0x45, 0xfc, 0x00, 0x00,
        0x00, 0x00, 0x8b, 0x45, 0x08, 0x83, 0x4d, 0xfc, 0xff, 0x8b, 0x4d, 0xf4, 0x64, 0x89, 0x0d,
        0x00, 0x00, 0x00, 0x00, 0xc9, 0xc2, 0x04, 0x00,
    ];
    code.resize(0x40, 0xcc);
    code.extend_from_slice(&SEH_PROLOG4);
    let p = image(&code);
    let text = decompiled(&p, 0x401000);
    assert!(text.contains("return a1;"), "{text}");
    assert!(!text.contains("fs"), "{text}");
    assert!(!text.contains("= -1;"), "{text}");
    assert!(!text.contains("= 0;"), "{text}");
}

/// An inline handler prologue leaves nothing either: the head read from
/// `fs:[0]` and pushed, and the registration of the new record.
///
/// `push ebp; mov ebp,esp; push -1; push 0x401100; mov eax,fs:[0];
/// push eax; mov fs:[0],esp; mov eax,[ebp+8]; mov ecx,[ebp-0x10];
/// mov fs:[0],ecx; leave; ret 4`.
#[test]
fn an_inline_handler_prologue_renders_as_nothing() {
    let text = dc(&[
        0x55, 0x8b, 0xec, 0x6a, 0xff, 0x68, 0x00, 0x11, 0x40, 0x00, 0x64, 0xa1, 0x00, 0x00, 0x00,
        0x00, 0x50, 0x64, 0x89, 0x25, 0x00, 0x00, 0x00, 0x00, 0x8b, 0x45, 0x08, 0x8b, 0x4d, 0xf0,
        0x64, 0x89, 0x0d, 0x00, 0x00, 0x00, 0x00, 0xc9, 0xc2, 0x04, 0x00,
    ]);
    assert!(text.contains("return a1;"), "{text}");
    assert!(!text.contains("fs"), "{text}");
}

/// A parameter or result nothing narrows is the machine word: `uint32_t`
/// on a 32-bit target, where every one of 2,200 functions read `uint64_t`.
///
/// `mov eax,[esp+4]; ret`.
#[test]
fn the_default_type_is_the_machine_word() {
    let text = dc(&[0x8b, 0x44, 0x24, 0x04, 0xc3]);
    assert!(text.contains("uint32_t sub_401000(uint32_t a1)"), "{text}");
    assert!(!text.contains("uint64_t"), "{text}");
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
    assert!(text.contains("(&local_c)"), "{text}");
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

/// A `__thiscall` callee whose frame a helper builds still takes `this`
/// at its call sites: the scan for the registers it reads goes on past
/// the helper's call.
///
/// The caller at 0x401000: `mov ecx,[esp+4]; call 0x401010; ret`. The
/// callee: `mov eax,0; call 0x401040; mov eax,ecx; mov ecx,[ebp-0xc];
/// mov fs:[0],ecx; leave; ret`, with `__SEH_prolog4` at 0x401040.
#[test]
fn a_helper_framed_callee_still_takes_this_at_its_call_sites() {
    let mut code = vec![0x8b, 0x4c, 0x24, 0x04, 0xe8, 0x07, 0x00, 0x00, 0x00, 0xc3];
    code.resize(0x10, 0xcc);
    code.extend_from_slice(&[
        0xb8, 0x00, 0x00, 0x00, 0x00, 0xe8, 0x26, 0x00, 0x00, 0x00, 0x8b, 0xc1, 0x8b, 0x4d, 0xf4,
        0x64, 0x89, 0x0d, 0x00, 0x00, 0x00, 0x00, 0xc9, 0xc3,
    ]);
    code.resize(0x40, 0xcc);
    code.extend_from_slice(&SEH_PROLOG4);
    let p = image(&code);
    let text = decompiled(&p, 0x401000);
    assert!(text.contains("sub_401010(a1)"), "{text}");
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

/// A 32-bit constant with its sign bit set and a small magnitude is the
/// negative number the source wrote.
///
/// `mov eax,-1; ret` returns `-1`, and `add eax,-4` is `a1 - 4`, where a
/// flag like `0x80000000` stays hex.
#[test]
fn small_negative_constants_read_as_negative_on_32_bits() {
    let text = dc(&[0xb8, 0xff, 0xff, 0xff, 0xff, 0xc3]);
    assert!(text.contains("return -1;"), "{text}");
    let text = dc(&[0x8b, 0x44, 0x24, 0x04, 0x83, 0xc0, 0xfc, 0xc3]);
    assert!(text.contains("return a1 - 4;"), "{text}");
    let text = dc(&[0xb8, 0x00, 0x00, 0x00, 0x80, 0xc3]);
    assert!(text.contains("return 0x80000000;"), "{text}");
}

/// A fragment with no prologue that restores `fs:[0]` before returning
/// is a handler function's tail, and the unlink renders as nothing there
/// too.
///
/// `mov eax,[ebp+8]; mov ecx,[ebp-0xc]; mov fs:[0],ecx; pop edi; leave; ret`.
#[test]
fn a_fragment_that_unlinks_the_handler_renders_no_unlink() {
    let text = dc(&[
        0x8b, 0x45, 0x08, 0x8b, 0x4d, 0xf4, 0x64, 0x89, 0x0d, 0x00, 0x00, 0x00, 0x00, 0x5f, 0xc9,
        0xc3,
    ]);
    assert!(!text.contains("fs"), "{text}");
}

/// A class `moc` described is read from its string table, meta-data and
/// meta-object, its dispatcher names the slot's function, and the
/// meta-object's address renders as the class's `staticMetaObject`.
///
/// The string table at 0x402000 holds `Foo` and `doIt`; the meta-data at
/// 0x402030 declares one public slot; the meta-object at 0x402080 points
/// at both and at the dispatcher at 0x401020, `if (_c == 0 && _id == 0)
/// _t->doIt()`, which calls the function at 0x401000. The function at
/// 0x401040 is `mov eax, 0x402080; ret`.
#[test]
fn a_moc_described_class_names_its_slot() {
    use borer_engine::analysis::render::qt_tsv;
    let mut code = vec![0x8b, 0x41, 0x04, 0xc3];
    code.resize(0x20, 0xcc);
    code.extend_from_slice(&[
        0x8b, 0x44, 0x24, 0x08, 0x0b, 0x44, 0x24, 0x0c, 0x75, 0x0a, 0x8b, 0x4c, 0x24, 0x04, 0xe8,
        0xcd, 0xff, 0xff, 0xff, 0xc3, 0xc3,
    ]);
    code.resize(0x40, 0xcc);
    code.extend_from_slice(&[0xb8, 0x80, 0x20, 0x40, 0x00, 0xc3]);
    let le = |v: u32| v.to_le_bytes();
    let mut data = vec![0u8; 0x100];
    let put = |data: &mut Vec<u8>, at: usize, bytes: &[u8]| {
        data[at..at + bytes.len()].copy_from_slice(bytes);
    };
    for (k, v) in [0xffff_ffffu32, 3, 0, 0x20, 0xffff_ffff, 4, 0, 0x14]
        .into_iter()
        .enumerate()
    {
        put(&mut data, k * 4, &le(v));
    }
    put(&mut data, 0x20, b"Foo\0doIt\0");
    let meta = [
        7u32, 0, 0, 0, 1, 14, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 19, 2, 0x0a,
    ];
    for (k, v) in meta.into_iter().enumerate() {
        put(&mut data, 0x30 + k * 4, &le(v));
    }
    for (k, v) in [0u32, 0x402000, 0x402030, 0x401020, 0, 0]
        .into_iter()
        .enumerate()
    {
        put(&mut data, 0x80 + k * 4, &le(v));
    }
    let p = image_with_data(&code, &data);
    let a = Analysis::compute(&p);
    let name = |va: u64| a.function(va).and_then(|f| f.name.clone());
    assert_eq!(name(0x401000).as_deref(), Some("Foo::doIt"));
    let text = qt_tsv(&a);
    assert!(
        text.contains("class Foo  (staticMetaObject 0x402080, qt_static_metacall 0x401020)"),
        "{text}"
    );
    assert!(text.contains("slots: doIt@0x401000"), "{text}");
    let text = decompile(&p, &a, &Overlay::default(), 0x401040).unwrap_or_default();
    assert!(text.contains("return &Foo::staticMetaObject;"), "{text}");
}

/// A class `moc` described with no signals, slots or properties, whose
/// string table is its name alone and whose method offset is zero, is
/// listed, so its meta-object is named where it is returned.
///
/// The string table at 0x402000 holds only `Foo`; the meta-data at
/// 0x402030 declares nothing; the meta-object at 0x402080 points at both
/// and has no dispatcher. The function at 0x401000 is `mov eax,
/// 0x402080; ret`.
#[test]
fn a_moc_class_with_nothing_declared_is_listed() {
    use borer_engine::analysis::render::qt_tsv;
    let code = [0xb8, 0x80, 0x20, 0x40, 0x00, 0xc3];
    let le = |v: u32| v.to_le_bytes();
    let mut data = vec![0u8; 0x100];
    let put = |data: &mut Vec<u8>, at: usize, bytes: &[u8]| {
        data[at..at + bytes.len()].copy_from_slice(bytes);
    };
    for (k, v) in [0xffff_ffffu32, 3, 0, 0x10].into_iter().enumerate() {
        put(&mut data, k * 4, &le(v));
    }
    put(&mut data, 0x10, b"Foo\0");
    for (k, v) in [7u32, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
        .into_iter()
        .enumerate()
    {
        put(&mut data, 0x30 + k * 4, &le(v));
    }
    for (k, v) in [0u32, 0x402000, 0x402030, 0, 0, 0].into_iter().enumerate() {
        put(&mut data, 0x80 + k * 4, &le(v));
    }
    let p = image_with_data(&code, &data);
    let a = Analysis::compute(&p);
    let text = qt_tsv(&a);
    assert!(
        text.contains("class Foo  (staticMetaObject 0x402080)"),
        "{text}"
    );
    let text = decompile(&p, &a, &Overlay::default(), 0x401000).unwrap_or_default();
    assert!(text.contains("return &Foo::staticMetaObject;"), "{text}");
}

/// The first three slots of a `Q_OBJECT` class's vtable are named.
///
/// They are `metaObject`, `qt_metacast` and `qt_metacall` once the first
/// is seen to return the class's meta-object; the slot after them keeps
/// its numbered name.
///
/// `Foo`'s string table is at 0x402000 and its meta-object at 0x402080;
/// the locator at 0x4020a0 names `Foo` for the table at 0x402118, whose
/// slots are 0x401000 (`mov eax, 0x402080; ret`), 0x401010, 0x401020 and
/// 0x401030; the constructor at 0x401040 stores the table.
#[test]
fn a_qobjects_first_three_virtuals_are_named() {
    let mut code = vec![0xb8, 0x80, 0x20, 0x40, 0x00, 0xc3];
    code.resize(0x10, 0xcc);
    code.extend_from_slice(&[0x33, 0xc0, 0xc3]);
    code.resize(0x20, 0xcc);
    code.extend_from_slice(&[0xb8, 0x01, 0x00, 0x00, 0x00, 0xc3]);
    code.resize(0x30, 0xcc);
    code.extend_from_slice(&[0xb8, 0x02, 0x00, 0x00, 0x00, 0xc3]);
    code.resize(0x40, 0xcc);
    code.extend_from_slice(&[0xc7, 0x01, 0x18, 0x21, 0x40, 0x00, 0xc3]);
    let le = |v: u32| v.to_le_bytes();
    let mut data = vec![0u8; 0x140];
    let put = |data: &mut Vec<u8>, at: usize, bytes: &[u8]| {
        data[at..at + bytes.len()].copy_from_slice(bytes);
    };
    let words = |data: &mut Vec<u8>, at: usize, values: &[u32]| {
        for (k, v) in values.iter().enumerate() {
            data[at + k * 4..at + k * 4 + 4].copy_from_slice(&le(*v));
        }
    };
    words(&mut data, 0, &[0xffff_ffff, 3, 0, 0x10]);
    put(&mut data, 0x10, b"Foo\0");
    words(&mut data, 0x30, &[7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]);
    words(&mut data, 0x80, &[0, 0x402000, 0x402030, 0, 0, 0]);
    words(&mut data, 0xa0, &[0, 0, 0, 0x4020c0, 0x4020e0]);
    put(&mut data, 0xc8, b".?AVFoo@@\0");
    words(&mut data, 0xe0, &[0, 0, 1, 0x4020f0]);
    words(&mut data, 0xf0, &[0x4020f8]);
    words(&mut data, 0xf8, &[0x4020c0, 0, 0, 0xffff_ffff, 0, 0]);
    words(
        &mut data,
        0x114,
        &[0x4020a0, 0x401000, 0x401010, 0x401020, 0x401030],
    );
    let p = image_with_data(&code, &data);
    let a = Analysis::compute(&p);
    let name = |va: u64| a.function(va).and_then(|f| f.name.clone());
    assert_eq!(name(0x401000).as_deref(), Some("Foo::metaObject"));
    assert_eq!(name(0x401010).as_deref(), Some("Foo::qt_metacast"));
    assert_eq!(name(0x401020).as_deref(), Some("Foo::qt_metacall"));
    assert_eq!(name(0x401030).as_deref(), Some("Foo::vfunc_3"));
}

/// A dispatcher compiled to a compare ladder maps each case by the count
/// it reaches, whatever order the compiler laid the case blocks out in.
///
/// `Bar` declares slots `a`, `b`, `c`; the dispatcher at 0x401030 tests
/// `_c`, loads `_id`, then `sub eax,0; je c0; dec eax; je c1; dec eax;
/// jne exit` with `c2` falling through first and `c0`, `c1` after it.
#[test]
fn a_ladder_dispatcher_maps_its_cases_by_count() {
    let mut code = vec![0x8b, 0x41, 0x04, 0xc3];
    code.resize(0x10, 0xcc);
    code.extend_from_slice(&[0x8b, 0x41, 0x08, 0xc3]);
    code.resize(0x20, 0xcc);
    code.extend_from_slice(&[0x8b, 0x41, 0x0c, 0xc3]);
    code.resize(0x30, 0xcc);
    code.extend_from_slice(&[
        0x8b, 0x44, 0x24, 0x08, 0x85, 0xc0, 0x75, 0x2d, 0x8b, 0x44, 0x24, 0x0c, 0x83, 0xe8, 0x00,
        0x74, 0x10, 0x48, 0x74, 0x17, 0x48, 0x75, 0x1e, 0x8b, 0x4c, 0x24, 0x04, 0xe8, 0xd0, 0xff,
        0xff, 0xff, 0xc3, 0x8b, 0x4c, 0x24, 0x04, 0xe8, 0xa6, 0xff, 0xff, 0xff, 0xc3, 0x8b, 0x4c,
        0x24, 0x04, 0xe8, 0xac, 0xff, 0xff, 0xff, 0xc3, 0xc3,
    ]);
    let le = |v: u32| v.to_le_bytes();
    let mut data = vec![0u8; 0x100];
    let put = |data: &mut Vec<u8>, at: usize, bytes: &[u8]| {
        data[at..at + bytes.len()].copy_from_slice(bytes);
    };
    let headers = [
        0xffff_ffffu32,
        3,
        0,
        0x40,
        0xffff_ffff,
        1,
        0,
        0x34,
        0xffff_ffff,
        1,
        0,
        0x26,
        0xffff_ffff,
        1,
        0,
        0x18,
    ];
    for (k, v) in headers.into_iter().enumerate() {
        put(&mut data, k * 4, &le(v));
    }
    put(&mut data, 0x40, b"Bar\0a\0b\0c\0");
    let mut meta = vec![7u32, 0, 0, 0, 3, 14, 0, 0, 0, 0, 0, 0, 0, 0];
    for name in 1..=3u32 {
        meta.extend_from_slice(&[name, 0, 29, 2, 0x0a]);
    }
    for (k, v) in meta.into_iter().enumerate() {
        put(&mut data, 0x50 + k * 4, &le(v));
    }
    for (k, v) in [0u32, 0x402000, 0x402050, 0x401030, 0, 0]
        .into_iter()
        .enumerate()
    {
        put(&mut data, 0xd0 + k * 4, &le(v));
    }
    let p = image_with_data(&code, &data);
    let a = Analysis::compute(&p);
    let name = |va: u64| a.function(va).and_then(|f| f.name.clone());
    assert_eq!(name(0x401000).as_deref(), Some("Bar::a"));
    assert_eq!(name(0x401010).as_deref(), Some("Bar::b"));
    assert_eq!(name(0x401020).as_deref(), Some("Bar::c"));
}

/// A jump made after the frame is torn down is a tail call, and its
/// target a function, even when nothing else names that target.
///
/// `push ebp; mov ebp,esp; pop ebp; jmp 0x401010`, with `mov eax,1; ret`
/// at 0x401010 reached by nothing else.
#[test]
fn a_jump_after_the_epilogue_is_a_tail_call() {
    let mut code = vec![0x55, 0x8b, 0xec, 0x5d, 0xe9, 0x07, 0x00, 0x00, 0x00];
    code.resize(0x10, 0xcc);
    code.extend_from_slice(&[0xb8, 0x01, 0x00, 0x00, 0x00, 0xc3]);
    let p = image(&code);
    let a = Analysis::compute(&p);
    assert!(
        a.function(0x401010).is_some(),
        "the jump target is not a function"
    );
    let text = decompile(&p, &a, &Overlay::default(), 0x401000).unwrap_or_default();
    assert!(text.contains("sub_401010("), "{text}");
}

/// An `add esp, N` that cleans up after a call is not an epilogue: the
/// jump after it stays inside the function.
///
/// `push ebp; mov ebp,esp; push 1; call 0x401020; add esp,4; jmp L;
/// L: pop ebp; ret`, with `mov eax,[esp+4]; ret` at 0x401020.
#[test]
fn an_argument_cleanup_before_a_jump_is_not_an_epilogue() {
    let mut code = vec![
        0x55, 0x8b, 0xec, 0x6a, 0x01, 0xe8, 0x16, 0x00, 0x00, 0x00, 0x83, 0xc4, 0x04, 0xeb, 0x00,
        0x5d, 0xc3,
    ];
    code.resize(0x20, 0xcc);
    code.extend_from_slice(&[0x8b, 0x44, 0x24, 0x04, 0xc3]);
    let p = image(&code);
    let a = Analysis::compute(&p);
    assert!(
        a.function(0x40100f).is_none(),
        "the jump target was cut off as a function"
    );
    let text = decompile(&p, &a, &Overlay::default(), 0x401000).unwrap_or_default();
    assert!(text.contains("sub_401020(1)"), "{text}");
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

/// A frame local below the saved frame pointer is a local.
///
/// `push ebp; mov ebp,esp; push ecx; mov dword [ebp-4],5; mov eax,[ebp-4];
/// leave; ret`: the slot is named by its distance below the entry stack
/// pointer, and its displacement reads as minus four, not as `0xfffffffc`.
#[test]
fn frame_locals_are_locals() {
    let text = dc(&[
        0x55, 0x8b, 0xec, 0x51, 0xc7, 0x45, 0xfc, 0x05, 0x00, 0x00, 0x00, 0x8b, 0x45, 0xfc, 0xc9,
        0xc3,
    ]);
    assert!(text.contains("return 5;"), "{text}");
    assert!(!text.contains("0xffff"), "{text}");
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

/// The 32-bit values where a signed condition's overflow shows: the
/// extremes, their neighbours, and the small numbers around zero.
fn boundary_i32() -> [i32; 11] {
    [
        i32::MIN,
        i32::MIN + 1,
        -2,
        -1,
        0,
        1,
        2,
        5,
        i32::MAX - 1,
        i32::MAX,
        0x4000_0000,
    ]
}

/// `dec ecx; jl` jumps when SF != OF, which is the counter before the
/// decrement being below one: at `INT_MIN` the decrement overflows, the
/// result is positive, and the jump is still taken.
///
/// `mov ecx,[esp+4]; dec ecx; jl L; xor eax,eax; ret; L: mov eax,1; ret`.
/// The sign test `(int32_t)(a1 - 1) < 0` it used to print says not taken
/// there.
#[test]
fn dec_then_jl_reads_the_overflow() {
    let text = dc(&[
        0x8b, 0x4c, 0x24, 0x04, 0x49, 0x7c, 0x03, 0x33, 0xc0, 0xc3, 0xb8, 0x01, 0x00, 0x00, 0x00,
        0xc3,
    ]);
    assert!(text.contains("if (a1 < 1) {"), "{text}");
    assert!(text.contains("int32_t a1"), "{text}");
    assert!(!text.contains("- 1) < 0"), "{text}");
    for x in boundary_i32() {
        let (r, of) = x.overflowing_sub(1);
        let jl = (r < 0) != of;
        assert_eq!(x < 1, jl, "a1 = {x}");
    }
    assert_ne!(i32::MIN.wrapping_sub(1) < 0, i32::MIN < 1);
}

/// `inc eax; jg` jumps when ZF is clear and SF == OF: the counter before
/// the increment is above minus one, `INT_MAX` included, where the sign
/// of `a1 + 1` says not.
///
/// `mov eax,[esp+4]; inc eax; jg L; xor eax,eax; ret; L: mov eax,1; ret`.
#[test]
fn inc_then_jg_reads_the_overflow() {
    let text = dc(&[
        0x8b, 0x44, 0x24, 0x04, 0x40, 0x7f, 0x03, 0x33, 0xc0, 0xc3, 0xb8, 0x01, 0x00, 0x00, 0x00,
        0xc3,
    ]);
    assert!(text.contains("if (a1 > (int32_t)-1) {"), "{text}");
    assert!(!text.contains("+ 1) > 0"), "{text}");
    for x in boundary_i32() {
        let (r, of) = x.overflowing_add(1);
        let jg = r != 0 && (r < 0) == of;
        assert_eq!(x > -1, jg, "a1 = {x}");
    }
}

/// `add eax, [esp+8]; jl` jumps on the true sum being negative: where the
/// signed sum overflows it has the sign of either addend, otherwise the
/// sign of the machine sum.
///
/// `mov eax,[esp+4]; add eax,[esp+8]; jl L; xor eax,eax; ret; L: mov
/// eax,1; ret`.
#[test]
fn add_then_jl_reads_the_overflow() {
    let text = dc(&[
        0x8b, 0x44, 0x24, 0x04, 0x03, 0x44, 0x24, 0x08, 0x7c, 0x03, 0x33, 0xc0, 0xc3, 0xb8, 0x01,
        0x00, 0x00, 0x00, 0xc3,
    ]);
    assert!(
        text.contains("if ((saddo32(a1, a2) ? (int32_t)a1 : (int32_t)(a1 + a2)) < 0) {"),
        "{text}"
    );
    for x in boundary_i32() {
        for y in boundary_i32() {
            let (r, of) = x.overflowing_add(y);
            let jl = (r < 0) != of;
            let rendered = if of { x < 0 } else { x.wrapping_add(y) < 0 };
            assert_eq!(rendered, jl, "a1 = {x}, a2 = {y}");
        }
    }
}

/// `shl eax, 1; jl` reads the overflow too: SF != OF after a one-bit
/// left shift is the sign of the operand, not bit 30 of it.
///
/// `mov eax,[esp+4]; shl eax,1; jl L; xor eax,eax; ret; L: mov eax,1; ret`.
#[test]
fn shl_by_one_then_jl_reads_the_overflow() {
    let text = dc(&[
        0x8b, 0x44, 0x24, 0x04, 0xd1, 0xe0, 0x7c, 0x03, 0x33, 0xc0, 0xc3, 0xb8, 0x01, 0x00, 0x00,
        0x00, 0xc3,
    ]);
    assert!(text.contains("if (a1 < 0) {"), "{text}");
    for x in boundary_i32() {
        let r = x.wrapping_shl(1);
        let of = (r < 0) != (x < 0);
        assert_eq!(x < 0, (r < 0) != of, "a1 = {x}");
    }
}

/// `cmp eax, [esp+8]; js` jumps on the sign of the difference at 32 bits,
/// not on an unsigned `a1 < a2`.
///
/// `mov eax,[esp+4]; cmp eax,[esp+8]; js L; xor eax,eax; ret; L: mov
/// eax,1; ret`.
#[test]
fn cmp_then_js_is_the_sign_of_the_difference() {
    let text = dc(&[
        0x8b, 0x44, 0x24, 0x04, 0x3b, 0x44, 0x24, 0x08, 0x78, 0x03, 0x33, 0xc0, 0xc3, 0xb8, 0x01,
        0x00, 0x00, 0x00, 0xc3,
    ]);
    assert!(text.contains("if ((int32_t)(a1 - a2) < 0) {"), "{text}");
}

/// `lock dec dword [ecx]; jl` reads the overflow of the subtraction the
/// atomic made: the old value is the new one plus one, and the jump is
/// taken when that was below one.
///
/// `mov ecx,[esp+4]; lock dec dword [ecx]; jl L; xor eax,eax; ret; L: mov
/// eax,1; ret`.
#[test]
fn a_locked_dec_then_jl_reads_the_overflow() {
    let text = dc(&[
        0x8b, 0x4c, 0x24, 0x04, 0xf0, 0xff, 0x09, 0x7c, 0x03, 0x33, 0xc0, 0xc3, 0xb8, 0x01, 0x00,
        0x00, 0x00, 0xc3,
    ]);
    assert!(
        text.contains("tmp_1 = atomic_sub32(*(uint32_t*)a1, 1);"),
        "{text}"
    );
    assert!(text.contains("if ((int32_t)(tmp_1 + 1) < 1) {"), "{text}");
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

/// `rol` writes only CF and OF, so a `je` after it reads the zero flag of
/// the compare before: `cmp ecx, 7; rol ecx, 5; je` tests `a1 == 7`, not
/// the rotated value.
///
/// `mov ecx,[esp+4]; cmp ecx,7; rol ecx,5; je L; xor eax,eax; ret; L: mov
/// eax,1; ret`.
#[test]
fn a_rotate_keeps_the_zero_flag_before_it() {
    let text = dc(&[
        0x8b, 0x4c, 0x24, 0x04, 0x83, 0xf9, 0x07, 0xc1, 0xc1, 0x05, 0x74, 0x03, 0x33, 0xc0, 0xc3,
        0xb8, 0x01, 0x00, 0x00, 0x00, 0xc3,
    ]);
    assert!(text.contains("if (a1 == 7) {"), "{text}");
    assert!(!text.contains("rotl32(a1, 5) == 0"), "{text}");
}

/// `tzcnt` sets CF when its source is zero and ZF when the count is: `jb`
/// after it tests the source, `je` the count.
///
/// `mov ecx,[esp+4]; tzcnt eax,ecx; jcc L; xor eax,eax; ret; L: mov
/// eax,1; ret` with `jb` and with `je`.
#[test]
fn tzcnt_sets_the_carry_on_a_zero_source() {
    let with = |jcc: u8| {
        dc(&[
            0x8b, 0x4c, 0x24, 0x04, 0xf3, 0x0f, 0xbc, 0xc1, jcc, 0x03, 0x33, 0xc0, 0xc3, 0xb8,
            0x01, 0x00, 0x00, 0x00, 0xc3,
        ])
    };
    let below = with(0x72);
    assert!(below.contains("if (a1 == 0) {"), "{below}");
    assert!(!below.contains("/*"), "{below}");
    let equal = with(0x74);
    assert!(equal.contains("if (tzcnt(a1) == 0) {"), "{equal}");
}

/// A below-or-equal after arithmetic reads as C, never as a bare value.
///
/// `add; jbe` is carry or zero, `and; jbe` the zero flag alone (a logical
/// operation clears the carry): both read as C, never as the bare value
/// under a comment, which C would read as `value != 0` both ways.
///
/// `mov eax,[esp+4]; add eax,[esp+8]; jbe L; ...` and `mov eax,[esp+4];
/// shr eax,3; and eax,0x3f; jbe L; ...`.
#[test]
fn below_or_equal_after_arithmetic_reads_as_c() {
    let add = dc(&[
        0x8b, 0x44, 0x24, 0x04, 0x03, 0x44, 0x24, 0x08, 0x76, 0x03, 0x33, 0xc0, 0xc3, 0xb8, 0x01,
        0x00, 0x00, 0x00, 0xc3,
    ]);
    assert!(
        add.contains("if ((uaddo32(a1, a2) != 0 || a1 + a2 == 0)) {"),
        "{add}"
    );
    let and = dc(&[
        0x8b, 0x44, 0x24, 0x04, 0xc1, 0xe8, 0x03, 0x83, 0xe0, 0x3f, 0x76, 0x03, 0x33, 0xc0, 0xc3,
        0xb8, 0x01, 0x00, 0x00, 0x00, 0xc3,
    ]);
    assert!(and.contains("if (((a1 >> 3) & 0x3f) == 0) {"), "{and}");
    assert!(!and.contains("/*"), "{and}");
}

/// A constant a bitwise operator applies is a mask, even where its value
/// is the address of a string in the image.
///
/// `mov eax,[esp+4]; and eax,0x402000; ret` with "abcde" at 0x402000.
#[test]
fn a_mask_is_not_named_as_the_string_at_its_value() {
    let text = dc_data(
        &[0x8b, 0x44, 0x24, 0x04, 0x25, 0x00, 0x20, 0x40, 0x00, 0xc3],
        b"abcde\0",
        &[],
    );
    assert!(text.contains("return a1 & 0x402000;"), "{text}");
    assert!(!text.contains('"'), "{text}");
}

/// A constant multiplied, added or compared is a number even where its
/// value is the address of a string in the image; only a load through it
/// reads the string.
///
/// "abcde" at 0x402000, `a1 = [esp+4]`: `imul eax,[esp+4],0x402000; ret`,
/// `mov eax,[esp+4]; add eax,0x402002; ret` (inside the string), `mov
/// eax,[esp+4]; cmp eax,0x402000; jl L; mov eax,1; ret; L: xor eax,eax;
/// ret` and `mov eax,[esp+4]; movzx eax,byte [eax+0x402000]; ret`.
#[test]
fn only_a_load_reads_a_constant_as_the_string_at_its_value() {
    let data = b"abcde\0";
    let mul = dc_data(
        &[0x69, 0x44, 0x24, 0x04, 0x00, 0x20, 0x40, 0x00, 0xc3],
        data,
        &[],
    );
    assert!(mul.contains("0x402000"), "{mul}");
    assert!(!mul.contains('"'), "{mul}");
    let add = dc_data(
        &[0x8b, 0x44, 0x24, 0x04, 0x05, 0x02, 0x20, 0x40, 0x00, 0xc3],
        data,
        &[],
    );
    assert!(add.contains("0x402002"), "{add}");
    assert!(!add.contains('"'), "{add}");
    let cmp = dc_data(
        &[
            0x8b, 0x44, 0x24, 0x04, 0x3d, 0x00, 0x20, 0x40, 0x00, 0x7c, 0x06, 0xb8, 0x01, 0x00,
            0x00, 0x00, 0xc3, 0x33, 0xc0, 0xc3,
        ],
        data,
        &[],
    );
    assert!(cmp.contains("0x402000"), "{cmp}");
    assert!(!cmp.contains('"'), "{cmp}");
    let load = dc_data(
        &[
            0x8b, 0x44, 0x24, 0x04, 0x0f, 0xb6, 0x80, 0x00, 0x20, 0x40, 0x00, 0xc3,
        ],
        data,
        &[],
    );
    assert!(load.contains("\"abcde\""), "{load}");
}

/// A sum indexing a string from its first character keeps the literal;
/// the same address multiplied stays a number.
///
/// `"SunMon"` at 0x402001 after a terminator, `a1 = [esp+4]`: `mov
/// eax,[esp+4]; lea eax,[eax+eax*2]; add eax,0x402001; ret` and `imul
/// eax,[esp+4],0x402001; ret`.
#[test]
fn a_sum_from_a_string_start_keeps_the_literal() {
    let data = b"\0SunMon\0";
    let sum = dc_data(
        &[
            0x8b, 0x44, 0x24, 0x04, 0x8d, 0x04, 0x40, 0x05, 0x01, 0x20, 0x40, 0x00, 0xc3,
        ],
        data,
        &[],
    );
    assert!(sum.contains("\"SunMon\""), "{sum}");
    let mul = dc_data(
        &[0x69, 0x44, 0x24, 0x04, 0x01, 0x20, 0x40, 0x00, 0xc3],
        data,
        &[],
    );
    assert!(mul.contains("0x402001"), "{mul}");
    assert!(!mul.contains('"'), "{mul}");
}

/// A multiplier is a number even where its bytes spell four characters;
/// a value compared with or returned keeps the code it spells.
///
/// `mov eax,0x55555556; imul dword [esp+4]; mov eax,edx; ret` (a division
/// by three), `imul eax,[esp+4],0x55555556; ret`, `cmp dword [esp+4],'GSTG';
/// jne L; mov eax,1; ret; L: xor eax,eax; ret` and `mov eax,'MESH'; ret`.
#[test]
fn a_multiplier_spelling_four_characters_is_a_number() {
    let high = dc(&[
        0xb8, 0x56, 0x55, 0x55, 0x55, 0xf7, 0x6c, 0x24, 0x04, 0x8b, 0xc2, 0xc3,
    ]);
    assert!(high.contains("0x55555556"), "{high}");
    assert!(!high.contains("'UUUV'"), "{high}");
    let mul = dc(&[0x69, 0x44, 0x24, 0x04, 0x56, 0x55, 0x55, 0x55, 0xc3]);
    assert!(mul.contains("0x55555556"), "{mul}");
    assert!(!mul.contains("'UUUV'"), "{mul}");
    let tag = dc(&[
        0x81, 0x7c, 0x24, 0x04, 0x47, 0x54, 0x53, 0x47, 0x75, 0x06, 0xb8, 0x01, 0x00, 0x00, 0x00,
        0xc3, 0x33, 0xc0, 0xc3,
    ]);
    assert!(tag.contains("'GSTG'"), "{tag}");
    let returned = dc(&[0xb8, 0x48, 0x53, 0x45, 0x4d, 0xc3]);
    assert!(returned.contains("return 'MESH';"), "{returned}");
}

/// A stored value read from the register the protection writes out
/// first reads that register's new name, not the load again through the
/// rewritten index (`g[g[i]]`).
///
/// `mov ecx,[esp+4]; mov edx,[esp+8]; test ecx,ecx; je +1; inc ecx; mov
/// ecx,[edx+ecx*4]; mov [edx+0x24],ecx; test edx,edx; je +2; mov eax,ecx;
/// ret`.
#[test]
fn a_stored_value_survives_the_write_out_of_its_index() {
    let text = dc(&[
        0x8b, 0x4c, 0x24, 0x04, 0x8b, 0x54, 0x24, 0x08, 0x85, 0xc9, 0x74, 0x01, 0x41, 0x8b, 0x0c,
        0x8a, 0x89, 0x4a, 0x24, 0x85, 0xd2, 0x74, 0x02, 0x8b, 0xc1, 0xc3,
    ]);
    assert!(text.contains("ecx = ((uint32_t*)a2)[ecx];"), "{text}");
    assert!(text.contains("*(uint32_t*)(a2 + 0x24) = ecx;"), "{text}");
    assert_eq!(text.matches("((uint32_t*)a2)[ecx]").count(), 1, "{text}");
}

/// A `rep movsd` over the frame lands after the stores it overwrites, so
/// a slot read after the copy reads the copied bytes, not the zero stored
/// there first.
///
/// `sub esp,0x20; mov dword [esp+8],0; mov esi,[esp+0x24]; mov edi,esp;
/// mov ecx,8; rep movsd; mov eax,[esp+8]; add esp,0x20; ret`.
#[test]
fn a_rep_movs_over_the_frame_overwrites_pending_slots() {
    let text = dc(&[
        0x83, 0xec, 0x20, 0xc7, 0x44, 0x24, 0x08, 0x00, 0x00, 0x00, 0x00, 0x8b, 0x74, 0x24, 0x24,
        0x8b, 0xfc, 0xb9, 0x08, 0x00, 0x00, 0x00, 0xf3, 0xa5, 0x8b, 0x44, 0x24, 0x08, 0x83, 0xc4,
        0x20, 0xc3,
    ]);
    let copy = text.find("memcpy(&local_20, a1, 32);").unwrap_or(0);
    let zero = text.find("local_18 = 0;").unwrap_or(usize::MAX);
    assert!(zero < copy, "{text}");
    assert!(text.contains("return local_18;"), "{text}");
    assert!(!text.contains("return 0;"), "{text}");
}

/// `bt [ecx], eax` tests a bit of the string at `ecx`: the dword `eax >>
/// 5` from it, bit `eax & 31`, not the first dword shifted by all of `eax`.
///
/// `mov eax,[esp+4]; mov ecx,[esp+8]; bt [ecx],eax; setb al; movzx
/// eax,al; ret`.
#[test]
fn a_bit_test_on_memory_indexes_the_bit_string() {
    let text = dc(&[
        0x8b, 0x44, 0x24, 0x04, 0x8b, 0x4c, 0x24, 0x08, 0x0f, 0xa3, 0x01, 0x0f, 0x92, 0xc0, 0x0f,
        0xb6, 0xc0, 0xc3,
    ]);
    assert!(
        text.contains("((uint32_t*)a2)[(int64_t)(int32_t)a1 >> 5] >> (a1 & 0x1f)"),
        "{text}"
    );
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

/// The lifter and the emulator agree on every block of `code` at 0x401000,
/// for sixteen seeds of random registers and memory.
///
/// # Arguments
///
/// * `code` - The bytes of `.text`, one block ending in `ret`.
fn agrees_with_the_emulator(code: &[u8]) {
    use borer_engine::analysis::decompile::verify::{verify, verify_tsv};
    let p = image(code);
    let a = Analysis::compute(&p);
    for seed in 1..=16 {
        let v = verify(&p, &a, &[0x401000], seed);
        assert_eq!(v.checked, 1, "seed {seed}: {}", verify_tsv(&v));
        assert!(v.mismatches.is_empty(), "seed {seed}: {}", verify_tsv(&v));
    }
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

/// `pop es` leaves `eax` alone in the emulator as in the lifter: the
/// emulator once indexed its general registers by the segment register's
/// number, which is `rax`'s, and popped into `ax`.
#[test]
fn pop_es_agrees_with_the_emulator() {
    agrees_with_the_emulator(&[
        0x8b, 0x44, 0x24, 0x04, // ASM: mov eax,[esp+4]
        0x68, 0x66, 0x55, 0x00, 0x00, // ASM: push 0x5566
        0x07, // ASM: pop es
        0x08, 0x00, // ASM: or [eax],al
        0xc3, // ASM: ret
    ]);
}

/// A 16-bit address reads the 16-bit registers and wraps at 64 KiB, in the
/// lifter as in the emulator.
///
/// An address-size prefix in 32-bit code makes `[di-1]` the word `di` minus
/// one, modulo 2^16: never `edi`, and never `di` plus the 0xffff the
/// decoder holds the displacement as. Data decoded as code is full of such
/// prefixes (msvcrt's error strings). `mov edi,[esp+4]; mov dh,[esp+8];
/// add [di-1],dh; mov eax,[di+0x10]; ret`.
#[test]
fn a_16_bit_address_wraps_in_the_lifter_and_the_emulator() {
    let code = [
        0x8b, 0x7c, 0x24, 0x04, // ASM: mov edi,[esp+4]
        0x8a, 0x74, 0x24, 0x08, // ASM: mov dh,[esp+8]
        0x67, 0x00, 0x75, 0xff, // ASM: add [di-1],dh
        0x67, 0x8b, 0x45, 0x10, // ASM: mov eax,[di+0x10]
        0xc3, // ASM: ret
    ];
    let text = decompiled(&image(&code), 0x401000);
    assert!(text.contains("- 1) & 0xffff"), "{text}");
    agrees_with_the_emulator(&code);
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
    assert!(text.contains("*(double*)(eax + 8)"), "{text}");
    assert_st_written(&text);
}

/// Fails when the text reads an x87 register no statement assigns.
///
/// # Arguments
///
/// * `text` - The pseudo-C.
fn assert_st_written(text: &str) {
    for i in 0..8 {
        let name = format!("st{i}");
        let read = text
            .match_indices(&name)
            .any(|(at, _)| !text[at + name.len()..].starts_with(" = "));
        assert!(
            !read || text.contains(&format!("{name} = ")),
            "{name} read, never written: {text}"
        );
    }
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
    assert!(callee.contains("double sub_401020("), "{callee}");
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
    assert!(text.contains("xmm0 = sub_401020(a1);"), "{text}");
    assert!(text.contains("*(double*)a3 = xmm0;"), "{text}");
}

/// A 32-bit call clobbers the vector registers.
///
/// A callee that hands no float back in `xmm0` binds none there: the read
/// after it is of a register the convention leaves undefined, never the
/// call's result.
///
/// `sub_401020` is `push esi; call sub_401040; pop esi; ret`; the caller
/// is that of [`a_32_bit_callee_returning_in_xmm0_binds_it`].
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
    assert!(text.contains("xmm0 = __libm_sse2_pow(a1, a3);"), "{text}");
    assert!(text.contains("*(double*)a5 = xmm0;"), "{text}");
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
    assert!(text.contains("eax = sub_401020(a1);"), "{text}");
    assert!(text.contains("*(float*)eax = a2;"), "{text}");
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
    assert!(text.contains("local_8 = a1;"), "{text}");
    assert!(text.contains("return (local_8 & 0xffff) + a1;"), "{text}");
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

/// A jump from an inner switch's arm to the join of the switch around it
/// stays a jump: no loop holds either switch, so it is no `continue`, and
/// a `break` there would leave only the inner switch.
///
/// The shape of `BasepProcessInvalidImage`'s `case 2: { rcx = 21; ... }`:
/// an outer switch on `ecx` whose second arm switches on `edx`; that
/// switch's second arm jumps to the code after the outer switch, while its
/// other arms meet at a tail of their own that returns 1. Both joins are
/// ten stores long, too long to copy into an arm.
#[test]
fn a_jump_to_an_outer_switch_join_stays_a_jump() {
    let mut code = vec![
        0x8b, 0x4c, 0x24, 0x04, // ASM: mov ecx,[esp+4]
        0x8b, 0x54, 0x24, 0x08, // ASM: mov edx,[esp+8]
        0x33, 0xc0, // ASM: xor eax,eax
        0x83, 0xf9, 0x02, // ASM: cmp ecx,2
        0x77, 0x6a, // ASM: ja join
        0xff, 0x24, 0x8d, 0x00, 0x20, 0x40, 0x00, // ASM: jmp [ecx*4+0x402000]
        0xb8, 0x01, 0x00, 0x00, 0x00, // ASM: outer case 0: mov eax,1
        0xeb, 0x5c, // ASM: jmp join
        0x83, 0xfa, 0x02, // ASM: outer case 1: cmp edx,2
        0x77, 0x1a, // ASM: ja tail
        0xff, 0x24, 0x95, 0x0c, 0x20, 0x40, 0x00, // ASM: jmp [edx*4+0x40200c]
        0xb8, 0x03, 0x00, 0x00, 0x00, // ASM: inner case 0: mov eax,3
        0xeb, 0x0c, // ASM: jmp tail
        0xb8, 0x15, 0x00, 0x00, 0x00, // ASM: inner case 1: mov eax,21
        0xeb, 0x42, // ASM: jmp join
        0xb8, 0x04, 0x00, 0x00, 0x00, // ASM: inner case 2: mov eax,4
    ];
    for k in 0..10u8 {
        code.extend_from_slice(&[0xa3, k * 4, 0x31, 0x40, 0x00]); // ASM: tail: mov [0x403100+4k],eax
    }
    code.extend_from_slice(&[0xb8, 0x01, 0x00, 0x00, 0x00, 0xc3]); // ASM: mov eax,1; ret
    code.extend_from_slice(&[0xb8, 0x09, 0x00, 0x00, 0x00]); // ASM: outer case 2: mov eax,9
    for k in 0..10u8 {
        code.extend_from_slice(&[0xa3, k * 4, 0x30, 0x40, 0x00]); // ASM: join: mov [0x403000+4k],eax
    }
    code.extend_from_slice(&[0x33, 0xc0, 0xc3]); // ASM: xor eax,eax; ret
    let table = [
        0x16, 0x10, 0x40, 0x00, 0x1d, 0x10, 0x40, 0x00, 0x74, 0x10, 0x40, 0x00, 0x29, 0x10, 0x40,
        0x00, 0x30, 0x10, 0x40, 0x00, 0x37, 0x10, 0x40, 0x00,
    ];
    let text = dc_data(&code, &table, &[]);
    assert!(!text.contains("continue;"), "{text}");
    let arm = text.find("= 21;").unwrap_or(0);
    let jump = text.get(arm..).and_then(|t| t.lines().nth(1)).unwrap_or("");
    assert_eq!(jump.trim(), "goto L_401079;", "{text}");
}

/// A loop-exit jump inside a later arm of a switch the loop holds stays a
/// jump: the arms' braces sit at the switch's own indentation, and a
/// `break` there would leave the switch and run the loop on.
///
/// A loop over `*ecx` dispatching through a three-entry jump table whose
/// second arm jumps to the shared tail after the loop, which the entry
/// also reaches.
#[test]
fn a_loop_exit_in_a_switch_arm_stays_a_jump() {
    let mut code = vec![
        0x8b, 0x4c, 0x24, 0x04, // ASM: mov ecx,[esp+4]
        0x33, 0xc0, // ASM: xor eax,eax
        0x85, 0xc9, // ASM: test ecx,ecx
        0x74, 0x23, // ASM: je tail
        0x8b, 0x11, // ASM: top: mov edx,[ecx]
        0x83, 0xfa, 0x02, // ASM: cmp edx,2
        0x77, 0x14, // ASM: ja latch
        0xff, 0x24, 0x95, 0x00, 0x20, 0x40, 0x00, // ASM: jmp [edx*4+0x402000]
        0x83, 0xc0, 0x01, // ASM: case 0: add eax,1
        0xeb, 0x08, // ASM: jmp latch
        0x83, 0xc0, 0x05, // ASM: case 1: add eax,5
        0xeb, 0x0b, // ASM: jmp tail
        0x83, 0xc0, 0x07, // ASM: case 2: add eax,7
        0x83, 0xc1, 0x04, // ASM: latch: add ecx,4
        0x83, 0x39, 0x00, // ASM: cmp dword [ecx],0
        0x75, 0xdd, // ASM: jne top
    ];
    for k in 0..9u8 {
        code.extend_from_slice(&[0xa3, k * 4, 0x30, 0x40, 0x00]); // ASM: tail: mov [0x403000+4k],eax
    }
    code.push(0xc3);
    let table = [
        0x18, 0x10, 0x40, 0x00, 0x1d, 0x10, 0x40, 0x00, 0x22, 0x10, 0x40, 0x00,
    ];
    let text = dc_data(&code, &table, &[]);
    let arm = text.find("case 1: {").unwrap_or(0);
    let next = text.find("case 2: {").unwrap_or(0);
    let body = text.get(arm..next).unwrap_or("");
    assert!(body.contains("goto L_40102d;"), "{text}");
    assert!(!body.contains("break;"), "{text}");
}

/// A 32-bit global read into a register in 64-bit code is no wider than
/// 32 bits, so an index read from it needs no mask.
///
/// `mov ecx,[rip+0x402000]; mov rax,[rdx+rcx*8]; ret` in a 64-bit image.
#[test]
fn a_32_bit_global_index_needs_no_mask() {
    let p = raw::image(
        Arch::X86_64,
        &[
            0x8b, 0x0d, 0xfa, 0x0f, 0x00, 0x00, 0x48, 0x8b, 0x04, 0xca, 0xc3,
        ],
        &[0; 8],
    );
    let text = decompiled(&p, 0x401000);
    assert!(text.contains("g32_402000"), "{text}");
    assert!(!text.contains("& 0xffffffff"), "{text}");
}

/// A write to `esp` in 64-bit code moves the stack pointer.
///
/// It zero-extends into `rsp`, so the tracked frame offset is lost and a
/// later stack read is a raw dereference, not the slot it was before the
/// write. `lea esp,[rcx]; mov rax,[rsp]; ret` in a 64-bit image: comparing
/// only the full register (`rsp`) would miss the `esp` write and read
/// `retaddr` at the stale offset.
#[test]
fn a_write_to_esp_in_64_bit_code_loses_the_frame() {
    let p = raw::image(
        Arch::X86_64,
        &[0x8d, 0x21, 0x48, 0x8b, 0x04, 0x24, 0xc3],
        &[],
    );
    let text = decompiled(&p, 0x401000);
    assert!(text.contains("return *(uint64_t*)rsp;"), "{text}");
    assert!(!text.contains("retaddr"), "{text}");
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
        .find("xmm1 = *(uint128_t*)(a2 + 0x10);")
        .expect("the reload is written out");
    let sqrt = text
        .find("sqrtps(xmm1)")
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

/// The funclets of a frame handler linked into the program belong to it.
///
/// The handler is no import and has no name; the thunk is a handler's all
/// the same, since the record it hands over is a `FuncInfo` by its magic
/// number. The 32-bit client's unwind actions, read as functions of their
/// own, used the parent's `ebp` as a register nothing set.
#[test]
fn an_exception_funclet_of_a_linked_handler_belongs_to_its_parent() {
    use borer_engine::analysis::{Funclet, FuncletRole};
    let p = funclet_image(&[0x55, 0x8b, 0xec, 0x5d, 0xc3]); // ASM: push ebp; mov ebp,esp; pop ebp; ret
    let a = Analysis::compute(&p);
    assert_eq!(
        a.function(0x401050).and_then(|f| f.funclet),
        Some(Funclet {
            parent: 0x401000,
            role: FuncletRole::Unwind(0)
        })
    );
    let text = decompile(&p, &a, &Overlay::default(), 0x401050).unwrap_or_default();
    assert!(text.contains("return local_8;"), "{text}");
}

/// Runs a function's final text as C beside the binary in the emulator on
/// 64 inputs its signature types, and requires every run the binary
/// returns from to agree.
///
/// # Arguments
///
/// * `p` - The program.
/// * `entry` - The function.
///
/// # Returns
///
/// The final text, for the caller's own assertions.
fn runs_agree(p: &Program, entry: u64) -> String {
    use borer_engine::analysis::render::{Verdict, check_generated};
    let a = Analysis::compute(p);
    let o = Overlay::default();
    let text = decompile_named(p, &a, &o, entry).unwrap_or_default();
    let runs = check_generated(p, &a, &o, entry, 64, 1, 20_000).unwrap_or_default();
    let differ: Vec<String> = runs
        .iter()
        .filter_map(|(args, v)| match v {
            Verdict::Differs(line, what) => Some(format!("{args}: L{line} {what}")),
            Verdict::Agrees | Verdict::Unchecked(..) => None,
        })
        .collect();
    assert!(differ.is_empty(), "{}\n{text}", differ.join("\n"));
    assert!(
        runs.iter().any(|(_, v)| *v == Verdict::Agrees),
        "{runs:?}\n{text}"
    );
    text
}

/// The zeros pushed for a bitmap that only a computed address reads are
/// stored.
///
/// msvcrt's `strcspn` zeroes 32 bytes with eight `push eax` and sets and
/// tests bits of them through `bts [esp], eax` and `bt [esp], eax`. No
/// slot is read by name, so the pushes were dead stores, and the text set
/// bits of a bitmap it never cleared.
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
    assert!(text.contains("local_c = 0;"), "{text}");
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

/// An unwinder that only puts the chain's head back registers no handler.
///
/// msvcrt's `_global_unwind2` reads `fs:[0]`, pushes the four arguments of
/// `RtlUnwind` and, after it, stores the head it read back to `fs:[0]`.
/// That store made the function a handler's, whose entry pushes are the
/// registration record and render as nothing: `RtlUnwind()` lost its
/// arguments, and the head was never read into `local_c`.
#[test]
fn an_unwinder_restoring_the_chain_head_registers_no_handler() {
    let code = [
        0x8b, 0xff, // ASM: mov edi, edi
        0x55, // ASM: push ebp
        0x8b, 0xec, // ASM: mov ebp, esp
        0x51, 0x51, 0x53, 0x56, 0x57, // ASM: push ecx; push ecx; push ebx; push esi; push edi
        0x64, 0x8b, 0x35, 0x00, 0x00, 0x00, 0x00, // ASM: mov esi, fs:[0]
        0x89, 0x75, 0xf8, // ASM: mov [ebp-8], esi
        0xc7, 0x45, 0xfc, 0x2c, 0x10, 0x40, 0x00, // ASM: mov dword [ebp-4], 0x40102c
        0x6a, 0x00, // ASM: push 0
        0xff, 0x75, 0x0c, // ASM: push dword [ebp+0xc]
        0xff, 0x75, 0xfc, // ASM: push dword [ebp-4]
        0xff, 0x75, 0x08, // ASM: push dword [ebp+8]
        0xff, 0x15, 0x00, 0x20, 0x40, 0x00, // ASM: call [0x402000] (RtlUnwind)
        0x8b, 0x45, 0x0c, // ASM: mov eax, [ebp+0xc]
        0x8b, 0x40, 0x04, // ASM: mov eax, [eax+4]
        0x83, 0xe0, 0xfd, // ASM: and eax, -3
        0x8b, 0x4d, 0x0c, // ASM: mov ecx, [ebp+0xc]
        0x89, 0x41, 0x04, // ASM: mov [ecx+4], eax
        0x64, 0x8b, 0x3d, 0x00, 0x00, 0x00, 0x00, // ASM: mov edi, fs:[0]
        0x8b, 0x5d, 0xf8, // ASM: mov ebx, [ebp-8]
        0x89, 0x3b, // ASM: mov [ebx], edi
        0x64, 0x89, 0x1d, 0x00, 0x00, 0x00, 0x00, // ASM: mov fs:[0], ebx
        0x5f, 0x5e, 0x5b, // ASM: pop edi; pop esi; pop ebx
        0xc9, // ASM: leave
        0xc2, 0x08, 0x00, // ASM: ret 8
    ];
    let text = dc_with(&code, &[(0x402000, "RtlUnwind")]);
    assert!(text.contains("RtlUnwind(a1, 0x40102c, a2, 0);"), "{text}");
    assert!(
        text.contains("local_c = NtCurrentTeb()->NtTib.ExceptionList;"),
        "{text}"
    );
}

/// A one-slot vtable a constructor stores is named by its complete object
/// locator on a 32-bit image as on a 64-bit one.
///
/// The locator's links are absolute and its signature zero; the class it
/// names (`One`) reaches the table, its constructor and its one virtual
/// method, although nothing but the constructor vouches for the table.
#[test]
fn a_locators_class_names_a_one_slot_table_on_a_32_bit_image() {
    let code = [
        0xb8, 0x58, 0x20, 0x40, 0x00, // ASM: mov eax,0x402058
        0x89, 0x01, // ASM: mov [ecx],eax
        0xc3, // ASM: ret
        0x8b, 0x41, 0x08, // ASM: mov eax,[ecx+8] (S0 at 0x401008)
        0xc3, // ASM: ret
    ];
    // The RTTI of `One`: a type descriptor, a hierarchy of one class and
    // a locator whose address is the word before the vtable at 0x402058.
    let mut data = vec![0u8; 0x60];
    let put = |d: &mut Vec<u8>, at: usize, b: &[u8]| d[at..at + b.len()].copy_from_slice(b);
    put(&mut data, 0x08, b".?AVOne@@\0");
    put(&mut data, 0x20, &1u32.to_le_bytes());
    put(&mut data, 0x24, &0x402028u32.to_le_bytes());
    put(&mut data, 0x28, &0x402030u32.to_le_bytes());
    put(&mut data, 0x30, &0x402000u32.to_le_bytes());
    put(&mut data, 0x3c, &u32::MAX.to_le_bytes());
    put(&mut data, 0x4c, &0x402000u32.to_le_bytes());
    put(&mut data, 0x50, &0x402018u32.to_le_bytes());
    put(&mut data, 0x54, &0x402040u32.to_le_bytes());
    put(&mut data, 0x58, &0x401008u32.to_le_bytes());
    let p = image_with_data(&code, &data);
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    assert_eq!(
        a.classes.vtables.get(&0x402058).map(String::as_str),
        Some("One")
    );
    assert_eq!(name_of(&a, &o, 0x401008), "One::vfunc_0");
    assert_eq!(name_of(&a, &o, 0x401000), "One::ctor_or_dtor");
}
