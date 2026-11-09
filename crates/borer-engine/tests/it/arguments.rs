//! What a call passes: the arguments its callee takes, and none that
//! nothing set.
//!
//! Each fixture is a hand-assembled System V caller at 0x401000 and its
//! callee after it in a raw image. The caller's text runs beside the binary
//! as ISO C, as certify reads it ([`iso_agrees`]), so an argument that
//! reads a register no line sets fails the run as it fails certify.

#![expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]

use borer_engine::analysis::decompile::decompile;
use borer_engine::analysis::render::{Verdict, check_generated_iso};
use borer_engine::analysis::{Analysis, Overlay};
use borer_engine::program::{Arch, BinaryFormat, Program};

/// Builds a System V image of `code` at 0x401000, entered there.
///
/// # Arguments
///
/// * `code` - The bytes of `.text`, at most a page.
fn sysv(code: &[u8]) -> Program {
    let mut p = crate::raw::image(Arch::X86_64, code, &[]);
    p.format = BinaryFormat::Elf;
    p
}

/// Runs a function's text as ISO C beside the binary on eight inputs, as
/// certify does, and requires every run to agree.
///
/// # Arguments
///
/// * `p` - The program.
/// * `entry` - The function.
///
/// # Returns
///
/// The text, for the caller's own assertions.
#[expect(
    clippy::expect_used,
    reason = "a text that does not read has no useful recovery"
)]
fn iso_agrees(p: &Program, entry: u64) -> String {
    let a = Analysis::compute(p);
    let o = Overlay::default();
    let text = decompile(p, &a, &o, entry).unwrap_or_default();
    let rows = check_generated_iso(p, &a, &o, entry, 8, 1, 20_000).expect("the text reads");
    assert!(
        !rows.is_empty() && rows.iter().all(|(_, v)| *v == Verdict::Agrees),
        "{rows:?}\n{text}"
    );
    text
}

/// An epilogue releases its frame on its own path even when an
/// instruction that leaves the stack pointer alone sits among its pops.
///
/// In `add rsp, 0x20; mov eax, ebx; pop rbx; ret` the frame scan's walk
/// back from the `ret` stopped at the `mov`, so the `add` counted for the
/// code after it in the image, and the local at `[rsp+0x18]` there read as
/// the second stack argument: the callee took eight parameters, and its
/// caller passed `rsi` to `r9`, which nothing set.
#[test]
fn an_epilogue_steps_over_what_leaves_the_stack_alone() {
    let code = [
        0xbf, 0x05, 0x00, 0x00, 0x00, // ASM: mov edi,5
        0xe8, 0x06, 0x00, 0x00, 0x00, // ASM: call 0x401010
        0xc3, // ASM: ret
        0xcc, 0xcc, 0xcc, 0xcc, 0xcc, // ASM: int3 (padding)
        0x53, // ASM: push rbx
        0x48, 0x83, 0xec, 0x20, // ASM: sub rsp,0x20
        0x89, 0xfb, // ASM: mov ebx,edi
        0x85, 0xff, // ASM: test edi,edi
        0x74, 0x09, // ASM: je 0x401024
        0x48, 0x83, 0xc4, 0x20, // ASM: add rsp,0x20
        0x89, 0xd8, // ASM: mov eax,ebx
        0x5b, // ASM: pop rbx
        0xc3, // ASM: ret
        0xcc, // ASM: int3 (padding)
        0x89, 0x7c, 0x24, 0x18, // ASM: mov [rsp+0x18],edi
        0x8b, 0x44, 0x24, 0x18, // ASM: mov eax,[rsp+0x18]
        0x48, 0x83, 0xc4, 0x20, // ASM: add rsp,0x20
        0x5b, // ASM: pop rbx
        0xc3, // ASM: ret
    ];
    let p = sysv(&code);
    let a = Analysis::compute(&p);
    assert_eq!(a.function(0x401010).map(|f| f.stack_args), Some(0));
    let text = iso_agrees(&p, 0x401000);
    assert!(text.contains("sub_401010(5)"), "{text}");
}

/// A tail jump to a variadic function hands on no stack word of the
/// function jumping.
///
/// The variadic callee homes `rdx` to `r9` for `va_start` and takes the
/// address of its list's stack part, `[rsp+0x60]` over its 0x58-byte
/// frame, which its frame scan counts as one stack argument. The wrapper
/// that sets `esi` and `edx` and jumps to it was read as handing that word
/// on, so it took seven parameters and its caller passed `rsi` to `r9`,
/// which nothing set.
#[test]
fn a_tail_jump_to_a_variadic_function_hands_on_no_stack_word() {
    let code = [
        0xbf, 0x05, 0x00, 0x00, 0x00, // ASM: mov edi,5
        0xe8, 0x06, 0x00, 0x00, 0x00, // ASM: call 0x401010
        0xc3, // ASM: ret
        0xcc, 0xcc, 0xcc, 0xcc, 0xcc, // ASM: int3 (padding)
        0x89, 0xfe, // ASM: mov esi,edi
        0xba, 0x07, 0x00, 0x00, 0x00, // ASM: mov edx,7
        0x31, 0xc0, // ASM: xor eax,eax
        0xe9, 0x02, 0x00, 0x00, 0x00, // ASM: jmp 0x401020
        0xcc, 0xcc, // ASM: int3 (padding)
        0x48, 0x83, 0xec, 0x58, // ASM: sub rsp,0x58
        0x48, 0x89, 0x54, 0x24, 0x30, // ASM: mov [rsp+0x30],rdx
        0x48, 0x89, 0x4c, 0x24, 0x38, // ASM: mov [rsp+0x38],rcx
        0x4c, 0x89, 0x44, 0x24, 0x40, // ASM: mov [rsp+0x40],r8
        0x4c, 0x89, 0x4c, 0x24, 0x48, // ASM: mov [rsp+0x48],r9
        0x84, 0xc0, // ASM: test al,al
        0x48, 0x8d, 0x44, 0x24, 0x60, // ASM: lea rax,[rsp+0x60]
        0x8b, 0x44, 0x24, 0x30, // ASM: mov eax,[rsp+0x30]
        0x01, 0xf0, // ASM: add eax,esi
        0x48, 0x83, 0xc4, 0x58, // ASM: add rsp,0x58
        0xc3, // ASM: ret
    ];
    let text = iso_agrees(&sysv(&code), 0x401000);
    assert!(text.contains("sub_401010(5)"), "{text}");
}

/// A read far above the frame is no argument, not the 32nd one.
///
/// `or qword [rsp+0x1000], 0` over a 0x18-byte frame is a stack probe's
/// touch, 509 words above the return address: the frame scan counted it
/// as the last of 32 stack arguments, so the callee took 38 parameters and
/// its caller passed `rsi` to `r9`, which nothing set.
#[test]
fn a_read_far_above_the_frame_is_no_argument() {
    let code = [
        0xbf, 0x05, 0x00, 0x00, 0x00, // ASM: mov edi,5
        0xe8, 0x06, 0x00, 0x00, 0x00, // ASM: call 0x401010
        0xc3, // ASM: ret
        0xcc, 0xcc, 0xcc, 0xcc, 0xcc, // ASM: int3 (padding)
        0x48, 0x83, 0xec, 0x18, // ASM: sub rsp,0x18
        0x85, 0xff, // ASM: test edi,edi
        0x75, 0x09, // ASM: jne 0x401021
        0x48, 0x83, 0x8c, 0x24, 0x00, 0x10, 0x00, 0x00, 0x00, // ASM: or qword [rsp+0x1000],0
        0x89, 0xf8, // ASM: mov eax,edi
        0x48, 0x83, 0xc4, 0x18, // ASM: add rsp,0x18
        0xc3, // ASM: ret
    ];
    let p = sysv(&code);
    let a = Analysis::compute(&p);
    assert_eq!(a.function(0x401010).map(|f| f.stack_args), Some(0));
    let text = iso_agrees(&p, 0x401000);
    assert!(text.contains("sub_401010(5)"), "{text}");
}

/// A variadic function's register save area is no parameter read, so a
/// function calling it takes nothing through it.
///
/// The callee takes all six integer registers fixed and saves `xmm0` to
/// `xmm7` behind `test al, al`, the count of vector arguments its caller
/// filled, as GCC builds openssh's `sshlog`. Those stores read as the
/// eight vector registers handed on, so the function calling it took nine
/// parameters, and its own caller passed `xmm0` to `xmm7`, which nothing
/// set.
#[test]
fn a_variadic_callee_s_vector_save_area_is_no_parameter() {
    let mut code = vec![
        0xbf, 0x05, 0x00, 0x00, 0x00, // ASM: mov edi,5
        0xe8, 0x06, 0x00, 0x00, 0x00, // ASM: call 0x401010
        0xc3, // ASM: ret
        0xcc, 0xcc, 0xcc, 0xcc, 0xcc, // ASM: int3 (padding)
        0xbe, 0x01, 0x00, 0x00, 0x00, // ASM: mov esi,1
        0xba, 0x02, 0x00, 0x00, 0x00, // ASM: mov edx,2
        0xb9, 0x03, 0x00, 0x00, 0x00, // ASM: mov ecx,3
        0x41, 0xb8, 0x04, 0x00, 0x00, 0x00, // ASM: mov r8d,4
        0x41, 0xb9, 0x05, 0x00, 0x00, 0x00, // ASM: mov r9d,5
        0x31, 0xc0, // ASM: xor eax,eax
        0xe8, 0x0e, 0x00, 0x00, 0x00, // ASM: call 0x401040
        0xc3, // ASM: ret
    ];
    code.resize(0x40, 0xcc);
    code.extend_from_slice(&[
        0x48, 0x81, 0xec, 0xd8, 0x00, 0x00, 0x00, // ASM: sub rsp,0xd8
        0x84, 0xc0, // ASM: test al,al
        0x74, 0x37, // ASM: je 0x401082
        0x0f, 0x29, 0x44, 0x24, 0x50, // ASM: movaps [rsp+0x50],xmm0
        0x0f, 0x29, 0x4c, 0x24, 0x60, // ASM: movaps [rsp+0x60],xmm1
        0x0f, 0x29, 0x54, 0x24, 0x70, // ASM: movaps [rsp+0x70],xmm2
        0x0f, 0x29, 0x9c, 0x24, 0x80, 0x00, 0x00, 0x00, // ASM: movaps [rsp+0x80],xmm3
        0x0f, 0x29, 0xa4, 0x24, 0x90, 0x00, 0x00, 0x00, // ASM: movaps [rsp+0x90],xmm4
        0x0f, 0x29, 0xac, 0x24, 0xa0, 0x00, 0x00, 0x00, // ASM: movaps [rsp+0xa0],xmm5
        0x0f, 0x29, 0xb4, 0x24, 0xb0, 0x00, 0x00, 0x00, // ASM: movaps [rsp+0xb0],xmm6
        0x0f, 0x29, 0xbc, 0x24, 0xc0, 0x00, 0x00, 0x00, // ASM: movaps [rsp+0xc0],xmm7
        0x8d, 0x04, 0x37, // ASM: lea eax,[rdi+rsi]
        0x01, 0xd0, // ASM: add eax,edx
        0x01, 0xc8, // ASM: add eax,ecx
        0x44, 0x01, 0xc0, // ASM: add eax,r8d
        0x44, 0x01, 0xc8, // ASM: add eax,r9d
        0x48, 0x81, 0xc4, 0xd8, 0x00, 0x00, 0x00, // ASM: add rsp,0xd8
        0xc3, // ASM: ret
    ]);
    let text = iso_agrees(&sysv(&code), 0x401000);
    assert!(text.contains("sub_401010(5)"), "{text}");
}

/// A variadic function whose variable arguments are all integers saves no
/// vector half, and its integer save area is no parameter read either.
///
/// The callee takes two fixed arguments, saves `rdx` to `r9` and points
/// `va_start` at the list's stack part (`lea rax, [rsp+0x60]` over its
/// 0x58-byte frame), with no `test al, al` after, as GCC builds gnulib's
/// `rpl_fcntl`. The saves of `rcx`, `r8` and `r9` read as handed on, so the
/// function calling it took six parameters, and its own caller passed `rsi`
/// to `r9`, which nothing set.
#[test]
fn an_integer_save_area_is_no_parameter() {
    let mut code = vec![
        0xbf, 0x05, 0x00, 0x00, 0x00, // ASM: mov edi,5
        0xe8, 0x06, 0x00, 0x00, 0x00, // ASM: call 0x401010
        0xc3, // ASM: ret
        0xcc, 0xcc, 0xcc, 0xcc, 0xcc, // ASM: int3 (padding)
        0xbe, 0x02, 0x00, 0x00, 0x00, // ASM: mov esi,2
        0xba, 0x03, 0x00, 0x00, 0x00, // ASM: mov edx,3
        0x31, 0xc0, // ASM: xor eax,eax
        0xe8, 0x0f, 0x00, 0x00, 0x00, // ASM: call 0x401030
        0xc3, // ASM: ret
    ];
    code.resize(0x30, 0xcc);
    code.extend_from_slice(&[
        0x48, 0x83, 0xec, 0x58, // ASM: sub rsp,0x58
        0x48, 0x89, 0x54, 0x24, 0x30, // ASM: mov [rsp+0x30],rdx
        0x48, 0x89, 0x4c, 0x24, 0x38, // ASM: mov [rsp+0x38],rcx
        0x4c, 0x89, 0x44, 0x24, 0x40, // ASM: mov [rsp+0x40],r8
        0x4c, 0x89, 0x4c, 0x24, 0x48, // ASM: mov [rsp+0x48],r9
        0x48, 0x8d, 0x44, 0x24, 0x60, // ASM: lea rax,[rsp+0x60]
        0x48, 0x89, 0x44, 0x24, 0x08, // ASM: mov [rsp+8],rax
        0x48, 0x8d, 0x44, 0x24, 0x20, // ASM: lea rax,[rsp+0x20]
        0x48, 0x89, 0x44, 0x24, 0x10, // ASM: mov [rsp+0x10],rax
        0x8b, 0x44, 0x24, 0x30, // ASM: mov eax,[rsp+0x30]
        0x01, 0xf8, // ASM: add eax,edi
        0x01, 0xf0, // ASM: add eax,esi
        0x48, 0x83, 0xc4, 0x58, // ASM: add rsp,0x58
        0xc3, // ASM: ret
    ]);
    let text = iso_agrees(&sysv(&code), 0x401000);
    assert!(text.contains("sub_401010(5)"), "{text}");
}

/// A parameter its function only hands on is still its parameter at the
/// call: the register holds it, and the call passes it by its name.
///
/// bash's `sv_execignore(char *name)` jumps to `setup_exec_ignore` with
/// `rdi` untouched, and neither body reads it. Both signatures list the
/// parameter, as the debug information states it, but on System V the
/// entry named only the positions the body reads, so the call passed
/// `rdi`, which no line set, where `name` is.
#[test]
fn a_parameter_handed_on_untouched_is_passed_by_its_name() {
    use borer_engine::dwarf::{Parameter, Subprogram};
    use borer_engine::program::{Symbol, SymbolKind};
    let mut code = vec![
        0xe9, 0x0b, 0x00, 0x00, 0x00, // ASM: jmp 0x401010
    ];
    code.resize(0x10, 0xcc);
    code.extend_from_slice(&[
        0xb8, 0x01, 0x00, 0x00, 0x00, // ASM: mov eax,1
        0xc3, // ASM: ret
    ]);
    let mut p = sysv(&code);
    for (low_pc, name, param) in [
        (0x401000, "sv_execignore", "name"),
        (0x401010, "setup_exec_ignore", "varname"),
    ] {
        p.debug_functions.push(Subprogram {
            low_pc,
            name: name.to_owned(),
            parameters: vec![Parameter {
                name: param.to_owned(),
                type_name: Some("char *".to_owned()),
            }],
            return_type: Some("int".to_owned()),
            locals: std::collections::BTreeMap::new(),
        });
        p.symbols.push(Symbol {
            name: name.to_owned(),
            addr: low_pc,
            kind: SymbolKind::Export,
        });
    }
    let text = iso_agrees(&p, 0x401000);
    assert!(text.contains("setup_exec_ignore(name)"), "{text}");
}

/// A callee whose arity nothing states takes no slot whose register
/// nothing set, whatever the call's block set after it.
///
/// The block stores `rdx` for a copy of its own and sets `rdi`, then calls
/// a callee whose body says nothing of its arity (one jump through a
/// pointer, as an import's thunk is). `rdx` set in the block bridged the
/// hole at `rsi`, and the call passed `rsi`, which nothing set (dpkg's
/// `MD5Init(var1, rsi, var1)`).
#[test]
fn a_hole_ends_the_list_of_a_callee_of_unknown_arity() {
    let mut code = vec![
        0x48, 0x89, 0xf8, // ASM: mov rax,rdi
        0x48, 0x8b, 0x17, // ASM: mov rdx,[rdi]
        0x48, 0x89, 0x57, 0x08, // ASM: mov [rdi+8],rdx
        0x48, 0x89, 0xc7, // ASM: mov rdi,rax
        0xe8, 0x02, 0x00, 0x00, 0x00, // ASM: call 0x401014
        0xc3, // ASM: ret
        0xcc, // ASM: int3 (padding)
        0xff, 0x25, 0xe6, 0x0f, 0x00, 0x00, // ASM: jmp qword [rip+0xfe6] (0x402000)
    ];
    code.resize(0x20, 0xcc);
    code.extend_from_slice(&[
        0xb8, 0x07, 0x00, 0x00, 0x00, // ASM: mov eax,7
        0xc3, // ASM: ret
    ]);
    let mut p = crate::raw::image(Arch::X86_64, &code, &0x0040_1020u64.to_le_bytes());
    p.format = BinaryFormat::Elf;
    let text = iso_agrees(&p, 0x401000);
    assert!(text.contains("sub_401014(a1)"), "{text}");
}

/// A register an earlier call only clobbered is no argument of a callee
/// whose arity nothing states either.
///
/// dpkg's `buffer_md5_init` calls `m_malloc` first, so `rsi` holds what
/// that call left, then stores `rdx` for a copy of its own and calls
/// `MD5Init` through its import stub. The clobbered `rsi` counted as set,
/// bridged to `rdx`, and the call read `MD5Init(var1, rsi, var1)`.
#[test]
fn a_register_an_earlier_call_left_is_no_argument_of_an_unknown_callee() {
    let mut code = vec![
        0x53, // ASM: push rbx
        0x48, 0x89, 0xfb, // ASM: mov rbx,rdi
        0xe8, 0x1f, 0x00, 0x00, 0x00, // ASM: call 0x401028
        0x48, 0x8b, 0x13, // ASM: mov rdx,[rbx]
        0x48, 0x89, 0x53, 0x08, // ASM: mov [rbx+8],rdx
        0x48, 0x89, 0xdf, // ASM: mov rdi,rbx
        0xe8, 0x08, 0x00, 0x00, 0x00, // ASM: call 0x401020
        0x5b, // ASM: pop rbx
        0xc3, // ASM: ret
    ];
    code.resize(0x20, 0xcc);
    code.extend_from_slice(&[
        0xff, 0x25, 0xda, 0x0f, 0x00, 0x00, // ASM: jmp qword [rip+0xfda] (0x402000)
        0xcc, 0xcc, // ASM: int3 (padding)
        0x31, 0xf6, // ASM: xor esi,esi
        0xb8, 0x01, 0x00, 0x00, 0x00, // ASM: mov eax,1
        0xc3, // ASM: ret
    ]);
    code.extend_from_slice(&[
        0xb8, 0x07, 0x00, 0x00, 0x00, // ASM: mov eax,7
        0xc3, // ASM: ret
    ]);
    let mut p = crate::raw::image(Arch::X86_64, &code, &0x0040_1030u64.to_le_bytes());
    p.format = BinaryFormat::Elf;
    let text = iso_agrees(&p, 0x401000);
    assert!(text.contains("sub_401020(a1)"), "{text}");
}

/// A frame taken in several steps places every read against all of them.
///
/// Under stack-clash probing a large frame is allocated a page at a time:
/// `sub rsp, 0x1000; or qword [rsp], 0; sub rsp, 0xb0`. The frame scan kept
/// only the first step, so the local at `[rsp+0x10a8]` (openssh's
/// `sshbuf_load_fd` keeps its canary there) read as stack argument 20, the
/// callee took 26 parameters, and its caller passed `rsi` to `r9`, which
/// nothing set.
#[test]
fn a_frame_taken_in_steps_is_one_frame() {
    let mut code = vec![
        0xbf, 0x05, 0x00, 0x00, 0x00, // ASM: mov edi,5
        0xe8, 0x06, 0x00, 0x00, 0x00, // ASM: call 0x401010
        0xc3, // ASM: ret
    ];
    code.resize(0x10, 0xcc);
    code.extend_from_slice(&[
        0x53, // ASM: push rbx
        0x48, 0x81, 0xec, 0x00, 0x10, 0x00, 0x00, // ASM: sub rsp,0x1000
        0x48, 0x83, 0x0c, 0x24, 0x00, // ASM: or qword [rsp],0
        0x48, 0x81, 0xec, 0xb0, 0x00, 0x00, 0x00, // ASM: sub rsp,0xb0
        0x48, 0x89, 0xbc, 0x24, 0xa8, 0x10, 0x00, 0x00, // ASM: mov [rsp+0x10a8],rdi
        0x8b, 0x84, 0x24, 0xa8, 0x10, 0x00, 0x00, // ASM: mov eax,[rsp+0x10a8]
        0x48, 0x81, 0xc4, 0xb0, 0x10, 0x00, 0x00, // ASM: add rsp,0x10b0
        0x5b, // ASM: pop rbx
        0xc3, // ASM: ret
    ]);
    let p = sysv(&code);
    let a = Analysis::compute(&p);
    assert_eq!(a.function(0x401010).map(|f| f.stack_args), Some(0));
    let text = iso_agrees(&p, 0x401000);
    assert!(text.contains("sub_401010(5)"), "{text}");
}
