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
