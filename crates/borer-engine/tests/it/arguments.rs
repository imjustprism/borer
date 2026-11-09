//! What a call passes: the arguments its callee takes, and none that
//! nothing set.
//!
//! Each fixture is a hand-assembled System V caller at 0x401000 and its
//! callee after it in a raw image. The caller's text runs beside the binary
//! ([`crate::decompiled::runs_agree`]), so an argument that reads a
//! register no line sets fails the run as it fails certify.

#![expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]

use borer_engine::analysis::Analysis;
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
    let text = crate::decompiled::runs_agree(&p, 0x401000);
    assert!(text.contains("sub_401010(5)"), "{text}");
}
