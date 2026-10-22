//! Parameter types read off the code: what a function's own accesses and
//! the calls it makes show its parameters to be.

#![expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]

use crate::decompiled;
use borer_engine::analysis::decompile::decompile;
use borer_engine::analysis::{Analysis, Overlay};
use decompiled::{program64, replays_clean};

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
