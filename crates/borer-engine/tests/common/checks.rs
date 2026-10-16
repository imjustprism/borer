//! The license-check fixtures of the shared image.
//!
//! A phrase-named synchronization wrapper and a phrase-less input reader,
//! laid down at the bottom of `.text2` and in the span of `.data` above
//! every other fixture, which [`code_bytes`](super::code_bytes) and
//! [`data_bytes`](super::data_bytes) call for.

use super::{put, put_rdata};

/// Lays down the check code at 0x5c00 and 0x5c40.
///
/// `FX` compares rwlock state bits while mentioning a check phrase, and
/// `KC` reads input through scanf and compares a byte of what it read
/// against the value the call parsed.
///
/// # Arguments
///
/// * `bytes` - The image being built.
pub(crate) fn code(bytes: &mut [u8]) {
    put(bytes, 0x5c00, &[0x48, 0x8d, 0x0d, 0x19, 0xe1, 0xff, 0xff]); // ASM: lea rcx,[rip-0x1ee7] -> 0x3d20 (FX)
    put(bytes, 0x5c07, &[0x48, 0x3d, 0x00, 0x00, 0x00, 0x40]); // ASM: cmp rax,0x40000000
    put(bytes, 0x5c0d, &[0x48, 0x3d, 0x00, 0x00, 0x00, 0xc0]); // ASM: cmp rax,0xc0000000
    put(bytes, 0x5c13, &[0xc3]); // ASM: ret
    put(bytes, 0x5c40, &[0x53]); // ASM: push rbx (KC)
    put(bytes, 0x5c41, &[0x48, 0x8b, 0xd9]); // ASM: mov rbx,rcx
    put(bytes, 0x5c44, &[0x48, 0x8d, 0x0d, 0x15, 0xe1, 0xff, 0xff]); // ASM: lea rcx,[rip-0x1eeb] -> 0x3d60
    put(bytes, 0x5c4b, &[0x48, 0x8b, 0xd3]); // ASM: mov rdx,rbx
    put(bytes, 0x5c4e, &[0xff, 0x15, 0x4c, 0xe1, 0xff, 0xff]); // ASM: call [rip-0x1eb4] -> 0x3da0 (scanf)
    put(bytes, 0x5c54, &[0x0f, 0xb6, 0x0b]); // ASM: movzx ecx,byte [rbx]
    put(bytes, 0x5c57, &[0x3b, 0xc8]); // ASM: cmp ecx,eax
    put(bytes, 0x5c59, &[0x0f, 0x94, 0xc0]); // ASM: sete al
    put(bytes, 0x5c5c, &[0x0f, 0xb6, 0xc0]); // ASM: movzx eax,al
    put(bytes, 0x5c5f, &[0x5b]); // ASM: pop rbx
    put(bytes, 0x5c60, &[0xc3]); // ASM: ret
}

/// Lays down the check data at 0x3d20 and beyond.
///
/// The phrase string `FX` references, the scanf format `KC` passes, the
/// import slot its call goes through, and the pointers that seed both as
/// functions.
///
/// # Arguments
///
/// * `bytes` - The image being built.
pub(crate) fn rdata(bytes: &mut [u8]) {
    put_rdata(bytes, 0x3d20, b"assertion failed: is_unlocked(state)\0");
    put_rdata(bytes, 0x3d60, b"%d\0");
    put_rdata(bytes, 0x3da0, &0u64.to_le_bytes());
    put_rdata(bytes, 0x3e00, &0x5c00u64.to_le_bytes());
    put_rdata(bytes, 0x3e08, &0x5c40u64.to_le_bytes());
}
