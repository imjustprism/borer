//! The interlocked-operation fixtures of the shared image.
//!
//! `LKO`, `XA` and `CX` at the top of the `.text2` space the virtual-call
//! fixtures leave, laid down by [`code_bytes`](super::code_bytes), which
//! the seeds in [`data_bytes`](super::data_bytes) point the analysis at.

use super::put;

/// Lays down the interlocked-operation code.
///
/// `LKO` 0x5900 sets a flag bit with `lock or` and returns one; `XA`
/// 0x5910 adds through `xadd` and branches on the sum; `CX` 0x5930
/// compares and exchanges and branches on the match.
///
/// # Arguments
///
/// * `bytes` - The image being built.
pub(crate) fn code(bytes: &mut [u8]) {
    put(
        bytes,
        0x5900,
        &[0xf0, 0x83, 0x49, 0x10, 0x40], // ASM: lock or dword [rcx+0x10],0x40 (LKO)
    );
    put(bytes, 0x5905, &[0xb8, 0x01, 0x00, 0x00, 0x00]); // ASM: mov eax,1
    put(bytes, 0x590a, &[0xc3]); // ASM: ret
    put(bytes, 0x5910, &[0x89, 0x54, 0x24, 0x18]); // ASM: mov [rsp+0x18],edx (XA)
    put(bytes, 0x5914, &[0xb8, 0x10, 0x00, 0x00, 0x00]); // ASM: mov eax,0x10
    put(bytes, 0x5919, &[0x0f, 0xc1, 0x44, 0x24, 0x18]); // ASM: xadd [rsp+0x18],eax
    put(bytes, 0x591e, &[0x74, 0x06]); // ASM: jz 0x5926 (Z)
    put(bytes, 0x5920, &[0xb8, 0x02, 0x00, 0x00, 0x00]); // ASM: mov eax,2
    put(bytes, 0x5925, &[0xc3]); // ASM: ret
    put(bytes, 0x5926, &[0x31, 0xc0]); // ASM: xor eax,eax (Z)
    put(bytes, 0x5928, &[0xc3]); // ASM: ret
    put(bytes, 0x5930, &[0xb8, 0x05, 0x00, 0x00, 0x00]); // ASM: mov eax,5 (CX)
    put(bytes, 0x5935, &[0x0f, 0xb1, 0x11]); // ASM: cmpxchg [rcx],edx
    put(bytes, 0x5938, &[0x74, 0x06]); // ASM: jz 0x5940 (S)
    put(bytes, 0x593a, &[0xb8, 0x02, 0x00, 0x00, 0x00]); // ASM: mov eax,2
    put(bytes, 0x593f, &[0xc3]); // ASM: ret
    put(bytes, 0x5940, &[0x31, 0xc0]); // ASM: xor eax,eax (S)
    put(bytes, 0x5942, &[0xc3]); // ASM: ret
}
