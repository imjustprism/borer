//! The virtual-call fixtures of the shared image.
//!
//! The TLS singleton and the embedded base field, laid down at the top of
//! `.text2` and in the span of `.data` below the RTTI fixtures, which
//! [`code_bytes`](super::code_bytes) and [`data_bytes`](super::data_bytes)
//! call for.

use super::{put, put_rdata};

/// Lays down the virtual-call code at 0x5760...
///
/// `T2::T2` with its slots and `TW`, then `WBase::WBase`, `Wrap::Wrap`,
/// `Wrap::Call`, `Wrap::Miss` and the four slots, every rip-relative
/// displacement set for these addresses.
///
/// # Arguments
///
/// * `bytes` - The image being built.
pub(crate) fn code(bytes: &mut [u8]) {
    put(bytes, 0x5760, &[0x48, 0x89, 0xcb]); // ASM: mov rbx,rcx (T2)
    put(bytes, 0x5763, &[0x48, 0x8d, 0x05, 0xb6, 0xdd, 0xff, 0xff]); // ASM: lea rax,[rip+..] -> 0x3520
    put(bytes, 0x576a, &[0x48, 0x89, 0x03]); // ASM: mov [rbx],rax
    put(
        bytes,
        0x576d,
        &[0x65, 0x48, 0x8b, 0x04, 0x25, 0x58, 0x00, 0x00, 0x00],
    ); // ASM: mov rax,gs:[0x58]
    put(bytes, 0x5776, &[0x8b, 0x0d, 0xa4, 0xcf, 0xff, 0xff]); // ASM: mov ecx,[rip+..] -> 0x2720 (_tls_index)
    put(bytes, 0x577c, &[0x48, 0x8b, 0x04, 0xc8]); // ASM: mov rax,[rax+rcx*8]
    put(bytes, 0x5780, &[0xbd, 0x18, 0x00, 0x00, 0x00]); // ASM: mov ebp,0x18
    put(bytes, 0x5785, &[0x48, 0x89, 0x1c, 0x28]); // ASM: mov [rax+rbp],rbx
    put(bytes, 0x5789, &[0x48, 0x8d, 0x15, 0xb0, 0xdd, 0xff, 0xff]); // ASM: lea rdx,[rip+..] -> 0x3540
    put(bytes, 0x5790, &[0xc3]); // ASM: ret
    put(
        bytes,
        0x57a0,
        &[0x65, 0x48, 0x8b, 0x04, 0x25, 0x58, 0x00, 0x00, 0x00],
    ); // ASM: mov rax,gs:[0x58] (TW)
    put(bytes, 0x57a9, &[0x8b, 0x0d, 0x71, 0xcf, 0xff, 0xff]); // ASM: mov ecx,[rip+..] -> 0x2720
    put(bytes, 0x57af, &[0x48, 0x8b, 0x04, 0xc8]); // ASM: mov rax,[rax+rcx*8]
    put(bytes, 0x57b3, &[0x48, 0x8b, 0x48, 0x18]); // ASM: mov rcx,[rax+0x18]
    put(bytes, 0x57b7, &[0x48, 0x8b, 0x01]); // ASM: mov rax,[rcx]
    put(bytes, 0x57ba, &[0xff, 0x50, 0x08]); // ASM: call qword ptr [rax+8]
    put(bytes, 0x57bd, &[0xc3]); // ASM: ret
    put(bytes, 0x57c0, &[0xb8, 0x05, 0x00, 0x00, 0x00]); // ASM: mov eax,5 (T2 slot 0)
    put(bytes, 0x57c5, &[0xc3]); // ASM: ret
    put(bytes, 0x57c6, &[0xb8, 0x06, 0x00, 0x00, 0x00]); // ASM: mov eax,6 (T2 slot 1)
    put(bytes, 0x57cb, &[0xc3]); // ASM: ret
    put(bytes, 0x57e0, &[0x48, 0x8d, 0x05, 0x99, 0xdd, 0xff, 0xff]); // ASM: lea rax,[rip+..] -> 0x3580
    put(bytes, 0x57e7, &[0x48, 0x89, 0x01]); // ASM: mov [rcx],rax
    put(bytes, 0x57ea, &[0x48, 0x8d, 0x15, 0xcf, 0xdd, 0xff, 0xff]); // ASM: lea rdx,[rip+..] -> 0x35c0
    put(bytes, 0x57f1, &[0xc3]); // ASM: ret
    put(bytes, 0x5800, &[0x48, 0x89, 0xcb]); // ASM: mov rbx,rcx
    put(bytes, 0x5803, &[0x48, 0x8d, 0x05, 0x96, 0xdd, 0xff, 0xff]); // ASM: lea rax,[rip+..] -> 0x35a0
    put(bytes, 0x580a, &[0x48, 0x89, 0x03]); // ASM: mov [rbx],rax
    put(bytes, 0x580d, &[0x48, 0x8d, 0x05, 0x6c, 0xdd, 0xff, 0xff]); // ASM: lea rax,[rip+..] -> 0x3580
    put(bytes, 0x5814, &[0x48, 0x89, 0x43, 0x08]); // ASM: mov [rbx+8],rax
    put(bytes, 0x5818, &[0x48, 0x8d, 0x15, 0xc1, 0xdd, 0xff, 0xff]); // ASM: lea rdx,[rip+..] -> 0x35e0
    put(bytes, 0x581f, &[0xc3]); // ASM: ret
    put(bytes, 0x5830, &[0x48, 0x8b, 0x41, 0x08]); // ASM: mov rax,[rcx+8]
    put(bytes, 0x5834, &[0xff, 0x50, 0x08]); // ASM: call qword ptr [rax+8]
    put(bytes, 0x5837, &[0x48, 0x8d, 0x15, 0xf2, 0xdb, 0xff, 0xff]); // ASM: lea rdx,[rip+..] -> 0x3430
    put(bytes, 0x583e, &[0xc3]); // ASM: ret
    put(bytes, 0x5850, &[0x48, 0x8b, 0x41, 0x10]); // ASM: mov rax,[rcx+0x10]
    put(bytes, 0x5854, &[0xff, 0x50, 0x08]); // ASM: call qword ptr [rax+8]
    put(bytes, 0x5857, &[0x48, 0x8d, 0x15, 0xf2, 0xdb, 0xff, 0xff]); // ASM: lea rdx,[rip+..] -> 0x3450
    put(bytes, 0x585e, &[0xc3]); // ASM: ret
    put(bytes, 0x5870, &[0xb8, 0x07, 0x00, 0x00, 0x00]); // ASM: mov eax,7 (WBase slot 0)
    put(bytes, 0x5875, &[0xc3]); // ASM: ret
    put(bytes, 0x5876, &[0xb8, 0x08, 0x00, 0x00, 0x00]); // ASM: mov eax,8 (WBase slot 1)
    put(bytes, 0x587b, &[0xc3]); // ASM: ret
    put(bytes, 0x587c, &[0xb8, 0x09, 0x00, 0x00, 0x00]); // ASM: mov eax,9 (Wrap slot 0)
    put(bytes, 0x5881, &[0xc3]); // ASM: ret
    put(bytes, 0x5882, &[0xb8, 0x0a, 0x00, 0x00, 0x00]); // ASM: mov eax,0xa (Wrap slot 1)
    put(bytes, 0x5887, &[0xc3]); // ASM: ret
}

/// Lays down the virtual-call data.
///
/// `T2`'s vtable, signature and seeds at 0x3520.., `WBase`'s and `Wrap`'s
/// vtables at 0x3580.., their constructors' signatures at 0x35c0.., the
/// methods' at 0x3430.. and the seeds of the four functions at 0x3470..,
/// all in the span below the RTTI fixtures that start at 0x3600.
///
/// # Arguments
///
/// * `bytes` - The image being built.
pub(crate) fn data(bytes: &mut [u8]) {
    put_rdata(bytes, 0x3520, &0x57c0u64.to_le_bytes());
    put_rdata(bytes, 0x3528, &0x57c6u64.to_le_bytes());
    put_rdata(bytes, 0x3530, &0u64.to_le_bytes());
    put_rdata(bytes, 0x3540, b"__cdecl T2::T2(void)\0");
    put_rdata(bytes, 0x3560, &0x5760u64.to_le_bytes());
    put_rdata(bytes, 0x3568, &0x57a0u64.to_le_bytes());
    put_rdata(bytes, 0x3580, &0x5870u64.to_le_bytes());
    put_rdata(bytes, 0x3588, &0x5876u64.to_le_bytes());
    put_rdata(bytes, 0x3590, &0u64.to_le_bytes());
    put_rdata(bytes, 0x35a0, &0x587cu64.to_le_bytes());
    put_rdata(bytes, 0x35a8, &0x5882u64.to_le_bytes());
    put_rdata(bytes, 0x35b0, &0u64.to_le_bytes());
    put_rdata(bytes, 0x35c0, b"__cdecl WBase::WBase(void)\0");
    put_rdata(bytes, 0x35e0, b"__cdecl Wrap::Wrap(void)\0");
    put_rdata(bytes, 0x3430, b"void __cdecl Wrap::Call(void)\0");
    put_rdata(bytes, 0x3450, b"void __cdecl Wrap::Miss(void)\0");
    put_rdata(bytes, 0x3470, &0x57e0u64.to_le_bytes());
    put_rdata(bytes, 0x3478, &0x5800u64.to_le_bytes());
    put_rdata(bytes, 0x3480, &0x5830u64.to_le_bytes());
    put_rdata(bytes, 0x3488, &0x5850u64.to_le_bytes());
}
