//! Guarded regions in the pseudo-C: the code a `try` or `__try` protects
//! is written inside one, and the code its handler runs inside the
//! handler, for each kind of exception metadata.

use borer_engine::headers::ExceptionHandler;
use borer_engine::program::{Arch, Program, Section};

use crate::decompiled::decompiled;

/// Image base of the PE-like fixtures.
const BASE: u64 = 0x1_4000_0000;

/// Asserts that `needles` appear in `text` in order.
///
/// # Arguments
///
/// * `text` - The pseudo-C.
/// * `needles` - What must appear, in order.
///
/// # Panics
///
/// When one is missing or out of order.
#[expect(
    clippy::panic,
    reason = "a test helper; the panic names the missing needle and the text"
)]
fn in_order(text: &str, needles: &[&str]) {
    let mut at = 0;
    for n in needles {
        let Some(k) = text[at..].find(n) else {
            panic!("{n:?} missing after byte {at}:\n{text}");
        };
        at += k + n.len();
    }
}

/// An Itanium landing pad that catches one type is the `catch` of a
/// `try` around the call sites that land on it, and its code is the
/// clause's body.
///
/// # Panics
///
/// When the `try` or the `catch` is missing.
#[test]
fn an_itanium_landing_pad_is_a_catch() {
    let p = crate::lsda::throwing(true);
    let text = decompiled(&p, 0x1000);
    in_order(
        &text,
        &["try {\n", "} catch (foo::Bar) {\n", "return 1;\n", "}\n"],
    );
}

/// Builds an x64 image with one function whose scope table guards its
/// call with `__except (EXCEPTION_EXECUTE_HANDLER)`, the `__except` body
/// inside the function.
///
/// # Panics
///
/// Never: the layout is fixed.
fn seh64() -> Program {
    let mut bytes = vec![0xccu8; 0x2100];
    let code: &[(usize, &[u8])] = &[
        (0x1000, &[0x48, 0x83, 0xec, 0x28]),       // ASM: sub rsp, 0x28
        (0x1004, &[0xe8, 0xf7, 0x00, 0x00, 0x00]), // ASM: call 0x1100
        (0x1009, &[0x48, 0x83, 0xc4, 0x28]),       // ASM: add rsp, 0x28
        (0x100d, &[0xc3]),                         // ASM: ret
        (0x1010, &[0xb8, 0xff, 0xff, 0xff, 0xff]), // ASM: mov eax, -1
        (0x1015, &[0x48, 0x83, 0xc4, 0x28]),       // ASM: add rsp, 0x28
        (0x1019, &[0xc3]),                         // ASM: ret
        (0x1100, &[0x8b, 0x01]),                   // ASM: mov eax, [rcx]
        (0x1102, &[0xc3]),                         // ASM: ret
        (0x1180, &[0xc3]),                         // ASM: ret
    ];
    for (at, b) in code {
        bytes[*at..*at + b.len()].copy_from_slice(b);
    }
    for (k, v) in [1u32, 0x1004, 0x1009, 1, 0x1010].iter().enumerate() {
        bytes[0x2000 + 4 * k..0x2004 + 4 * k].copy_from_slice(&v.to_le_bytes());
    }
    let sections = vec![
        Section::mapped(".text", BASE + 0x1000, 0x1000, 0x1000, false, true),
        Section::mapped(".rdata", BASE + 0x2000, 0x2000, 0x100, false, false),
    ];
    let mut p = Program::raw(bytes, Arch::X86_64, BASE, Some(BASE + 0x1000), sections);
    p.function_ranges = vec![
        (BASE + 0x1000, BASE + 0x101a),
        (BASE + 0x1100, BASE + 0x1103),
    ];
    p.headers.exception_handlers = vec![ExceptionHandler {
        function: BASE + 0x1000,
        handler: BASE + 0x1180,
        data: BASE + 0x2000,
    }];
    p
}

/// A scope-table record is a `__try` around its range, its `__except`
/// written with the constant filter and its body the function's own code
/// the runtime resumes at.
///
/// # Panics
///
/// When the `__try` or the `__except` is missing.
#[test]
fn a_scope_table_record_is_a_try_except() {
    let text = decompiled(&seh64(), BASE + 0x1000);
    in_order(
        &text,
        &[
            "__try {\n",
            "sub_140001100(",
            "} __except (EXCEPTION_EXECUTE_HANDLER) {\n",
            "return 0xffffffff;\n",
            "}\n",
        ],
    );
}

/// Builds a 32-bit image whose function registers `_except_handler4`
/// inline, enters `__try` 0 around a call by storing its index at
/// `[ebp-4]`, and leaves it by storing `-2`.
///
/// # Panics
///
/// Never: the layout is fixed.
fn seh32() -> Program {
    const IMAGE: u64 = 0x40_0000;
    let mut bytes = vec![0xccu8; 0x2100];
    let code: &[(usize, &[u8])] = &[
        (0x1000, &[0x55]),                                     // ASM: push ebp
        (0x1001, &[0x8b, 0xec]),                               // ASM: mov ebp, esp
        (0x1003, &[0x6a, 0xfe]),                               // ASM: push -2
        (0x1005, &[0x68, 0x00, 0x20, 0x40, 0x00]),             // ASM: push 0x402000
        (0x100a, &[0x68, 0x80, 0x11, 0x40, 0x00]),             // ASM: push 0x401180
        (0x100f, &[0x64, 0xa1, 0x00, 0x00, 0x00, 0x00]),       // ASM: mov eax, fs:[0]
        (0x1015, &[0x50]),                                     // ASM: push eax
        (0x1016, &[0xc7, 0x45, 0xfc, 0x00, 0x00, 0x00, 0x00]), // ASM: mov dword [ebp-4], 0
        (0x101d, &[0xe8, 0xde, 0x00, 0x00, 0x00]),             // ASM: call 0x401100
        (0x1022, &[0xc7, 0x45, 0xfc, 0xfe, 0xff, 0xff, 0xff]), // ASM: mov dword [ebp-4], -2
        (0x1029, &[0x8b, 0xe5]),                               // ASM: mov esp, ebp
        (0x102b, &[0x5d]),                                     // ASM: pop ebp
        (0x102c, &[0xc3]),                                     // ASM: ret
        (0x1030, &[0xb8, 0xff, 0xff, 0xff, 0xff]),             // ASM: mov eax, -1
        (0x1035, &[0x8b, 0xe5]),                               // ASM: mov esp, ebp
        (0x1037, &[0x5d]),                                     // ASM: pop ebp
        (0x1038, &[0xc3]),                                     // ASM: ret
        (0x1040, &[0xb8, 0x01, 0x00, 0x00, 0x00]),             // ASM: mov eax, 1
        (0x1045, &[0xc3]),                                     // ASM: ret
        (0x1100, &[0x33, 0xc0]),                               // ASM: xor eax, eax
        (0x1102, &[0xc3]),                                     // ASM: ret
        (0x1180, &[0xc3]),                                     // ASM: ret
    ];
    for (at, b) in code {
        bytes[*at..*at + b.len()].copy_from_slice(b);
    }
    let table = [
        0xffff_fffe_u32,
        0,
        0xffff_fffe,
        0,
        0xffff_fffe,
        0x40_1040,
        0x40_1030,
    ];
    for (k, v) in table.iter().enumerate() {
        bytes[0x2000 + 4 * k..0x2004 + 4 * k].copy_from_slice(&v.to_le_bytes());
    }
    let sections = vec![
        Section::mapped(".text", IMAGE + 0x1000, 0x1000, 0x1000, false, true),
        Section::mapped(".rdata", IMAGE + 0x2000, 0x2000, 0x100, false, false),
    ];
    Program::raw(bytes, Arch::X86, IMAGE, Some(IMAGE + 0x1000), sections)
}

/// A 32-bit `__try` is the instructions run while the frame's index is
/// its own: the call between the two stores is guarded, and the
/// `__except` body the scope table names is its handler.
///
/// # Panics
///
/// When the `__try` or the `__except` is missing.
#[test]
fn a_32_bit_try_level_is_a_try_except() {
    let text = decompiled(&seh32(), 0x40_1000);
    in_order(
        &text,
        &[
            "__try {\n",
            "sub_401100(",
            "} __except (",
            ") {\n",
            "return -1;\n",
            "}\n",
        ],
    );
}
