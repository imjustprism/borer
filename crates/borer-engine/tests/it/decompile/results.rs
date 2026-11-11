//! Results: what a function hands back, in which register and at what width.

use super::*;

/// A callee some caller reads `rdx` after is noted as handing a second
/// value back, and one no caller reads is not.
///
/// The calling convention leaves `rdx` to the callee to clobber, so a read
/// before a write after the call wants the callee's own value there: the
/// note is what tells a reader the register is a second result and not
/// stale.
#[test]
fn a_callee_whose_callers_read_rdx_hands_it_back() {
    use borer_engine::program::{Arch, BinaryFormat, Program, Section};
    let mut code = vec![
        0xe8, 0x1b, 0x00, 0x00, 0x00, // ASM: call 0x401020
        0x48, 0x89, 0xd3, // ASM: mov rbx,rdx
        0x48, 0x89, 0xd8, // ASM: mov rax,rbx
        0xc3, // ASM: ret
    ];
    code.resize(0x20, 0xcc);
    code.extend_from_slice(&[
        0xb8, 0x01, 0x00, 0x00, 0x00, // ASM: mov eax,1
        0xba, 0x02, 0x00, 0x00, 0x00, // ASM: mov edx,2
        0xc3, // ASM: ret
    ]);
    code.resize(0x30, 0xcc);
    code.extend_from_slice(&[
        0xb8, 0x03, 0x00, 0x00, 0x00, // ASM: mov eax,3
        0xc3, // ASM: ret
    ]);
    code.resize(0x40, 0xcc);
    code.extend_from_slice(&[
        0xe8, 0xeb, 0xff, 0xff, 0xff, // ASM: call 0x401030
        0xc3, // ASM: ret
    ]);
    let mut bytes = vec![0u8; 0x1000];
    bytes[..code.len()].copy_from_slice(&code);
    let mut p = Program::raw(
        bytes,
        Arch::X86_64,
        0x400_000,
        Some(0x401_000),
        vec![Section::mapped(".text", 0x401_000, 0, 0x1000, false, true)],
    );
    p.format = BinaryFormat::Pe;
    let pair = decompiled(&p, 0x401_020);
    assert!(pair.contains("// hands back rdx"), "{pair}");
    let solo = decompiled(&p, 0x401_030);
    assert!(!solo.contains("hands back rdx"), "{solo}");
}

/// On a 32-bit target the second value a callee hands back is in `edx`,
/// and the note names that register.
///
/// # Panics
///
/// When the note names `rdx` or is missing.
#[test]
fn a_32_bit_callee_hands_back_edx() {
    use borer_engine::program::{Arch, BinaryFormat, Program, Section};
    let mut code = vec![
        0xe8, 0x1b, 0x00, 0x00, 0x00, // ASM: call 0x401020
        0x89, 0xd3, // ASM: mov ebx,edx
        0x89, 0xd8, // ASM: mov eax,ebx
        0xc3, // ASM: ret
    ];
    code.resize(0x20, 0xcc);
    code.extend_from_slice(&[
        0xb8, 0x01, 0x00, 0x00, 0x00, // ASM: mov eax,1
        0xba, 0x02, 0x00, 0x00, 0x00, // ASM: mov edx,2
        0xc3, // ASM: ret
    ]);
    let mut bytes = vec![0u8; 0x1000];
    bytes[..code.len()].copy_from_slice(&code);
    let mut p = Program::raw(
        bytes,
        Arch::X86,
        0x400_000,
        Some(0x401_000),
        vec![Section::mapped(".text", 0x401_000, 0, 0x1000, false, true)],
    );
    p.format = BinaryFormat::Pe;
    let pair = decompiled(&p, 0x401_020);
    assert!(pair.contains("// hands back edx"), "{pair}");
    assert!(!pair.contains("rdx"), "{pair}");
}

/// A function handing a second result back in `rdx` says what it is
/// before its `return`.
///
/// `mov eax,1; mov edx,2; ret`, whose caller reads `rdx` after the call:
/// the text said only `return 1;`, and the `2` the caller reads as
/// `sub_401020__rdx()` was nowhere in it.
#[test]
fn a_second_result_handed_back_is_in_the_text() {
    use borer_engine::program::{Arch, BinaryFormat, Program, Section};
    let mut code = vec![
        0xe8, 0x1b, 0x00, 0x00, 0x00, // ASM: call 0x401020
        0x48, 0x89, 0xd3, // ASM: mov rbx,rdx
        0x48, 0x89, 0xd8, // ASM: mov rax,rbx
        0xc3, // ASM: ret
    ];
    code.resize(0x20, 0xcc);
    code.extend_from_slice(&[
        0xb8, 0x01, 0x00, 0x00, 0x00, // ASM: mov eax,1
        0xba, 0x02, 0x00, 0x00, 0x00, // ASM: mov edx,2
        0xc3, // ASM: ret
    ]);
    let mut bytes = vec![0u8; 0x1000];
    bytes[..code.len()].copy_from_slice(&code);
    let mut p = Program::raw(
        bytes,
        Arch::X86_64,
        0x400_000,
        Some(0x401_000),
        vec![Section::mapped(".text", 0x401_000, 0, 0x1000, false, true)],
    );
    p.format = BinaryFormat::Pe;
    let pair = decompiled(&p, 0x401_020);
    assert!(pair.contains("rdx = 2;\nreturn 1;"), "{pair}");
}

/// A result read through the register the second result comes back in is
/// taken before the line that replaces that register.
///
/// `mov rdx,[rcx]; lea rax,[rdx+16]; mov [rcx],rax; mov rax,[rdx]; mov
/// rdx,[rdx+8]; ret` pops a 128-bit value off an argument list, and its
/// caller reads `rdx` after the call: written `rdx = *(uint64_t*)(rdx +
/// 8); return *(uint64_t*)rdx;`, the return read the new `rdx`, which
/// the check of the text names as a disagreement.
///
/// # Panics
///
/// When the return reads `rdx` after the line that replaces it.
#[test]
fn a_result_read_through_the_second_one_is_taken_first() {
    use borer_engine::analysis::decompile::checked_header;
    use borer_engine::program::{Arch, BinaryFormat, Program, Section};
    let mut code = vec![
        0xe8, 0x3b, 0x00, 0x00, 0x00, // ASM: call 0x401040
        0x48, 0x89, 0xd3, // ASM: mov rbx,rdx
        0x48, 0x89, 0xd8, // ASM: mov rax,rbx
        0xc3, // ASM: ret
    ];
    code.resize(0x40, 0xcc);
    code.extend_from_slice(&[
        0x48, 0x8b, 0x11, // ASM: mov rdx,[rcx]
        0x48, 0x8d, 0x42, 0x10, // ASM: lea rax,[rdx+16]
        0x48, 0x89, 0x01, // ASM: mov [rcx],rax
        0x48, 0x8b, 0x02, // ASM: mov rax,[rdx]
        0x48, 0x8b, 0x52, 0x08, // ASM: mov rdx,[rdx+8]
        0xc3, // ASM: ret
    ]);
    let mut bytes = vec![0u8; 0x1000];
    bytes[..code.len()].copy_from_slice(&code);
    let mut p = Program::raw(
        bytes,
        Arch::X86_64,
        0x400_000,
        Some(0x401_000),
        vec![Section::mapped(".text", 0x401_000, 0, 0x1000, false, true)],
    );
    p.format = BinaryFormat::Pe;
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let text = decompile(&p, &a, &o, 0x401_040).unwrap_or_default();
    let header = checked_header(&p, &a, &o, 0x401_040).unwrap_or_default();
    assert!(!header.contains("disagree"), "{header}\n{text}");
    let lines: Vec<&str> = text.lines().map(str::trim).collect();
    let at = lines
        .iter()
        .rposition(|l| l.starts_with("return "))
        .unwrap_or(0);
    assert!(lines[at].starts_with("return *(uint64_t*)var1"), "{text}");
    assert!(
        at.checked_sub(1)
            .and_then(|i| lines.get(i))
            .is_some_and(|l| l.starts_with("rdx = ")),
        "{text}"
    );
}

/// A function handing a second result back in `rdx` does not make `rdx`
/// live at its returns.
///
/// The callee is the corpus binary's `read_number` closure for `u16`,
/// copied byte for byte at its own address so the check draws the same
/// states, and its caller reads `rdx` after the call. Its hexadecimal
/// loop is `L: movzx edx,byte [r11+rsi]; ...; cmp ebx,edi; jae E; mul di;
/// jo F; add ax,bx; jb F; inc rsi; cmp r9,rsi; jne L`: read at every
/// return, `rdx` was compared at the edge out of the `mul di` that writes
/// only `dx`, where the check of the text disagreed on the bits above it.
///
/// # Panics
///
/// When the check disagrees.
#[test]
fn a_second_result_keeps_no_register_live_at_the_returns() {
    use borer_engine::analysis::decompile::checked_header;
    use borer_engine::program::{Arch, BinaryFormat, Program, Section};
    let mut code = vec![
        0xe8, 0x3b, 0x00, 0x00, 0x00, // ASM: call 0x142199040
        0x48, 0x89, 0xd3, // ASM: mov rbx,rdx
        0x48, 0x89, 0xd8, // ASM: mov rax,rbx
        0xc3, // ASM: ret
    ];
    code.resize(0x40, 0xcc);
    code.extend_from_slice(&[
        0x55, 0x41, 0x57, 0x41, 0x56, 0x56, 0x57, 0x53, 0x48, 0x83, 0xec, 0x28, 0x48, 0x8d, 0x6c,
        0x24, 0x20, 0x49, 0x89, 0xd0, 0x4c, 0x8b, 0x4a, 0x08, 0x4d, 0x85, 0xc9, 0x0f, 0x84, 0xb3,
        0x00, 0x00, 0x00, 0x49, 0x8b, 0x00, 0x80, 0x38, 0x30, 0x41, 0x0f, 0x94, 0xc2, 0x80, 0x39,
        0x00, 0x0f, 0x84, 0xc9, 0x00, 0x00, 0x00, 0x4d, 0x8b, 0x18, 0x8b, 0x71, 0x10, 0x8d, 0x46,
        0xfe, 0x83, 0xf8, 0x22, 0x0f, 0x87, 0xfa, 0x01, 0x00, 0x00, 0x48, 0x8b, 0x79, 0x08, 0x31,
        0xc0, 0x31, 0xd2, 0x83, 0xfe, 0x0a, 0x76, 0x4d, 0x66, 0x66, 0x66, 0x66, 0x2e, 0x0f, 0x1f,
        0x84, 0x00, 0x00, 0x00, 0x00, 0x00, 0x45, 0x0f, 0xb6, 0x34, 0x03, 0x45, 0x8d, 0x7e, 0xbf,
        0x41, 0x83, 0xe7, 0xdf, 0x41, 0x83, 0xc7, 0x0a, 0x41, 0x8d, 0x5e, 0xd0, 0x41, 0x83, 0xfe,
        0x3a, 0x41, 0x0f, 0x43, 0xdf, 0x39, 0xf3, 0x0f, 0x83, 0x22, 0x01, 0x00, 0x00, 0x48, 0x39,
        0xf8, 0x0f, 0x83, 0x8f, 0x01, 0x00, 0x00, 0x48, 0xff, 0xc0, 0x0f, 0xaf, 0xd6, 0x01, 0xd3,
        0x89, 0xda, 0x49, 0x39, 0xc1, 0x75, 0xc3, 0xeb, 0x29, 0x90, 0x41, 0x0f, 0xb6, 0x1c, 0x03,
        0x83, 0xc3, 0xd0, 0x39, 0xf3, 0x0f, 0x83, 0xf7, 0x00, 0x00, 0x00, 0x48, 0x39, 0xf8, 0x0f,
        0x83, 0x64, 0x01, 0x00, 0x00, 0x48, 0xff, 0xc0, 0x0f, 0xaf, 0xd6, 0x01, 0xd3, 0x89, 0xda,
        0x49, 0x39, 0xc1, 0x75, 0xd8, 0x4d, 0x01, 0xcb, 0x31, 0xf6, 0x89, 0xda, 0xe9, 0xdf, 0x00,
        0x00, 0x00, 0x4d, 0x8b, 0x18, 0x45, 0x31, 0xd2, 0x80, 0x39, 0x00, 0xba, 0x00, 0x00, 0x00,
        0x00, 0x41, 0xb9, 0x00, 0x00, 0x00, 0x00, 0xbe, 0x00, 0x00, 0x00, 0x00, 0xb8, 0x00, 0x00,
        0x00, 0x00, 0x0f, 0x84, 0x91, 0x00, 0x00, 0x00, 0xe9, 0xb6, 0x00, 0x00, 0x00, 0x4d, 0x8b,
        0x18, 0x8b, 0x79, 0x10, 0x8d, 0x47, 0xfe, 0x83, 0xf8, 0x22, 0x0f, 0x87, 0x31, 0x01, 0x00,
        0x00, 0x31, 0xf6, 0x31, 0xc0, 0x83, 0xff, 0x0a, 0x76, 0x48, 0x0f, 0x1f, 0x84, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x41, 0x0f, 0xb6, 0x14, 0x33, 0x44, 0x8d, 0x72, 0xbf, 0x41, 0x83, 0xe6,
        0xdf, 0x41, 0x83, 0xc6, 0x0a, 0x8d, 0x5a, 0xd0, 0x83, 0xfa, 0x3a, 0x41, 0x0f, 0x43, 0xde,
        0x39, 0xfb, 0x0f, 0x83, 0x8d, 0x00, 0x00, 0x00, 0x66, 0xf7, 0xe7, 0x0f, 0x80, 0xbb, 0x00,
        0x00, 0x00, 0x66, 0x01, 0xd8, 0x0f, 0x82, 0xb2, 0x00, 0x00, 0x00, 0x48, 0xff, 0xc6, 0x49,
        0x39, 0xf1, 0x75, 0xc3, 0xeb, 0x27, 0x90, 0x41, 0x0f, 0xb6, 0x1c, 0x33, 0x83, 0xc3, 0xd0,
        0x39, 0xfb, 0x73, 0x64, 0x66, 0xf7, 0xe7, 0x0f, 0x80, 0x92, 0x00, 0x00, 0x00, 0x66, 0x01,
        0xd8, 0x0f, 0x82, 0x89, 0x00, 0x00, 0x00, 0x48, 0xff, 0xc6, 0x49, 0x39, 0xf1, 0x75, 0xda,
        0x4d, 0x01, 0xcb, 0x4d, 0x89, 0x18, 0x49, 0xc7, 0x40, 0x08, 0x00, 0x00, 0x00, 0x00, 0x66,
        0x41, 0xb8, 0x01, 0x00, 0x89, 0xc2, 0x31, 0xc0, 0x4d, 0x85, 0xc9, 0x75, 0x4c, 0xe9, 0x8c,
        0x00, 0x00, 0x00, 0x49, 0x01, 0xc3, 0x4c, 0x89, 0xce, 0x48, 0x29, 0xc6, 0x49, 0x89, 0xc1,
        0x4d, 0x89, 0x18, 0x49, 0x89, 0x70, 0x08, 0x45, 0x31, 0xc0, 0x81, 0xfa, 0x00, 0x00, 0x01,
        0x00, 0x41, 0x0f, 0x92, 0xc0, 0x31, 0xc0, 0x4d, 0x85, 0xc9, 0x75, 0x20, 0xeb, 0x63, 0x49,
        0x01, 0xf3, 0x49, 0x29, 0xf1, 0x4d, 0x89, 0x18, 0x4d, 0x89, 0x48, 0x08, 0x66, 0x41, 0xb8,
        0x01, 0x00, 0x89, 0xc2, 0x49, 0x89, 0xf1, 0x31, 0xc0, 0x4d, 0x85, 0xc9, 0x74, 0x45, 0x80,
        0x79, 0x14, 0x00, 0x41, 0x0f, 0x45, 0xc0, 0x45, 0x84, 0xd2, 0x41, 0x0f, 0x44, 0xc0, 0x49,
        0x83, 0xf9, 0x01, 0x41, 0x0f, 0x44, 0xc0, 0xeb, 0x2c, 0x49, 0x8d, 0x04, 0x33, 0x48, 0xff,
        0xc0, 0x48, 0xf7, 0xd6, 0x4c, 0x01, 0xce, 0x49, 0x89, 0x00, 0x49, 0x89, 0x70, 0x08, 0xeb,
        0x14, 0x49, 0x8d, 0x0c, 0x03, 0x48, 0xff, 0xc1, 0x48, 0xf7, 0xd0, 0x4c, 0x01, 0xc8, 0x49,
        0x89, 0x08, 0x49, 0x89, 0x40, 0x08, 0x31, 0xc0, 0x48, 0x83, 0xc4, 0x28, 0x5b, 0x5f, 0x5e,
        0x41, 0x5e, 0x41, 0x5f, 0x5d, 0xc3, 0x49, 0xff, 0xc3, 0x49, 0xff, 0xc9, 0x4d, 0x89, 0x18,
        0x4d, 0x89, 0x48, 0x08, 0x48, 0x8d, 0x0d, 0x65, 0x39, 0x2e, 0x00, 0x4c, 0x8d, 0x05, 0xa5,
        0x39, 0x2e, 0x00, 0xba, 0x8f, 0x00, 0x00, 0x00, 0xe8, 0xab, 0x9b, 0x03, 0x00,
    ]);
    let mut bytes = vec![0u8; 0x1000];
    bytes[..code.len()].copy_from_slice(&code);
    let mut p = Program::raw(
        bytes,
        Arch::X86_64,
        0x1_4000_0000,
        Some(0x1_4219_9000),
        vec![Section::mapped(
            ".text",
            0x1_4219_9000,
            0,
            0x1000,
            false,
            true,
        )],
    );
    p.format = BinaryFormat::Pe;
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let text = decompile(&p, &a, &o, 0x1_4219_9040).unwrap_or_default();
    let header = checked_header(&p, &a, &o, 0x1_4219_9040).unwrap_or_default();
    assert!(text.contains("// hands back rdx"), "{text}");
    assert!(!header.contains("disagree"), "{header}\n{text}");
}

/// A call to a callee that hands `rdx` back renders its second result as
/// its own assignment under the callee's name with a `__rdx` suffix.
///
/// The register the caller reads after the call is set by the text, and
/// the interpreter answers it from the call it is the second half of.
///
/// # Panics
///
/// When the second result is not rendered.
#[test]
fn a_second_result_renders_as_its_own_assignment() {
    use borer_engine::program::{Arch, BinaryFormat, Program, Section};
    let mut code = vec![
        0xe8, 0x1b, 0x00, 0x00, 0x00, // ASM: call 0x401020
        0x48, 0x89, 0xd3, // ASM: mov rbx,rdx
        0x48, 0x89, 0xd8, // ASM: mov rax,rbx
        0xc3, // ASM: ret
    ];
    code.resize(0x20, 0xcc);
    code.extend_from_slice(&[
        0xb8, 0x01, 0x00, 0x00, 0x00, // ASM: mov eax,1
        0xba, 0x02, 0x00, 0x00, 0x00, // ASM: mov edx,2
        0xc3, // ASM: ret
    ]);
    let mut bytes = vec![0u8; 0x1000];
    bytes[..code.len()].copy_from_slice(&code);
    let mut p = Program::raw(
        bytes,
        Arch::X86_64,
        0x400_000,
        Some(0x401_000),
        vec![Section::mapped(".text", 0x401_000, 0, 0x1000, false, true)],
    );
    p.format = BinaryFormat::Pe;
    let text = decompiled(&p, 0x401_000);
    assert!(
        text.contains("sub_401020__rdx"),
        "the second result: {text}"
    );
}

/// A second result's line reads the arguments the call was made with, not
/// the first result that replaced one of them.
///
/// `call 0x401040; mov rcx,rax; call 0x401020; add rax,rdx; ret`, where
/// 0x401020 (`lea rax,[rcx+1]; lea rdx,[rcx+2]; ret`) hands back `rdx`:
/// the text wrote `rax = sub_401020(rax); rdx = sub_401020__rdx(rax);`,
/// whose second line reads the `rax` the first just assigned, like a
/// second call on the first one's result.
///
/// # Panics
///
/// When the second result's line follows an assignment of its argument.
#[test]
fn a_second_result_reads_the_arguments_before_the_call() {
    use borer_engine::program::{Arch, BinaryFormat, Program, Section};
    let mut code = vec![
        0xe8, 0x3b, 0x00, 0x00, 0x00, // ASM: call 0x401040
        0x48, 0x89, 0xc1, // ASM: mov rcx,rax
        0xe8, 0x13, 0x00, 0x00, 0x00, // ASM: call 0x401020
        0x48, 0x01, 0xd0, // ASM: add rax,rdx
        0xc3, // ASM: ret
    ];
    code.resize(0x20, 0xcc);
    code.extend_from_slice(&[
        0x48, 0x8d, 0x41, 0x01, // ASM: lea rax,[rcx+1]
        0x48, 0x8d, 0x51, 0x02, // ASM: lea rdx,[rcx+2]
        0xc3, // ASM: ret
    ]);
    code.resize(0x40, 0xcc);
    code.extend_from_slice(&[
        0xb8, 0x07, 0x00, 0x00, 0x00, // ASM: mov eax,7
        0xc3, // ASM: ret
    ]);
    let mut bytes = vec![0u8; 0x1000];
    bytes[..code.len()].copy_from_slice(&code);
    let mut p = Program::raw(
        bytes,
        Arch::X86_64,
        0x400_000,
        Some(0x401_000),
        vec![Section::mapped(".text", 0x401_000, 0, 0x1000, false, true)],
    );
    p.format = BinaryFormat::Pe;
    let text = decompiled(&p, 0x401_000);
    let lines: Vec<&str> = text.lines().map(str::trim).collect();
    let at = lines
        .iter()
        .position(|l| *l == "var3 = sub_401020__rdx(var1);")
        .expect("the second result reads the argument");
    let before = at.checked_sub(1).and_then(|i| lines.get(i)).copied();
    assert!(
        before.is_some_and(|l| l.starts_with("var2 = ") && l.ends_with("= sub_401020(var1);")),
        "{text}"
    );
}

/// An argument register an earlier call left unknown does not drop the
/// arguments set behind it.
///
/// `call SPLIT; mov rcx,rax; mov r8,-1; call THREE; ret`, where `SPLIT`
/// returns only in `rax` and `THREE` reads `rcx`, `rdx` and `r8`: `rdx` is
/// the first call's unknown second result, and the text names the register
/// rather than closing the list at it, so `r8`'s `-1` survives as the third
/// argument.
#[test]
fn an_unknown_second_result_does_not_drop_the_set_arguments_behind_it() {
    use borer_engine::program::{Arch, BinaryFormat, Program, Section};
    let mut code = vec![
        0xe8, 0x1b, 0x00, 0x00, 0x00, // ASM: call 0x401020
        0x48, 0x89, 0xc1, // ASM: mov rcx,rax
        0x49, 0xc7, 0xc0, 0xff, 0xff, 0xff, 0xff, // ASM: mov r8,-1
        0xe8, 0x1c, 0x00, 0x00, 0x00, // ASM: call 0x401030
        0xc3, // ASM: ret
    ];
    code.resize(0x20, 0xcc);
    code.extend_from_slice(&[
        0xb8, 0x05, 0x00, 0x00, 0x00, // ASM: mov eax,5
        0xc3, // ASM: ret
    ]);
    code.resize(0x30, 0xcc);
    code.extend_from_slice(&[
        0x4c, 0x89, 0xc0, // ASM: mov rax,r8
        0x48, 0x01, 0xd0, // ASM: add rax,rdx
        0x48, 0x01, 0xc8, // ASM: add rax,rcx
        0xc3, // ASM: ret
    ]);
    let mut bytes = vec![0u8; 0x1000];
    bytes[..code.len()].copy_from_slice(&code);
    let mut p = Program::raw(
        bytes,
        Arch::X86_64,
        0x400_000,
        Some(0x401_000),
        vec![Section::mapped(".text", 0x401_000, 0, 0x1000, false, true)],
    );
    p.format = BinaryFormat::Pe;
    let text = decompiled(&p, 0x401_000);
    assert!(text.contains("sub_401030(sub_401020(), rdx, -1)"), "{text}");
}

/// The frame idiom `mov rax, rsp` is no result: a function whose one
/// path to `ret` writes rax nowhere else returns nothing.
///
/// `mov rax,rsp; mov [rax+8],rbx; sub rsp,0x28; test ecx,ecx; je L; call
/// 0x140001040; L: add rsp,0x28; mov rbx,[rsp+8]; ret`; the callee `mov
/// eax,1; ret`.
#[test]
fn the_frame_idiom_returns_nothing() {
    let mut code = vec![
        0x48, 0x8b, 0xc4, 0x48, 0x89, 0x58, 0x08, 0x48, 0x83, 0xec, 0x28, 0x85, 0xc9, 0x74, 0x05,
        0xe8, 0x2c, 0x00, 0x00, 0x00, 0x48, 0x83, 0xc4, 0x28, 0x48, 0x8b, 0x5c, 0x24, 0x08, 0xc3,
    ];
    code.resize(0x40, 0xcc);
    code.extend_from_slice(&[0xb8, 0x01, 0x00, 0x00, 0x00, 0xc3]);
    let p = program64(&code);
    let a = Analysis::compute(&p);
    let f = a.function(0x1_4000_1000).map(|f| f.returns_value);
    assert_eq!(f, Some(Some(false)));
    let text = decompile(&p, &a, &Overlay::default(), 0x1_4000_1000).unwrap_or_default();
    assert!(!text.contains("retaddr"), "{text}");
    assert!(text.contains("// signature: void "), "{text}");
}

/// A `push rax` at the entry reserves a word, as clang's `/Od` frames do,
/// and stores nothing: `push rax; mov [rsp],ecx; mov eax,[rsp]; pop rcx;
/// ret` reads no `rax` the caller left.
#[test]
fn a_push_of_rax_at_the_entry_only_makes_room() {
    let code = [
        0x50, // ASM: push rax
        0x89, 0x0c, 0x24, // ASM: mov [rsp],ecx
        0x8b, 0x04, 0x24, // ASM: mov eax,[rsp]
        0x59, // ASM: pop rcx
        0xc3, // ASM: ret
    ];
    let p = program64(&code);
    let a = Analysis::compute(&p);
    let text = decompile(&p, &a, &Overlay::default(), 0x1_4000_1000).unwrap_or_default();
    assert!(!text.contains("rax"), "{text}");
}

/// A call through the result reads it: after `call 0x140001040; call
/// [rax+0x10]; ret` the callee `mov eax,1; ret` returns a value.
#[test]
fn a_call_through_the_result_reads_it() {
    let mut code = vec![0xe8, 0x3b, 0x00, 0x00, 0x00, 0xff, 0x50, 0x10, 0xc3];
    code.resize(0x40, 0xcc);
    code.extend_from_slice(&[0xb8, 0x01, 0x00, 0x00, 0x00, 0xc3]);
    let p = program64(&code);
    let a = Analysis::compute(&p);
    let f = a.function(0x1_4000_1040).map(|f| f.returns_value);
    assert_eq!(f, Some(Some(true)));
}

/// Handing back what a callee returning nothing left returns nothing.
///
/// `jmp 0x140001060` over `test ecx,ecx; je L; mov eax,1; mov [rdx],eax;
/// L: ret`, which reaches its `ret` without writing rax, is `void` and
/// drops the `return` of the tail call, whatever its callers do: its one
/// caller, `call 0x140001060; call 0x140001040; ret`, hands its rax on to
/// callers unknown.
#[test]
fn passing_on_a_callee_that_returns_nothing_returns_nothing() {
    let mut code = vec![
        0xe8, 0x5b, 0x00, 0x00, 0x00, 0xe8, 0x36, 0x00, 0x00, 0x00, 0xc3,
    ];
    code.resize(0x40, 0xcc);
    code.extend_from_slice(&[0xe9, 0x1b, 0x00, 0x00, 0x00]);
    code.resize(0x60, 0xcc);
    code.extend_from_slice(&[
        0x85, 0xc9, 0x74, 0x07, 0xb8, 0x01, 0x00, 0x00, 0x00, 0x89, 0x02, 0xc3,
    ]);
    let p = program64(&code);
    let a = Analysis::compute(&p);
    let f = a.function(0x1_4000_1040).map(|f| f.returns_value);
    assert_eq!(f, Some(Some(false)));
    let text = decompile(&p, &a, &Overlay::default(), 0x1_4000_1040).unwrap_or_default();
    assert!(text.contains("// signature: void "), "{text}");
    assert!(!text.contains("return sub_"), "{text}");
}

/// Two paths each ending in a call through a table, joining at the
/// epilogue of a function nobody calls: the function returns nothing,
/// and neither call's result is assigned to the return register.
///
/// `sub rsp,0x28; mov r10,[rcx]; test edx,edx; je L; call [r10+8]; jmp
/// M; L: call [r10+0x10]; M: add rsp,0x28; ret`.
#[test]
fn a_dead_result_before_a_bare_return_is_dropped() {
    let code = [
        0x48, 0x83, 0xec, 0x28, 0x4c, 0x8b, 0x11, 0x85, 0xd2, 0x74, 0x06, 0x41, 0xff, 0x52, 0x08,
        0xeb, 0x04, 0x41, 0xff, 0x52, 0x10, 0x48, 0x83, 0xc4, 0x28, 0xc3,
    ];
    let p = program64(&code);
    let text = decompiled(&p, 0x1_4000_1000);
    assert!(text.contains("return;"), "{text}");
    assert!(!text.contains("rax"), "{text}");
}

/// A register several calls write and no line reads holds results nobody
/// reads: each call stands as a statement of its own.
///
/// Once a condition takes in the call it tests, the calls before and after
/// it may assign `x0` with nothing left to read it; the assignments in two
/// arms are not in line with one another, so only the absence of any read
/// tells them dead.
#[test]
fn results_no_line_reads_are_dropped() {
    let body = "if (a1 != 0) {\n  x0 = sub_1(a1);\n} else {\n  x0 = sub_2(a1);\n}\nif ((uint32_t)sub_3(a1) != 0) {\n  return 1;\n}\nreturn 0;\n";
    let out = cleanup(body);
    assert!(!out.contains("x0"), "{out}");
    assert!(
        out.contains("sub_1(a1);") && out.contains("sub_2(a1);"),
        "{out}"
    );
    let read = body.replace("return 0;", "return x0;");
    assert!(
        cleanup(&read).contains("x0 = sub_1(a1);"),
        "{}",
        cleanup(&read)
    );
}

/// A frame pointer set from `rax` after `mov rax, rsp` places a read
/// through it against the entry stack pointer: the byte at `[rbp+0x40]`
/// is the first stack argument.
///
/// `mov rax,rsp; mov [rax+8],rbx; push rbp; lea rbp,[rax-0x18]; sub
/// rsp,0x20; movzx eax,byte [rbp+0x40]; add rsp,0x20; pop rbp; mov
/// rbx,[rsp+8]; ret`.
#[test]
fn a_frame_pointer_set_from_the_rax_alias_places_stack_arguments() {
    let code = [
        0x48, 0x8b, 0xc4, 0x48, 0x89, 0x58, 0x08, 0x55, 0x48, 0x8d, 0x68, 0xe8, 0x48, 0x83, 0xec,
        0x20, 0x0f, 0xb6, 0x45, 0x40, 0x48, 0x83, 0xc4, 0x20, 0x5d, 0x48, 0x8b, 0x5c, 0x24, 0x08,
        0xc3,
    ];
    let p = program64(&code);
    let a = Analysis::compute(&p);
    let stack_args = a.function(0x1_4000_1000).map(|f| f.stack_args);
    assert_eq!(stack_args, Some(1));
}

/// `mov eax,1; ret`: the constant flows straight into the return and no dead
/// `rax = 1;` line survives.
#[test]
fn leaf_function_constant_return() {
    let out = dc(0x1020);
    assert!(out.contains("return 1;"), "no folded return:\n{out}");
    assert!(
        !out.contains("rax = 1;"),
        "dead register copy survived:\n{out}"
    );
}

/// A value-returning leaf gets the width it writes, `uint32_t` for its
/// `mov eax, 1`; a bare `ret` gets `void`.
#[test]
fn value_returning_signature() {
    let out = dc(0x1020);
    assert!(
        out.contains("// signature: uint32_t sub_1020()"),
        "leaf signature wrong:
{out}"
    );
    let bare = dc(0x10e0);
    assert!(
        bare.contains("// signature: void sub_10e0()"),
        "void signature wrong:
{bare}"
    );
}

/// `VD2`: its only caller overwrites `rax` right after the call, so the stale
/// `rax` left by `AR` is not a return value and the function is `void`.
#[test]
fn stale_return_register_no_caller_reads_is_void() {
    let out = dc(0x1600);
    assert!(out.contains("// signature: void exported_vd2("), "{out}");
    assert!(!out.contains("return rax"), "{out}");
}

/// A call whose `ret` follows returns the callee's result when the callee
/// is known to produce one.
///
/// `RC` renders `return Foo::Bar();` under a `uint64_t` header, not
/// `rax = Foo::Bar(); return;`.
#[test]
fn a_call_before_ret_returns_its_result() {
    let text = dc(0x1800);
    assert!(text.contains("return Foo::Bar();"), "{text}");
    assert!(text.contains("// signature: uint64_t sub_1800()"), "{text}");
    assert!(!text.contains("rax ="), "{text}");
}

/// A result every caller tests as a byte reads without a mask.
///
/// `CW` calls `BL`, whose only caller reads `al`, so `BL` returns a byte and
/// `test al, al` renders as `rax == 0` rather than `(rax & 0xff) == 0`.
#[test]
fn byte_wide_call_results_read_without_a_mask() {
    let out = dc(0x1f40);
    assert!(!out.contains("& 0xff"), "{out}");
    assert!(
        out.contains("sub_1f30() == 0") || out.contains("sub_1f30() != 0"),
        "{out}"
    );
}

/// A copy of a byte-wide result keeps its width, so a byte test of the
/// copy needs no mask either.
///
/// `CB2` copies the result of `BB`, which ends `sete al`, into `ecx` and
/// tests `cl`: the copy carries the byte width and the test renders with
/// no `& 0xff`.
#[test]
fn copies_of_byte_wide_results_read_without_a_mask() {
    let out = dc(0x1f70);
    assert!(!out.contains("& 0xff"), "{out}");
}

/// A result whose every last write fits a byte reads without a mask.
///
/// `CZ` copies the result of `BZ`, a zero-extended byte load, into `edx`
/// and tests `dl`: the value fits a byte, so the test renders with no
/// `& 0xff`.
#[test]
fn results_that_fit_a_byte_read_without_a_mask() {
    let out = dc(0x1fa0);
    assert!(!out.contains("& 0xff"), "{out}");
}

/// A result whose only wide return is a null pointer reads without a mask.
///
/// `CN` copies the result of `BN`, which returns either a zero-extended
/// byte or the null pointer it checked, into `edx` and tests `dl`: every
/// value fits a byte, so the test renders with no `& 0xff`.
#[test]
fn results_wide_only_when_null_read_without_a_mask() {
    let out = dc(0x1fd0);
    assert!(!out.contains("& 0xff"), "{out}");
}

/// A call that preserves `rax` is not the result: the value set before it
/// is what the function returns.
///
/// `CC` sets `eax` to 7 and calls the cookie-check-shaped `CK` before
/// returning, so it returns 7 and the check is a statement.
#[test]
fn calls_preserving_rax_do_not_replace_the_result() {
    let out = dc(0x4050);
    assert!(out.contains("return 7;"), "{out}");
    assert!(out.contains("sub_4041("), "{out}");
    assert!(!out.contains("= sub_4041("), "{out}");
}

/// A declared return type keeps the result even when no caller reads it.
///
/// `IG`, `IG2` and `IG3` call `Cls::Has`, `Ns::Flag` and `Ns::Flag2` and
/// overwrite `eax` at once, so no caller reads the results; the signatures
/// say `bool`, so the field read and the bytes kept in `rbx` across a call
/// are still returned, `Ns::Flag2`'s set on two paths.
#[test]
fn declared_return_types_keep_their_result() {
    let p = fixture();
    let a = Analysis::compute(&p);
    assert_ne!(a.function(0x1660).and_then(|f| f.returns_value), Some(true));
    let out = dc(0x1660);
    assert!(
        out.contains("return *(uint32_t*)((uintptr_t)this + 8)"),
        "{out}"
    );
    assert_ne!(a.function(0x4100).and_then(|f| f.returns_value), Some(true));
    let flag = dc(0x4100);
    assert!(flag.contains("// signature: bool Ns::Flag("), "{flag}");
    assert!(!flag.contains("return;"), "{flag}");
    assert!(flag.contains("return "), "{flag}");
    assert_ne!(a.function(0x4130).and_then(|f| f.returns_value), Some(true));
    let flag2 = dc(0x4130);
    assert!(flag2.contains("// signature: bool Ns::Flag2("), "{flag2}");
    assert!(!flag2.contains("return;"), "{flag2}");
    assert!(flag2.contains("return var1"), "{flag2}");
}

/// A value the body computes is returned though no caller reads it.
///
/// `NR`'s only caller drops its result, but every exit of `NR` returns the
/// product it computed itself: an unread result is still a result, so the
/// header keeps it rather than call the function `void`.
#[test]
fn a_computed_result_no_caller_reads_is_kept() {
    let out = dc(0x4da0);
    assert!(!out.contains("// signature: void "), "{out}");
    assert!(!out.contains("return;"), "{out}");
    assert!(out.contains("return 5 * a1;"), "{out}");
}

/// Dropping a returned value keeps the call that produced it.
///
/// `TR` tail-calls `TG` and its only caller ignores what comes back, so the
/// value is not worth printing. The call is: rewriting `return f(x);` as
/// `return;` took the call with it.
#[test]
fn a_dropped_return_value_keeps_its_call() {
    let out = dc(0x5550);
    assert!(out.contains("sub_5560("), "the tail call is gone: {out}");
}

/// A call result read two instructions later is still the call's result:
/// `UR` passes `P()` to `Q` though `mov edx, 5` comes between.
#[test]
fn call_results_read_later_are_assigned() {
    let p = fixture();
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let text = decompile(&p, &a, &o, 0x17d0).unwrap_or_default();
    let callee = borer_engine::analysis::name_of(&a, &o, 0x1200);
    assert!(text.contains(&format!("({callee}(), 5)")), "{text}");
}

/// A function whose every exit writes a 32-bit register returns that wide.
///
/// On a 64-bit target `mov eax, 0xc000000d` leaves `0x00000000c000000d`
/// in `rax`, where a `uint64_t` header turns the text's `return
/// STATUS_INVALID_PARAMETER;` (or `return ~rcx;` of a value kept whole)
/// into `0xffffffffc000000d`. `test ecx,ecx; je L; mov eax,0xc000000d;
/// ret; L: not ecx; mov eax,ecx; ret` returns a `uint32_t`; an exit that
/// writes all of `rax` (`mov rax,[rcx]`) or hands over to another function
/// whose width is unknown (`jmp sub`) keeps the whole register, and a byte
/// returned beside a handover to a function returning a byte stays a byte.
#[test]
fn a_result_every_exit_writes_as_32_bits_is_32_bits_wide() {
    let narrow = [
        0x85, 0xc9, 0x74, 0x06, 0xb8, 0x0d, 0x00, 0x00, 0xc0, 0xc3, 0xf7, 0xd1, 0x89, 0xc8, 0xc3,
    ];
    let text = decompiled(&program64(&narrow), 0x1_4000_1000);
    assert!(
        text.contains("// signature: uint32_t sub_140001000("),
        "{text}"
    );
    let mixed = [
        0x48, 0x85, 0xc9, 0x74, 0x04, 0x48, 0x8b, 0x01, 0xc3, 0x31, 0xc0, 0xc3,
    ];
    let text = decompiled(&program64(&mixed), 0x1_4000_1000);
    assert!(
        text.contains("// signature: uint64_t sub_140001000("),
        "{text}"
    );
    let mut tail = vec![
        0x85, 0xc9, 0x75, 0x0b, 0xe8, 0x37, 0x00, 0x00, 0x00, 0xb8, 0x57, 0x00, 0x00, 0x00, 0xc3,
        0xe9, 0x2c, 0x00, 0x00, 0x00,
    ];
    tail.resize(0x40, 0xcc);
    tail.extend_from_slice(&[0x48, 0x8b, 0x01, 0xc3]);
    let text = decompiled(&program64(&tail), 0x1_4000_1000);
    assert!(
        text.contains("// signature: uint64_t sub_140001000("),
        "{text}"
    );
    let mut byte = vec![
        0x85, 0xc9, 0x75, 0x08, 0xe8, 0x37, 0x00, 0x00, 0x00, 0x30, 0xc0, 0xc3, 0xe9, 0x2f, 0x00,
        0x00, 0x00,
    ];
    byte.resize(0x40, 0xcc);
    byte.extend_from_slice(&[0xb0, 0x01, 0xc3]);
    let text = decompiled(&program64(&byte), 0x1_4000_1000);
    assert!(
        text.contains("// signature: uint8_t sub_140001000("),
        "{text}"
    );
}

/// A `_setjmp` call returns a result: the comparison against zero is a
/// plain condition, and nothing treats the call as noreturn.
///
/// `lea rcx,[buf]; call [_setjmp]; test eax,eax; jne L` binds the result
/// and branches on it, the shape both returns of a `setjmp` land in: the
/// first return reads zero and falls through, the second reads what
/// `longjmp` was handed. The minimal model keeps that honest as an
/// ordinary conditional with both arms live, and the prototype's one
/// argument keeps the call from padding to the register slots.
#[test]
fn a_setjmp_call_still_returns_a_result() {
    let code = [
        0x48, 0x8d, 0x0d, 0x11, 0x10, 0x00, 0x00, // ASM: lea rcx,[0x14002018]
        0xff, 0x15, 0xfb, 0x0f, 0x00, 0x00, // ASM: call [0x14002008]
        0x85, 0xc0, // ASM: test eax,eax
        0x75, 0x06, // ASM: jne 0x140001017
        0xb8, 0x64, 0x00, 0x00, 0x00, // ASM: mov eax,100
        0xc3, // ASM: ret
        0xb8, 0xc8, 0x00, 0x00, 0x00, // ASM: mov eax,200
        0xc3, // ASM: ret
    ];
    let p = program64_with_imports(
        &code,
        &[0; 0x20],
        &[(0x1_4000_2008, "api-ms-win-crt-runtime-l1-1-0.dll!_setjmp")],
    );
    let text = decompiled(&p, 0x1_4000_1000);
    assert!(text.contains("if (_setjmp(0x140002018) != 0) {"), "{text}");
    assert!(text.contains("return 100;"), "{text}");
    assert!(text.contains("return 200;"), "{text}");
}
