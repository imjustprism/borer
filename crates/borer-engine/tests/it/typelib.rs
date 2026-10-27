//! The typed API library at call sites.
//!
//! Constants are named by the parameter they are passed for, results bound
//! only where the declaration hands one back, and the check against the
//! binary kept honest where the code reads a result the declaration rules
//! out.

#![expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]

use borer_engine::analysis::decompile::{checked_header, decompile};
use borer_engine::analysis::{Analysis, Overlay};
use borer_engine::program::{Arch, BinaryFormat, Program, Section, Symbol, SymbolKind};

/// Image base of the hand-built images.
const BASE: u64 = 0x1_4000_0000;
/// Where `.text` starts, and the function under test with it.
const TEXT: u64 = BASE + 0x1000;
/// Where `.rdata` starts: the import slots, then a string.
const RDATA: u64 = BASE + 0x2000;

/// Builds a 64-bit image of `format` with `code` at [`TEXT`], `data` at
/// [`RDATA`] and an import named by each of `imports` in consecutive
/// 8-byte slots from [`RDATA`].
///
/// # Arguments
///
/// * `format` - The container the image claims to be, which picks the
///   calling convention and the library's platform.
/// * `code` - The bytes of `.text`.
/// * `data` - The bytes of `.rdata`, slots included.
/// * `imports` - The import symbols' names, one per slot.
fn image(format: BinaryFormat, code: &[u8], data: &[u8], imports: &[&str]) -> Program {
    let mut bytes = vec![0u8; 0x2000];
    bytes[..code.len()].copy_from_slice(code);
    bytes[0x1000..0x1000 + data.len()].copy_from_slice(data);
    let mut p = Program::raw(
        bytes,
        Arch::X86_64,
        BASE,
        Some(TEXT),
        vec![
            Section::mapped(".text", TEXT, 0, 0x1000, false, true),
            Section::mapped(".rdata", RDATA, 0x1000, 0x1000, false, false),
        ],
    );
    p.format = format;
    p.symbols = imports
        .iter()
        .zip((RDATA..).step_by(8))
        .map(|(name, addr)| Symbol {
            name: (*name).to_owned(),
            addr,
            kind: SymbolKind::Import,
        })
        .collect();
    p
}

/// Encodes `call [rip+disp]` at `at` reaching the slot at `slot`.
///
/// # Arguments
///
/// * `at` - The call's address.
/// * `slot` - The import slot's address.
fn call_slot(at: u64, slot: u64) -> [u8; 6] {
    let disp = i32::try_from(slot.cast_signed() - (at + 6).cast_signed()).unwrap_or_default();
    let d = disp.to_le_bytes();
    // ASM: call qword [rip+disp]
    [0xff, 0x15, d[0], d[1], d[2], d[3]]
}

/// The text and the checked header of the function at [`TEXT`].
///
/// # Arguments
///
/// * `p` - The image.
fn decompiled(p: &Program) -> (String, String) {
    let a = Analysis::compute(p);
    let o = Overlay::default();
    (
        decompile(p, &a, &o, TEXT).unwrap_or_default(),
        checked_header(p, &a, &o, TEXT).unwrap_or_default(),
    )
}

/// A `CreateFileW` call passes its access, share mode, disposition and
/// flags by name, its null pointers as `NULL`, and the variable that holds
/// only its result, handed to `CloseHandle`, is a `HANDLE`.
#[test]
fn create_file_renders_its_constants_and_its_handle() {
    let mut code = vec![
        0x48, 0x83, 0xec, 0x48, // ASM: sub rsp, 0x48
        0x48, 0x8d, 0x0d, 0x00, 0x00, 0x00, 0x00, // ASM: lea rcx, [rip+wide] (patched)
        0xba, 0x00, 0x00, 0x00, 0x80, // ASM: mov edx, 0x80000000
        0x41, 0xb8, 0x01, 0x00, 0x00, 0x00, // ASM: mov r8d, 1
        0x45, 0x31, 0xc9, // ASM: xor r9d, r9d
        0xc7, 0x44, 0x24, 0x20, 0x03, 0x00, 0x00, 0x00, // ASM: mov dword [rsp+0x20], 3
        0xc7, 0x44, 0x24, 0x28, 0x80, 0x00, 0x00, 0x00, // ASM: mov dword [rsp+0x28], 0x80
        0x48, 0xc7, 0x44, 0x24, 0x30, 0x00, 0x00, 0x00, 0x00, // ASM: mov qword [rsp+0x30], 0
    ];
    let wide = RDATA + 0x40;
    let lea_end = TEXT + 11;
    let disp = i32::try_from(wide - lea_end).expect("near").to_le_bytes();
    code[7..11].copy_from_slice(&disp);
    let at = TEXT + u64::try_from(code.len()).expect("small");
    code.extend_from_slice(&call_slot(at, RDATA));
    code.extend_from_slice(&[0x48, 0x89, 0xc1]); // ASM: mov rcx, rax
    let at = TEXT + u64::try_from(code.len()).expect("small");
    code.extend_from_slice(&call_slot(at, RDATA + 8));
    code.extend_from_slice(&[
        0x48, 0x83, 0xc4, 0x48, // ASM: add rsp, 0x48
        0xc3, // ASM: ret
    ]);
    let mut data = vec![0u8; 0x40];
    for c in "out.txt".bytes() {
        data.extend_from_slice(&[c, 0]);
    }
    data.extend_from_slice(&[0, 0]);
    let p = image(
        BinaryFormat::Pe,
        &code,
        &data,
        &["KERNEL32.dll!CreateFileW", "KERNEL32.dll!CloseHandle"],
    );
    let (text, header) = decompiled(&p);
    assert!(
        text.contains(
            "CreateFileW(L\"out.txt\", GENERIC_READ, FILE_SHARE_READ, NULL, OPEN_EXISTING, FILE_ATTRIBUTE_NORMAL, NULL)"
        ),
        "{text}"
    );
    assert!(text.contains("HANDLE hObject;"), "{text}");
    assert!(header.contains("3/3 blocks"), "{header}");
    assert!(!header.contains("contradicted"), "{header}");
}

/// A `void` import binds no result.
///
/// Where the code after it reads `xmm0`, which a call leaves undefined, the
/// text writes no `xmm0 = SetLastError(..)` and the block says its call's
/// declaration is contradicted instead of counting as checked; where
/// nothing reads a result, the block is checked.
#[test]
fn a_void_import_binds_no_result() {
    let build = |reads_xmm0: bool| {
        let mut code = vec![
            0x48, 0x83, 0xec, 0x28, // ASM: sub rsp, 0x28
            0x31, 0xc9, // ASM: xor ecx, ecx
        ];
        let at = TEXT + u64::try_from(code.len()).expect("small");
        code.extend_from_slice(&call_slot(at, RDATA));
        if reads_xmm0 {
            code.extend_from_slice(&[0x66, 0x48, 0x0f, 0x7e, 0xc0]); // ASM: movq rax, xmm0
        } else {
            code.extend_from_slice(&[0x31, 0xc0]); // ASM: xor eax, eax
        }
        code.extend_from_slice(&[
            0x48, 0x83, 0xc4, 0x28, // ASM: add rsp, 0x28
            0xc3, // ASM: ret
        ]);
        image(
            BinaryFormat::Pe,
            &code,
            &[0u8; 8],
            &["KERNEL32.dll!SetLastError"],
        )
    };
    let (text, header) = decompiled(&build(true));
    assert!(text.contains("SetLastError(0);"), "{text}");
    assert!(!text.contains("xmm0 = SetLastError"), "{text}");
    assert!(header.contains("declaration contradicted"), "{header}");
    let (text, header) = decompiled(&build(false));
    assert!(text.contains("SetLastError(0);"), "{text}");
    assert!(header.contains("2/2 blocks"), "{header}");
}

/// An ELF's `mmap` takes its arity from the library, which the SDK table
/// does not know, and names its protection and flags; bits no member
/// covers stay in hex.
#[test]
fn mmap_names_its_protection_and_keeps_unknown_bits() {
    let build = |prot: u32| {
        let p = prot.to_le_bytes();
        let mut code = vec![
            0x48, 0x83, 0xec, 0x08, // ASM: sub rsp, 8
            0x31, 0xff, // ASM: xor edi, edi
            0xbe, 0x00, 0x10, 0x00, 0x00, // ASM: mov esi, 0x1000
            0xba, p[0], p[1], p[2], p[3], // ASM: mov edx, prot
            0xb9, 0x22, 0x00, 0x00, 0x00, // ASM: mov ecx, 0x22
            0x41, 0xb8, 0xff, 0xff, 0xff, 0xff, // ASM: mov r8d, -1
            0x45, 0x31, 0xc9, // ASM: xor r9d, r9d
        ];
        let at = TEXT + u64::try_from(code.len()).expect("small");
        code.extend_from_slice(&call_slot(at, RDATA));
        code.extend_from_slice(&[
            0x48, 0x83, 0xc4, 0x08, // ASM: add rsp, 8
            0xc3, // ASM: ret
        ]);
        image(BinaryFormat::Elf, &code, &[0u8; 8], &["mmap"])
    };
    let (text, _) = decompiled(&build(3));
    assert!(
        text.contains("mmap(NULL, 0x1000, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, "),
        "{text}"
    );
    let (text, _) = decompiled(&build(0x10_0003));
    assert!(
        text.contains("PROT_READ | PROT_WRITE | 0x100000, MAP_PRIVATE | MAP_ANONYMOUS"),
        "{text}"
    );
}

/// A comparison with a library call's result names the constant by the
/// group its declaration gives the result: `CreateFileW`'s `-1` is
/// `INVALID_HANDLE_VALUE`.
#[test]
fn a_compared_result_names_its_constant() {
    let mut code = vec![
        0x48, 0x83, 0xec, 0x48, // ASM: sub rsp, 0x48
        0x31, 0xc9, // ASM: xor ecx, ecx
        0xba, 0x00, 0x00, 0x00, 0x80, // ASM: mov edx, 0x80000000
        0x45, 0x31, 0xc0, // ASM: xor r8d, r8d
        0x45, 0x31, 0xc9, // ASM: xor r9d, r9d
        0xc7, 0x44, 0x24, 0x20, 0x03, 0x00, 0x00, 0x00, // ASM: mov dword [rsp+0x20], 3
        0xc7, 0x44, 0x24, 0x28, 0x00, 0x00, 0x00, 0x00, // ASM: mov dword [rsp+0x28], 0
        0x48, 0xc7, 0x44, 0x24, 0x30, 0x00, 0x00, 0x00, 0x00, // ASM: mov qword [rsp+0x30], 0
    ];
    let at = TEXT + u64::try_from(code.len()).expect("small");
    code.extend_from_slice(&call_slot(at, RDATA));
    code.extend_from_slice(&[
        0x48, 0x83, 0xf8, 0xff, // ASM: cmp rax, -1
        0x0f, 0x94, 0xc0, // ASM: sete al
        0x0f, 0xb6, 0xc0, // ASM: movzx eax, al
        0x48, 0x83, 0xc4, 0x48, // ASM: add rsp, 0x48
        0xc3, // ASM: ret
    ]);
    let p = image(
        BinaryFormat::Pe,
        &code,
        &[0u8; 8],
        &["KERNEL32.dll!CreateFileW"],
    );
    let (text, _) = decompiled(&p);
    assert!(text.contains("== INVALID_HANDLE_VALUE"), "{text}");
}

/// The same image decompiles to the same bytes twice.
#[test]
fn library_rendering_is_deterministic() {
    let mut code = vec![
        0x48, 0x83, 0xec, 0x08, // ASM: sub rsp, 8
        0xbf, 0x02, 0x00, 0x00, 0x00, // ASM: mov edi, 2
        0xbe, 0x01, 0x00, 0x00, 0x00, // ASM: mov esi, 1
        0x31, 0xd2, // ASM: xor edx, edx
    ];
    let at = TEXT + u64::try_from(code.len()).expect("small");
    code.extend_from_slice(&call_slot(at, RDATA));
    code.extend_from_slice(&[
        0x48, 0x83, 0xc4, 0x08, // ASM: add rsp, 8
        0xc3, // ASM: ret
    ]);
    let p = image(BinaryFormat::Elf, &code, &[0u8; 8], &["socket"]);
    let (first, _) = decompiled(&p);
    let (second, _) = decompiled(&p);
    assert_eq!(first, second);
    assert!(
        first.contains("socket(AF_INET, SOCK_STREAM, IPPROTO_IP)"),
        "{first}"
    );
}

/// A token query names the class of information it asks for, its null
/// buffers as `NULL`: a row the library gained for an import the system
/// tools call.
#[test]
fn a_token_query_names_its_information_class() {
    let mut code = vec![
        0x48, 0x83, 0xec, 0x38, // ASM: sub rsp, 0x38
        0xba, 0x01, 0x00, 0x00, 0x00, // ASM: mov edx, 1
        0x45, 0x31, 0xc0, // ASM: xor r8d, r8d
        0x45, 0x31, 0xc9, // ASM: xor r9d, r9d
        0x48, 0xc7, 0x44, 0x24, 0x20, 0x00, 0x00, 0x00, 0x00, // ASM: mov qword [rsp+0x20], 0
    ];
    let at = TEXT + u64::try_from(code.len()).expect("small");
    code.extend_from_slice(&call_slot(at, RDATA));
    code.extend_from_slice(&[
        0x48, 0x83, 0xc4, 0x38, // ASM: add rsp, 0x38
        0xc3, // ASM: ret
    ]);
    let p = image(
        BinaryFormat::Pe,
        &code,
        &[0u8; 8],
        &["ADVAPI32.dll!GetTokenInformation"],
    );
    let (text, header) = decompiled(&p);
    assert!(
        text.contains("GetTokenInformation(a1, TokenUser, NULL, 0, NULL)"),
        "{text}"
    );
    assert!(!header.contains("contradicted"), "{header}");
}

/// A function the binary defines under a library name takes the library's
/// prototype, its parameter and result typed where the code shows only
/// their widths.
#[test]
fn a_function_named_for_the_library_takes_its_prototype() {
    let code = [
        0x8b, 0x01, // ASM: mov eax, [rcx]
        0xc3, // ASM: ret
    ];
    let mut p = image(BinaryFormat::Pe, &code, &[0u8; 8], &[]);
    p.symbols.push(Symbol {
        name: "lstrlenW".to_owned(),
        addr: TEXT,
        kind: SymbolKind::Export,
    });
    let (text, _) = decompiled(&p);
    assert!(
        text.contains("// signature: int lstrlenW(LPCWSTR a1)"),
        "{text}"
    );
}

/// A parameter passed whole as a declared API's `int` is an `int`, and one
/// passed as its `const char *` is a `char *`, whatever byte store the
/// body also makes through it.
///
/// `exit(a1)` reads only `edi`, so the `uint64_t` that said only how wide a
/// register is was an `int32_t`; `strlen(a1)` followed by a store of the
/// byte before the terminator makes `a1` a string. Both run against the
/// binary the same way.
#[test]
fn declared_parameters_type_the_arguments_passed_to_them() {
    let mut code = vec![0x48, 0x83, 0xec, 0x08]; // ASM: sub rsp, 8
    let at = TEXT + u64::try_from(code.len()).expect("small");
    code.extend_from_slice(&call_slot(at, RDATA));
    code.extend_from_slice(&[
        0x48, 0x83, 0xc4, 0x08, // ASM: add rsp, 8
        0xc3, // ASM: ret
    ]);
    let p = image(BinaryFormat::Elf, &code, &[0u8; 8], &["exit"]);
    let (text, _) = decompiled(&p);
    assert!(text.contains("(int32_t a1)"), "{text}");
    assert!(text.contains("exit(a1);"), "{text}");
    let mut code = vec![
        0x53, // ASM: push rbx
        0x48, 0x89, 0xfb, // ASM: mov rbx, rdi
    ];
    let at = TEXT + u64::try_from(code.len()).expect("small");
    code.extend_from_slice(&call_slot(at, RDATA));
    code.extend_from_slice(&[
        0xc6, 0x44, 0x03, 0xff, 0x00, // ASM: mov byte [rbx+rax-1], 0
        0x5b, // ASM: pop rbx
        0xc3, // ASM: ret
    ]);
    let p = image(BinaryFormat::Elf, &code, &[0u8; 8], &["strlen"]);
    let (text, header) = decompiled(&p);
    assert!(text.contains("(char *a1)"), "{text}");
    assert!(!header.contains("contradicted"), "{header}");
}

/// A parameter passed whole as a library function's structure pointer
/// takes that pointer type.
///
/// `inflateEnd(a1)` hands the parameter on as zlib's stream, a
/// `struct z_stream_s *`; `mov rsi, rdi; xor edi, edi` then
/// `clock_gettime(0, a1)` hands it on as a `struct timespec *`. Both read
/// `void *` or `uint64_t` before, which said only how wide.
#[test]
fn a_parameter_passed_as_a_library_structure_takes_its_type() {
    let mut code = vec![0x48, 0x83, 0xec, 0x08]; // ASM: sub rsp, 8
    let at = TEXT + u64::try_from(code.len()).expect("small");
    code.extend_from_slice(&call_slot(at, RDATA));
    code.extend_from_slice(&[
        0x48, 0x83, 0xc4, 0x08, // ASM: add rsp, 8
        0xc3, // ASM: ret
    ]);
    let p = image(BinaryFormat::Elf, &code, &[0u8; 8], &["inflateEnd"]);
    let (text, header) = decompiled(&p);
    assert!(text.contains("(struct z_stream_s *a1)"), "{text}");
    assert!(!header.contains("contradicted"), "{header}");
    let mut code = vec![
        0x48, 0x83, 0xec, 0x08, // ASM: sub rsp, 8
        0x48, 0x89, 0xfe, // ASM: mov rsi, rdi
        0x31, 0xff, // ASM: xor edi, edi
    ];
    let at = TEXT + u64::try_from(code.len()).expect("small");
    code.extend_from_slice(&call_slot(at, RDATA));
    code.extend_from_slice(&[
        0x48, 0x83, 0xc4, 0x08, // ASM: add rsp, 8
        0xc3, // ASM: ret
    ]);
    let p = image(BinaryFormat::Elf, &code, &[0u8; 8], &["clock_gettime"]);
    let (text, header) = decompiled(&p);
    assert!(text.contains("(struct timespec *a1)"), "{text}");
    assert!(!header.contains("contradicted"), "{header}");
}
