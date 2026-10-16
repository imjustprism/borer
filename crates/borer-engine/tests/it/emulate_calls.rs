//! Emulated API and syscall arguments, decoded by the type library.
//!
//! The emulators record each imported call and syscall they service with its
//! arguments decoded from memory ([`borer_engine::emulate::calls`]): a wide
//! or narrow string read as text, a flag or handle named, an unknown pointer
//! left as `ptr 0x...`. The records show up in `borer://emulate` and feed
//! `borer://iocs` as the `emulated` source.

#![expect(
    clippy::missing_panics_doc,
    clippy::expect_used,
    reason = "assertions are the point of a test"
)]

use borer_engine::analysis::render::{emulate_tsv, iocs_tsv};
use borer_engine::analysis::{Analysis, Overlay};
use borer_engine::emulate::a64::Machine;
use borer_engine::emulate::calls::ArgValue;
use borer_engine::emulate::{Emulator, Stop};
use borer_engine::program::{Arch, BinaryFormat, Program, Section, Symbol, SymbolKind};

/// A raw x64 image whose one function calls `CreateFileW` with a wide path,
/// a flag word, a share word and a wild pointer, through an import slot.
///
/// The wide string sits in `.data` at `0x2000`, the slot at `0x3000`. The
/// format is set to PE so the type library declares the Win32 call.
fn createfilew_image() -> Program {
    let mut bytes = vec![0xccu8; 0x4000];
    let code: &[u8] = &[
        // ASM: movabs rcx, 0x2000  (lpFileName)
        0x48, 0xb9, 0x00, 0x20, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        // ASM: mov edx, 0x80000000  (GENERIC_READ)
        0xba, 0x00, 0x00, 0x00, 0x80, // ASM: mov r8d, 1  (FILE_SHARE_READ)
        0x41, 0xb8, 0x01, 0x00, 0x00, 0x00,
        // ASM: mov r9d, 0xdeadbeef  (a wild lpSecurityAttributes pointer)
        0x41, 0xb9, 0xef, 0xbe, 0xad, 0xde, // ASM: movabs rax, 0x3000  (the import slot)
        0x48, 0xb8, 0x00, 0x30, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        // ASM: mov rax, [rax]  (the stub install_imports planted)
        0x48, 0x8b, 0x00, // ASM: call rax
        0xff, 0xd0, // ASM: ret
        0xc3,
    ];
    bytes[0x1000..0x1000 + code.len()].copy_from_slice(code);
    let wide: Vec<u8> = "C:\\t".encode_utf16().flat_map(u16::to_le_bytes).collect();
    bytes[0x2000..0x2000 + wide.len()].copy_from_slice(&wide);
    let mut p = Program::raw(
        bytes,
        Arch::X86_64,
        0,
        Some(0x1000),
        vec![
            Section::mapped(".text", 0x1000, 0x1000, 0x1000, false, true),
            Section::mapped(".data", 0x2000, 0x2000, 0x2000, true, false),
        ],
    );
    p.format = BinaryFormat::Pe;
    p.symbols = vec![Symbol {
        name: "KERNEL32.dll!CreateFileW".to_owned(),
        addr: 0x3000,
        kind: SymbolKind::Import,
    }];
    p.function_ranges = vec![(
        0x1000,
        0x1000 + u64::try_from(code.len()).expect("a small image"),
    )];
    p
}

/// The recorded call decodes the wide path to text, the flag and share words
/// by name, and the wild pointer as `ptr 0x...`.
#[test]
fn a_win32_call_decodes_its_arguments() {
    let p = createfilew_image();
    let mut emu = Emulator::new(&p, 1000).expect("x64 emulates");
    emu.install_imports();
    let run = emu.run(0x1000);
    assert_eq!(run.stop, Stop::Returned, "{run:?}");
    let calls = emu.api_calls();
    assert_eq!(calls.len(), 1, "{calls:?}");
    let call = &calls[0];
    assert_eq!(call.api, "CreateFileW");
    assert_eq!(
        call.args[0],
        ArgValue::Str {
            text: "C:\\t".to_owned(),
            wide: true
        }
    );
    assert_eq!(call.args[1], ArgValue::Named("GENERIC_READ".to_owned()));
    assert_eq!(call.args[2], ArgValue::Named("FILE_SHARE_READ".to_owned()));
    assert_eq!(call.args[3], ArgValue::Ptr(0xdead_beef));
    assert!(
        call.call_text().contains("ptr 0xdeadbeef"),
        "{}",
        call.call_text()
    );
    assert!(
        call.call_text()
            .starts_with("CreateFileW(L\"C:\\\\t\", GENERIC_READ, FILE_SHARE_READ, ptr 0xdeadbeef"),
        "{}",
        call.call_text()
    );
}

/// A raw x64 ELF whose code opens a path through a Linux `syscall`.
fn open_syscall_image() -> Program {
    let mut bytes = vec![0xccu8; 0x3000];
    let code: &[u8] = &[
        // ASM: mov eax, 2  (open)
        0xb8, 0x02, 0x00, 0x00, 0x00, // ASM: movabs rdi, 0x2000  (the path)
        0x48, 0xbf, 0x00, 0x20, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, // ASM: syscall
        0x0f, 0x05, // ASM: ret
        0xc3,
    ];
    bytes[0x1000..0x1000 + code.len()].copy_from_slice(code);
    bytes[0x2000..0x2000 + 12].copy_from_slice(b"/etc/passwd\0");
    let mut p = Program::raw(
        bytes,
        Arch::X86_64,
        0,
        Some(0x1000),
        vec![
            Section::mapped(".text", 0x1000, 0x1000, 0x1000, false, true),
            Section::mapped(".data", 0x2000, 0x2000, 0x1000, true, false),
        ],
    );
    p.format = BinaryFormat::Elf;
    p.function_ranges = vec![(
        0x1000,
        0x1000 + u64::try_from(code.len()).expect("a small image"),
    )];
    p
}

/// A Linux `syscall` is recorded by name with its path argument decoded.
#[test]
fn an_x86_syscall_is_named_with_its_path() {
    let p = open_syscall_image();
    let mut emu = Emulator::new(&p, 1000).expect("x64 emulates");
    emu.install_imports();
    let run = emu.run(0x1000);
    assert_eq!(run.stop, Stop::Returned, "{run:?}");
    let calls = emu.api_calls();
    assert_eq!(emu.api_names(), ["open"], "{calls:?}");
    assert_eq!(calls[0].syscall, Some(2));
    assert_eq!(calls[0].args[0].text(), Some("/etc/passwd"));
    assert!(
        calls[0]
            .call_text()
            .starts_with("syscall 2 open(\"/etc/passwd\", O_RDONLY"),
        "{}",
        calls[0].call_text()
    );
}

/// `borer://emulate` lists a syscall once, in its calls, and not again on
/// the line of answers given as an unwatched process.
///
/// The run noted every syscall number with those answers as well, so the
/// report told each one twice.
#[test]
fn emulate_lists_a_syscall_once() {
    let p = open_syscall_image();
    let a = Analysis::compute(&p);
    let out = emulate_tsv(&p, &a, &Overlay::default(), "0x1000").expect("the run reports");
    assert_eq!(out.matches("open").count(), 1, "{out}");
    assert!(out.contains("\nsyscall 2 open(\"/etc/passwd\""), "{out}");
    assert!(!out.contains("unwatched"), "{out}");
}

/// A raw arm64 image whose `svc #0` opens a path, recorded by name.
#[test]
fn an_arm64_syscall_is_named_with_its_path() {
    const BASE: u64 = 0x1_0000;
    const PATH_AT: u64 = 0x3_0000;
    let words: [u32; 3] = [
        0xd280_0708, // ASM: movz x8, #56  (openat)
        0xd400_0001, // ASM: svc #0
        0xd65f_03c0, // ASM: ret
    ];
    let code: Vec<u8> = words.iter().flat_map(|w| w.to_le_bytes()).collect();
    let len = u64::try_from(code.len()).expect("a small image");
    let p = Program::raw(
        code,
        Arch::Arm64,
        0,
        Some(BASE),
        vec![Section::mapped(".text", BASE, 0, len, false, true)],
    );
    let mut m = Machine::new(&p, 1000).expect("an arm64 machine");
    for (k, b) in b"/tmp/x\0".iter().enumerate() {
        m.poke(PATH_AT + u64::try_from(k).expect("a small index"), *b);
    }
    assert!(m.set_register("x1", PATH_AT));
    let run = m.run(BASE);
    assert_eq!(run.stop, Stop::Returned, "{run:?}");
    assert_eq!(m.api_names(), ["openat"]);
    let call = &m.api_calls()[0];
    assert_eq!(call.syscall, Some(56));
    assert_eq!(call.strings().collect::<Vec<_>>(), ["/tmp/x"]);
}

/// A raw x64 PE whose generator function (marked by the splitmix64 golden
/// gamma constant) hands a wide URL to `InternetOpenUrlW`.
///
/// The generator recovery runs it, the emulator decodes the URL, and it
/// reaches `borer://iocs` as an `emulated` indicator.
fn generator_calls_url_image() -> Program {
    let mut bytes = vec![0xccu8; 0x4000];
    let code: &[u8] = &[
        // ASM: movabs rax, 0x9e3779b97f4a7c15  (splitmix64 golden gamma)
        0x48, 0xb8, 0x15, 0x7c, 0x4a, 0x7f, 0xb9, 0x79, 0x37, 0x9e,
        // ASM: xor ecx, ecx  (hInternet = NULL)
        0x31, 0xc9, // ASM: movabs rdx, 0x2000  (the wide URL)
        0x48, 0xba, 0x00, 0x20, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        // ASM: xor r8d, r8d  (headers = NULL)
        0x45, 0x31, 0xc0, // ASM: movabs r10, 0x3000  (the import slot)
        0x49, 0xba, 0x00, 0x30, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        // ASM: mov r10, [r10]  (the stub)
        0x4d, 0x8b, 0x12, // ASM: call r10
        0x41, 0xff, 0xd2, // ASM: ret
        0xc3,
    ];
    bytes[0x1000..0x1000 + code.len()].copy_from_slice(code);
    let wide: Vec<u8> = "http://evil.test/campaign"
        .encode_utf16()
        .flat_map(u16::to_le_bytes)
        .collect();
    bytes[0x2000..0x2000 + wide.len()].copy_from_slice(&wide);
    let mut p = Program::raw(
        bytes,
        Arch::X86_64,
        0,
        Some(0x1000),
        vec![
            Section::mapped(".text", 0x1000, 0x1000, 0x1000, false, true),
            Section::mapped(".data", 0x2000, 0x2000, 0x2000, true, false),
        ],
    );
    p.format = BinaryFormat::Pe;
    p.symbols = vec![Symbol {
        name: "WININET.dll!InternetOpenUrlW".to_owned(),
        addr: 0x3000,
        kind: SymbolKind::Import,
    }];
    p.function_ranges = vec![(
        0x1000,
        0x1000 + u64::try_from(code.len()).expect("a small image"),
    )];
    p
}

/// An emulated string argument of a generator run becomes an `emulated`
/// indicator with the calling API named.
#[test]
fn an_emulated_argument_is_an_ioc() {
    let p = generator_calls_url_image();
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let out = iocs_tsv(&p, &a, &o, "").expect("iocs");
    assert!(out.contains("evil.test"), "{out}");
    assert!(out.contains("emulated:InternetOpenUrlW"), "{out}");
}
