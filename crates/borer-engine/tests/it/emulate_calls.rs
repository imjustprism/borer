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

/// A modeled `memset` fills its destination, the first argument, with the
/// byte its second argument holds, as many times as the third says.
///
/// `memset(0x2000, 'A', 8)` through an import slot: the eight bytes at
/// `0x2000` read `A` and the ninth keeps its own byte. The model had the
/// first two swapped and wrote the pointer's low byte at the address `A`.
#[test]
fn a_memset_fills_its_destination_with_its_byte() {
    let mut bytes = vec![0xccu8; 0x4000];
    let code: &[u8] = &[
        0x48, 0xb9, 0x00, 0x20, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, // ASM: movabs rcx,0x2000
        0xba, 0x41, 0x00, 0x00, 0x00, // ASM: mov edx,0x41
        0x41, 0xb8, 0x08, 0x00, 0x00, 0x00, // ASM: mov r8d,8
        0x48, 0xb8, 0x00, 0x30, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, // ASM: movabs rax,0x3000
        0x48, 0x8b, 0x00, // ASM: mov rax,[rax]
        0xff, 0xd0, // ASM: call rax
        0xc3, // ASM: ret
    ];
    bytes[0x1000..0x1000 + code.len()].copy_from_slice(code);
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
        name: "msvcrt.dll!memset".to_owned(),
        addr: 0x3000,
        kind: SymbolKind::Import,
    }];
    let mut emu = Emulator::new(&p, 1000).expect("x64 emulates");
    emu.install_imports();
    let run = emu.run(0x1000);
    assert_eq!(run.stop, Stop::Returned, "{run:?}");
    let filled: Vec<Option<u8>> = (0x2000..0x2009).map(|a| emu.byte_stated(a)).collect();
    let mut want = vec![Some(b'A'); 8];
    want.push(Some(0xcc));
    assert_eq!(filled, want);
}

/// Where [`slot_image`]'s import slot sits.
const SLOT: u64 = 0x3000;

/// Where [`slot_image`]'s writable data starts.
const DATA: u64 = 0x2000;

/// A raw x64 image whose code at `0x1000` calls one import through its
/// slot and returns what the import left in `rax`; a test sets the
/// arguments in the registers the format's convention reads them from.
///
/// The image is based at its first section, so no headers map the null
/// page and a null pointer faults as it does in a real image.
///
/// # Arguments
///
/// * `format` - The format, which picks the convention (PE: `rcx`, `rdx`,
///   `r8`; ELF: `rdi`, `rsi`, `rdx`) and the type library's platform.
/// * `name` - The import, as `dll!name`.
fn slot_image(format: BinaryFormat, name: &str) -> Program {
    let mut bytes = vec![0xccu8; 0x4000];
    let code: &[u8] = &[
        0x48, 0xb8, 0x00, 0x30, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, // ASM: movabs rax,0x3000
        0x48, 0x8b, 0x00, // ASM: mov rax,[rax]
        0xff, 0xd0, // ASM: call rax
        0xc3, // ASM: ret
    ];
    bytes[0x1000..0x1000 + code.len()].copy_from_slice(code);
    let mut p = Program::raw(
        bytes,
        Arch::X86_64,
        0x1000,
        Some(0x1000),
        vec![
            Section::mapped(".text", 0x1000, 0x1000, 0x1000, false, true),
            Section::mapped(".data", DATA, DATA, 0x2000, true, false),
        ],
    );
    p.format = format;
    p.symbols = vec![Symbol {
        name: name.to_owned(),
        addr: SLOT,
        kind: SymbolKind::Import,
    }];
    p
}

/// A call nothing models is recorded as answered by default, by its index
/// among the serviced calls, and a syscall nothing models the same way; a
/// call the emulator models is not.
#[test]
fn calls_nothing_models_are_recorded_as_answered_by_default() {
    let p = createfilew_image();
    let mut emu = Emulator::new(&p, 1000).expect("x64 emulates");
    emu.install_imports();
    assert_eq!(emu.run(0x1000).stop, Stop::Returned);
    assert_eq!(emu.defaulted(), ["CreateFileW"]);
    assert_eq!(emu.defaulted_calls(), [0]);
    let p = open_syscall_image();
    let mut emu = Emulator::new(&p, 1000).expect("x64 emulates");
    emu.install_imports();
    assert_eq!(emu.run(0x1000).stop, Stop::Returned);
    assert_eq!(emu.defaulted(), ["open"]);
    let p = slot_image(BinaryFormat::Pe, "msvcrt.dll!memset");
    let mut emu = Emulator::new(&p, 1000).expect("x64 emulates");
    emu.install_imports();
    assert!(emu.set_register("rcx", DATA));
    assert!(emu.set_register("rdx", 0x41));
    assert!(emu.set_register("r8", 4));
    assert_eq!(emu.run(0x1000).stop, Stop::Returned);
    assert_eq!(emu.api_names(), ["memset"]);
    assert!(emu.defaulted().is_empty(), "{:?}", emu.defaulted());
}

/// Bytes placed before a [`call`]: where, and what.
type Poke<'b> = (u64, &'b [u8]);

/// Runs a [`slot_image`]'s call with `args` in the convention's argument
/// registers and `memory` poked first, under `budget` steps.
///
/// # Arguments
///
/// * `p` - The image.
/// * `args` - The first arguments, in order.
/// * `memory` - Bytes to place before the run.
/// * `budget` - The steps the run may take.
///
/// # Returns
///
/// How the run stopped, and the machine after it.
fn call<'p>(
    p: &'p Program,
    args: &[u64],
    memory: &[Poke<'_>],
    budget: usize,
) -> (Stop, Emulator<'p>) {
    let mut emu = Emulator::new(p, budget).expect("x64 emulates");
    emu.install_imports();
    let regs = if p.format == BinaryFormat::Elf {
        ["rdi", "rsi", "rdx"]
    } else {
        ["rcx", "rdx", "r8"]
    };
    for (r, v) in regs.iter().zip(args) {
        assert!(emu.set_register(r, *v));
    }
    for (at, bytes) in memory {
        for (k, b) in (0u64..).zip(bytes.iter()) {
            emu.poke(at + k, *b);
        }
    }
    let stop = emu.run(0x1000).stop;
    (stop, emu)
}

/// Calls the import `name` of a PE [`slot_image`] and requires it to
/// return.
///
/// # Returns
///
/// What it left in `eax`, and how many calls it answered by default.
fn answer(name: &str, args: &[u64], memory: &[Poke<'_>]) -> (u64, usize) {
    let p = slot_image(BinaryFormat::Pe, name);
    let (stop, emu) = call(&p, args, memory, 100_000);
    assert_eq!(stop, Stop::Returned, "{name}");
    let eax = emu.register("rax").expect("rax") & 0xffff_ffff;
    (eax, emu.defaulted().len())
}

/// `-1` as `eax` holds an `int`.
const LESS: u64 = 0xffff_ffff;

/// The length functions answer as C does.
///
/// They count the characters before the terminator, `strnlen` at most its
/// count, `wcslen` in the target's `wchar_t` (two bytes on Windows, four on
/// ELF). A null or unmapped string faults where `strlen` reads it, and
/// `lstrlenA` answers zero for one; a string with no terminator within the
/// cap stops the run as unmodeled.
#[test]
fn the_string_lengths_answer_as_c_does() {
    let s = b"receipts\0";
    assert_eq!(answer("msvcrt.dll!strlen", &[DATA], &[(DATA, s)]), (8, 0));
    assert_eq!(
        answer("msvcrt.dll!strnlen", &[DATA, 3], &[(DATA, s)]),
        (3, 0)
    );
    assert_eq!(
        answer("msvcrt.dll!strnlen", &[DATA, 20], &[(DATA, s)]),
        (8, 0)
    );
    assert_eq!(
        answer(
            "msvcrt.dll!wcslen",
            &[DATA],
            &[(DATA, &[b'a', 0, b'b', 0, 0, 0])]
        ),
        (2, 0)
    );
    let elf = slot_image(BinaryFormat::Elf, "wcslen");
    let four = [b'a', 0, 0, 0, b'b', 0, 0, 0, b'c', 0, 0, 0, 0, 0, 0, 0];
    let (stop, emu) = call(&elf, &[DATA], &[(DATA, &four)], 1000);
    assert_eq!((stop, emu.register("rax")), (Stop::Returned, Some(3)));
    for wild in [0, 0xdead_0000] {
        let p = slot_image(BinaryFormat::Pe, "msvcrt.dll!strlen");
        assert_eq!(call(&p, &[wild], &[], 1000).0, Stop::Fault(wild));
        assert_eq!(answer("KERNEL32.dll!lstrlenA", &[wild], &[]), (0, 0));
    }
    let p = slot_image(BinaryFormat::Pe, "msvcrt.dll!strlen");
    let long = vec![b'A'; 0x1_0001];
    let (stop, _) = call(&p, &[0x10_0000], &[(0x10_0000, &long)], 100_000);
    assert!(
        matches!(&stop, Stop::Unmodeled(what) if what.starts_with("strlen past 0x10000")),
        "{stop:?}"
    );
}

/// The compares answer the sign C promises.
///
/// The first differing `unsigned char` decides, bytes past a terminator are
/// not compared (`strncmp` stops at its count too), `memcmp` compares past
/// a zero, and `wcscmp` compares whole characters.
#[test]
fn the_string_compares_answer_as_c_does() {
    let (x, y) = (DATA, DATA + 0x100);
    let both = |a: &'static [u8], b: &'static [u8]| [(x, a), (y, b)];
    let strcmp =
        |a: &'static [u8], b: &'static [u8]| answer("msvcrt.dll!strcmp", &[x, y], &both(a, b)).0;
    assert_eq!(strcmp(b"abc\0", b"abc\0"), 0);
    assert_eq!(strcmp(b"abc\0", b"abz\0"), LESS);
    assert_eq!(strcmp(b"abz\0", b"abc\0"), 1);
    assert_eq!(strcmp(b"ab\0x", b"ab\0y"), 0);
    assert_eq!(strcmp(b"\x80\0", b"\x7f\0"), 1);
    let strncmp = |n: u64, a: &'static [u8], b: &'static [u8]| {
        answer("msvcrt.dll!strncmp", &[x, y, n], &both(a, b)).0
    };
    assert_eq!(strncmp(2, b"abX\0", b"abY\0"), 0);
    assert_eq!(strncmp(3, b"abX\0", b"abY\0"), LESS);
    assert_eq!(
        answer("msvcrt.dll!memcmp", &[x, y, 4], &both(b"ab\0X", b"ab\0Y")).0,
        LESS
    );
    assert_eq!(
        answer(
            "msvcrt.dll!wcscmp",
            &[x, y],
            &both(&[b'a', 0, 0, 0], &[b'b', 0, 0, 0])
        )
        .0,
        LESS
    );
}

/// The case-folding calls answer only while every character is ASCII.
///
/// The compares and `tolower`/`toupper` fold `A`..`Z` alone, as the C
/// locale does. At a character at or above `0x80` the locale decides, so
/// the call answers zero as not modeled; a difference decided before such a
/// byte still answers.
#[test]
fn the_case_folding_calls_answer_for_ascii_only() {
    let (x, y) = (DATA, DATA + 0x100);
    let stricmp = |a: &'static [u8], b: &'static [u8]| {
        answer("msvcrt.dll!_stricmp", &[x, y], &[(x, a), (y, b)])
    };
    assert_eq!(stricmp(b"ReCeIpT\0", b"receipt\0"), (0, 0));
    assert_eq!(stricmp(b"ab\xe9\0", b"ab\xe9\0"), (0, 1));
    assert_eq!(stricmp(b"ab\xe9\0", b"ac\xe9\0"), (LESS, 0));
    let case = |name, c| answer(name, &[c], &[]);
    assert_eq!(
        case("msvcrt.dll!tolower", u64::from(b'A')),
        (u64::from(b'a'), 0)
    );
    assert_eq!(
        case("msvcrt.dll!toupper", u64::from(b'q')),
        (u64::from(b'Q'), 0)
    );
    assert_eq!(case("msvcrt.dll!tolower", 0xffff_ffff), (0xffff_ffff, 0));
    assert_eq!(case("msvcrt.dll!tolower", 0xe9), (0, 1));
}

/// The copies answer as C does.
///
/// `strcpy` copies to and with the terminator and returns its destination,
/// `strncpy` pads with zeros to its count and copies no terminator past it,
/// `strcat` appends after the destination's terminator, `mempcpy` returns
/// the end of what it copied, and `_strdup` copies into a fresh region.
#[test]
fn the_string_copies_answer_as_c_does() {
    let (d, s) = (DATA, DATA + 0x100);
    let copy = |name: &str, args: &[u64], dst: &'static [u8], n: u64| {
        let p = slot_image(BinaryFormat::Pe, name);
        let (stop, emu) = call(&p, args, &[(d, dst), (s, b"abc\0")], 1000);
        assert_eq!(stop, Stop::Returned, "{name}");
        let after: Vec<u8> = (d..d + n)
            .map(|a| emu.byte_stated(a).unwrap_or(0))
            .collect();
        (emu.register("rax"), after)
    };
    let fill = &[0xaa; 8];
    assert_eq!(
        copy("msvcrt.dll!strcpy", &[d, s], fill, 6),
        (Some(d), b"abc\0\xaa\xaa".to_vec())
    );
    assert_eq!(
        copy("msvcrt.dll!strncpy", &[d, s, 6], fill, 8),
        (Some(d), b"abc\0\0\0\xaa\xaa".to_vec())
    );
    assert_eq!(
        copy("msvcrt.dll!strncpy", &[d, s, 2], fill, 4),
        (Some(d), b"ab\xaa\xaa".to_vec())
    );
    assert_eq!(
        copy("msvcrt.dll!strcat", &[d, s], b"xy\0\xaa\xaa\xaa\xaa\xaa", 6),
        (Some(d), b"xyabc\0".to_vec())
    );
    assert_eq!(
        copy("msvcrt.dll!mempcpy", &[d, s, 3], fill, 4),
        (Some(d + 3), b"abc\xaa".to_vec())
    );
    let p = slot_image(BinaryFormat::Pe, "msvcrt.dll!_strdup");
    let (stop, emu) = call(&p, &[s], &[(s, b"abc\0")], 1000);
    assert_eq!(stop, Stop::Returned);
    let at = emu.register("rax").expect("rax");
    assert_ne!(at, 0);
    let copied: Vec<Option<u8>> = (at..at + 4).map(|a| emu.byte_stated(a)).collect();
    assert_eq!(copied, [Some(b'a'), Some(b'b'), Some(b'c'), Some(0)]);
}

/// The searches answer as C does.
///
/// `strchr` finds the terminator too, `strrchr` the last match, `memchr`
/// only within its count, `strstr` an empty needle at the start, `strspn`
/// and `strcspn` count a prefix in or out of a set, `strpbrk` and the wide
/// `wcschr`/`wcsrchr` find as their narrow kin do, and a miss is `NULL`.
#[test]
fn the_string_searches_answer_as_c_does() {
    let (s, t) = (DATA, DATA + 0x100);
    let hay: &[Poke<'_>] = &[(s, b"abcabc\0")];
    let find = |name, args: &[u64], memory: &[Poke<'_>]| answer(name, args, memory).0;
    assert_eq!(find("msvcrt.dll!strchr", &[s, u64::from(b'c')], hay), s + 2);
    assert_eq!(find("msvcrt.dll!strchr", &[s, 0], hay), s + 6);
    assert_eq!(find("msvcrt.dll!strchr", &[s, u64::from(b'z')], hay), 0);
    assert_eq!(
        find("msvcrt.dll!strrchr", &[s, u64::from(b'c')], hay),
        s + 5
    );
    assert_eq!(find("msvcrt.dll!memchr", &[s, u64::from(b'c'), 2], hay), 0);
    assert_eq!(
        find("msvcrt.dll!memchr", &[s, u64::from(b'c'), 3], hay),
        s + 2
    );
    let with = |needle: &'static [u8]| [(s, b"abcabc\0".as_slice()), (t, needle)];
    assert_eq!(find("msvcrt.dll!strstr", &[s, t], &with(b"ca\0")), s + 2);
    assert_eq!(find("msvcrt.dll!strstr", &[s, t], &with(b"\0")), s);
    assert_eq!(find("msvcrt.dll!strstr", &[s, t], &with(b"cb\0")), 0);
    assert_eq!(find("msvcrt.dll!strspn", &[s, t], &with(b"ab\0")), 2);
    assert_eq!(find("msvcrt.dll!strcspn", &[s, t], &with(b"c\0")), 2);
    assert_eq!(find("msvcrt.dll!strpbrk", &[s, t], &with(b"cb\0")), s + 1);
    assert_eq!(find("msvcrt.dll!strpbrk", &[s, t], &with(b"xyz\0")), 0);
    let wide: &[Poke<'_>] = &[(s, &[b'a', 0, b'b', 0, b'c', 0, b'a', 0, 0, 0])];
    assert_eq!(
        find("msvcrt.dll!wcschr", &[s, u64::from(b'c')], wide),
        s + 4
    );
    assert_eq!(
        find("msvcrt.dll!wcsrchr", &[s, u64::from(b'a')], wide),
        s + 6
    );
}

/// A 32-bit image whose code at `0x1000` pushes [`DATA`] and calls one
/// import through its slot, popping the argument itself when `cdecl`.
///
/// # Arguments
///
/// * `name` - The import, as `dll!name`.
/// * `cdecl` - Whether the caller pops the argument.
fn stack_image(name: &str, cdecl: bool) -> Program {
    let mut bytes = vec![0xccu8; 0x4000];
    let mut code = vec![
        0x68, 0x00, 0x20, 0x00, 0x00, // ASM: push 0x2000
        0xff, 0x15, 0x00, 0x30, 0x00, 0x00, // ASM: call [0x3000]
    ];
    if cdecl {
        code.extend_from_slice(&[0x83, 0xc4, 0x04]); // ASM: add esp,4
    }
    code.push(0xc3); // ASM: ret
    bytes[0x1000..0x1000 + code.len()].copy_from_slice(&code);
    let mut p = Program::raw(
        bytes,
        Arch::X86,
        0,
        Some(0x1000),
        vec![
            Section::mapped(".text", 0x1000, 0x1000, 0x1000, false, true),
            Section::mapped(".data", DATA, DATA, 0x2000, true, false),
        ],
    );
    p.format = BinaryFormat::Pe;
    p.symbols = vec![Symbol {
        name: name.to_owned(),
        addr: SLOT,
        kind: SymbolKind::Import,
    }];
    p
}

/// A 32-bit string call takes its argument by its convention.
///
/// The argument is on the stack, and the callee pops it only where its
/// convention says: `msvcrt`'s `strlen` is `__cdecl` and `kernel32`'s
/// `lstrlenA` `__stdcall`. A wrong pop leaves the stack off by a word, and
/// the run does not return.
#[test]
fn a_32_bit_string_call_takes_its_argument_by_its_convention() {
    for (name, cdecl) in [
        ("msvcrt.dll!strlen", true),
        ("KERNEL32.dll!lstrlenA", false),
    ] {
        let p = stack_image(name, cdecl);
        let mut emu = Emulator::new(&p, 10_000).expect("x86 emulates");
        emu.install_imports();
        for (k, b) in (0u64..).zip(b"receipts\0") {
            emu.poke(DATA + k, *b);
        }
        assert_eq!(emu.run(0x1000).stop, Stop::Returned, "{name}");
        assert_eq!(emu.register("rax"), Some(8), "{name}");
    }
}

/// A copy of as many bytes as one call is modeled for still copies, and
/// one byte more stops the run, where it copied part and answered success.
#[test]
fn a_copy_past_the_cap_stops_instead_of_cutting_short() {
    /// The most bytes one modeled call reads or writes.
    const CAP: u64 = 0x1_0000;
    let source = vec![0x41u8; 0x1_0001];
    for name in ["msvcrt.dll!memcpy", "msvcrt.dll!memset"] {
        let p = slot_image(BinaryFormat::Pe, name);
        let memory = [(0x20_0000, source.as_slice())];
        let (stop, _) = call(&p, &[0x10_0000, 0x20_0000, CAP], &memory, 1000);
        assert_eq!(stop, Stop::Returned, "{name}");
        let (stop, _) = call(&p, &[0x10_0000, 0x20_0000, CAP + 1], &memory, 1000);
        assert!(
            matches!(&stop, Stop::Unmodeled(what) if what.contains("past 0x10000")),
            "{name}: {stop:?}"
        );
    }
}

/// A copy reads its source as a load does: a source nothing backs faults
/// at its first byte, where it once read as zeros and the copy succeeded.
#[test]
fn a_copy_from_memory_nothing_backs_faults_there() {
    let wild = 0xdead_0000;
    for name in [
        "msvcrt.dll!memcpy",
        "msvcrt.dll!memmove",
        "msvcrt.dll!mempcpy",
    ] {
        let p = slot_image(BinaryFormat::Pe, name);
        let (stop, emu) = call(&p, &[0x10_0000, wild, 4], &[], 1000);
        assert_eq!(stop, Stop::Fault(wild), "{name}");
        assert_eq!(emu.byte_at(0x10_0000), None, "{name} wrote its destination");
    }
}

/// A scan spends a step of the budget per character, as a `rep` string
/// instruction does, so one the budget cannot pay stops at the budget.
#[test]
fn a_string_scan_spends_the_budget() {
    let p = slot_image(BinaryFormat::Pe, "msvcrt.dll!strlen");
    let long = vec![b'A'; 0x400];
    let (stop, _) = call(&p, &[0x10_0000], &[(0x10_0000, &long)], 100);
    assert_eq!(stop, Stop::Budget);
}
