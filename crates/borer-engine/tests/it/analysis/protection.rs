//! Protection, capabilities, checks and anti-analysis reports.

use super::*;

/// The protection profile says whether reading the text is worth anything.
///
/// A packer leaves a name in its sections, a body that is all entropy, an
/// import table too thin to run, and megabytes of executable bytes with
/// almost no code in them. The fixture has none of that and says so.
#[test]
fn the_protection_profile_tells_packed_from_plain() {
    let p = fixture();
    let a = Analysis::compute(&p);
    let plain = borer_engine::analysis::render::protection_tsv(&p, &a);
    assert!(plain.starts_with("# plain"), "{plain}");

    let mut bytes = vec![0xccu8; 0x1000];
    let mut seed: u64 = 0x2545_f491_4f6c_dd1d;
    bytes.extend((0..0x40000).map(|_| {
        seed ^= seed << 13;
        seed ^= seed >> 7;
        seed ^= seed << 17;
        u8::try_from(seed >> 56).unwrap_or(0)
    }));
    let packed = Program::raw(
        bytes,
        Arch::X86_64,
        0,
        Some(0x1000),
        vec![Section::mapped(
            ".vmp0", 0x1000, 0x1000, 0x40000, true, true,
        )],
    );
    let pa = Analysis::compute(&packed);
    let text = borer_engine::analysis::render::protection_tsv(&packed, &pa);
    assert!(text.starts_with("# protected: VMProtect"), "{text}");
    assert!(text.contains("entropy 7.2 or above"), "{text}");
    assert!(text.contains("writable and executable"), "{text}");
}

/// A synchronization wrapper that compares rwlock state bits is never a
/// check, and its `is_unlocked` assertion says no phrase.
///
/// `FX` in the fixture image references an `is_unlocked` assertion and
/// compares against `0x40000000` and `0xc0000000`, the futex rwlock reader
/// and writer bits: a std wrapper every Rust binary carries, which once
/// stood as the only check a crackme listed.
#[test]
fn a_sync_bitmask_compare_is_not_a_check() {
    let p = fixture();
    let a = Analysis::compute(&p);
    let text = borer_engine::analysis::render::license_checks_tsv(&p, &a, &Overlay::default());
    assert!(text.starts_with("# 0 functions judge"), "{text}");
    assert!(!text.contains("(unlock)"), "{text}");
    assert!(!text.contains("0x40000000"), "{text}");
    assert!(!text.contains("0xc0000000"), "{text}");
}

/// A check no phrase names is found by what it reads and what it tests.
///
/// `KC` in the fixture image calls `scanf` into the buffer its parameter
/// points at and compares a byte of what it read against the value the
/// call parsed: the shape of `check(key(name), serial)` with the keygen
/// math on one side and the input on the other, and not a string in it.
#[test]
fn an_unnamed_check_is_found_by_what_it_reads_and_tests() {
    let p = fixture();
    let a = Analysis::compute(&p);
    let text = borer_engine::analysis::render::license_checks_tsv(&p, &a, &Overlay::default());
    assert!(
        text.starts_with(
            "# 0 functions judge a key, serial or license; 1 more test what they read"
        ),
        "{text}"
    );
    assert!(
        text.contains(
            "# 1 read input and test what they compute against it: sub_5c40 (a value it parsed)"
        ),
        "{text}"
    );
}

/// The capability map groups imports into what they let the program do.
///
/// The first question about an unknown binary is what it can do, and the
/// imports answer most of it. A program importing `WriteProcessMemory`
/// injects; one importing `SendMessageA` does not thereby talk on the
/// network, which the exact-match socket verbs ensure.
#[test]
fn the_capability_map_groups_imports() {
    let mut p = fixture();
    p.symbols = [
        "KERNEL32.dll!WriteProcessMemory",
        "USER32.dll!SendMessageA",
        "WS2_32.dll!connect",
    ]
    .iter()
    .map(|n| Symbol {
        name: (*n).to_owned(),
        addr: 0,
        kind: SymbolKind::Import,
    })
    .collect();
    let text = borer_engine::analysis::render::capability_map_tsv(&p, None);
    assert!(text.contains("process injection"), "{text}");
    assert!(text.contains("WriteProcessMemory"), "{text}");
    assert!(text.contains("networking"), "{text}");
    assert!(text.contains("connect"), "{text}");
    assert!(
        !text.contains("SendMessageA"),
        "a window message read as networking: {text}"
    );
}

/// What every program that checks its own elevation or paints a window
/// imports names no injection and no screen capture.
///
/// Notepad imports `OpenProcessToken` (reading its own token) and `GetDC`
/// (painting); the map listed them as process injection and screen
/// capture, since `openprocess` is a prefix of the token call.
///
/// # Panics
///
/// When either import lands in either capability, or `OpenProcess` stops
/// counting as injection.
#[test]
fn the_capability_map_does_not_read_token_or_paint_calls_as_attacks() {
    let mut p = fixture();
    let imports = |names: &[&str]| -> Vec<Symbol> {
        names
            .iter()
            .map(|n| Symbol {
                name: format!("KERNEL32.dll!{n}"),
                addr: 0,
                kind: SymbolKind::Import,
            })
            .collect()
    };
    p.symbols = imports(&["OpenProcessToken", "GetDC"]);
    let text = borer_engine::analysis::render::capability_map_tsv(&p, None);
    assert!(!text.contains("process injection"), "{text}");
    assert!(!text.contains("screen capture"), "{text}");
    p.symbols = imports(&["OpenProcess"]);
    let text = borer_engine::analysis::render::capability_map_tsv(&p, None);
    assert!(text.contains("process injection"), "{text}");
}

/// The anti-analysis report finds the stealthy instruction tells.
///
/// A routine of `cpuid; rdtsc; sidt; in; int3` carries three strong tells a
/// compiler never emits (the descriptor-table read, the port `in`, the
/// trap), so the verdict calls it out; `cpuid` and one `rdtsc` alone would not.
#[test]
fn the_anti_analysis_report_finds_the_tells() {
    let mut bytes = vec![0xc3u8; 0x1000];
    let code = [
        0x0fu8, 0xa2, 0x0f, 0x31, 0x0f, 0x01, 0x0c, 0x24, 0xed, 0xcc, 0xc3,
    ];
    bytes[0x40..0x40 + code.len()].copy_from_slice(&code);
    let mut p = Program::raw(
        bytes,
        Arch::X86_64,
        0,
        Some(0x1040),
        vec![Section::mapped(".text", 0x1000, 0, 0x1000, false, true)],
    );
    p.function_ranges = vec![(0x1040, 0x104b)];
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let text = borer_engine::analysis::render::anti_analysis_tsv(&p, &a, &o);
    assert!(
        text.starts_with("# anti-analysis:"),
        "verdict wrong: {text}"
    );
    assert!(text.contains("descriptor-table"), "{text}");
    assert!(text.contains("port read"), "{text}");
    assert!(text.contains("debugger trap"), "{text}");
    let plain = borer_engine::analysis::render::anti_analysis_tsv(
        &fixture(),
        &Analysis::compute(&fixture()),
        &o,
    );
    assert!(
        !plain.starts_with("# anti-analysis:"),
        "plain flagged: {plain}"
    );
}

/// The traps a compiler emits and the imports every C runtime carries do
/// not make a program one that resists being watched.
///
/// MSVC follows a call that does not return with `nop; int3`, and its
/// runtime imports `IsDebuggerPresent`; notepad, msvcrt and sqlite were
/// each called anti-analysis for exactly that. A real trap (an `int3` the
/// code runs into) still counts, beside an import only an anti-debugger
/// uses. Three `in al, dx` are one technique, not three: msvcrt's `_inp`
/// reads a port because that is what it is for.
///
/// # Panics
///
/// When the compiler's trap is counted or the runtime import tips the
/// verdict, or a real trap beside a telling import does not.
#[test]
fn compiler_traps_and_runtime_imports_are_not_anti_analysis() {
    let build = |code: &[u8], import: &str| {
        let mut bytes = vec![0xc3u8; 0x2000];
        bytes[0x40..0x40 + code.len()].copy_from_slice(code);
        let mut p = Program::raw(
            bytes,
            Arch::X86_64,
            0,
            Some(0x1040),
            vec![
                Section::mapped(".text", 0x1000, 0, 0x1000, false, true),
                Section::mapped(".rdata", 0x2000, 0x1000, 0x1000, false, false),
            ],
        );
        p.function_ranges = vec![(0x1040, 0x1040 + from_usize(code.len()))];
        p.symbols.push(Symbol {
            name: format!("KERNEL32.dll!{import}"),
            addr: 0x2000,
            kind: SymbolKind::Import,
        });
        let a = Analysis::compute(&p);
        borer_engine::analysis::render::anti_analysis_tsv(&p, &a, &Overlay::default())
    };
    let trap_after_call = [
        0x85u8, 0xc0, 0x74, 0x07, 0xe8, 0xb7, 0x00, 0x00, 0x00, 0x90, 0xcc, 0xc3,
    ];
    let quiet = build(&trap_after_call, "IsDebuggerPresent");
    assert!(!quiet.starts_with("# anti-analysis:"), "{quiet}");
    assert!(!quiet.contains("debugger trap"), "{quiet}");
    let real_trap = [0x31u8, 0xc0, 0xcc, 0xc3];
    let runtime = build(&real_trap, "IsDebuggerPresent");
    assert!(!runtime.starts_with("# anti-analysis:"), "{runtime}");
    assert!(runtime.contains("debugger trap"), "{runtime}");
    let telling = build(&real_trap, "CheckRemoteDebuggerPresent");
    assert!(telling.starts_with("# anti-analysis:"), "{telling}");
    let port_reads = [0xecu8, 0xec, 0xec, 0xc3];
    let one_technique = build(&port_reads, "IsDebuggerPresent");
    assert!(
        !one_technique.starts_with("# anti-analysis:"),
        "{one_technique}"
    );
}

/// The check finder pins the serial routine and the value it wants.
///
/// A function that references "incorrect serial" and compares the input to
/// `0xdeadbeef` is exactly a crackme's check; the finder lists it under the
/// phrase with that constant, which is the value to forge or the branch to
/// patch.
#[test]
fn the_check_finder_pins_a_serial_routine() {
    let mut bytes = vec![0xccu8; 0x3000];
    let code = [
        0x48u8, 0x8d, 0x0d, 0xb9, 0x0f, 0x00, 0x00, 0x3d, 0xef, 0xbe, 0xad, 0xde, 0x75, 0x01, 0xc3,
        0xc3,
    ];
    bytes[0x1040..0x1040 + code.len()].copy_from_slice(&code);
    bytes[0x2000..0x2011].copy_from_slice(b"incorrect serial\0");
    let mut p = Program::raw(
        bytes,
        Arch::X86_64,
        0,
        Some(0x1040),
        vec![
            Section::mapped(".text", 0x1000, 0x1000, 0x1000, false, true),
            Section::mapped(".rdata", 0x2000, 0x2000, 0x1000, false, false),
        ],
    );
    p.function_ranges = vec![(0x1040, 0x1050)];
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let text = borer_engine::analysis::render::license_checks_tsv(&p, &a, &o);
    assert!(
        text.contains("serial"),
        "the serial routine is not found: {text}"
    );
    assert!(
        text.contains("0xdeadbeef"),
        "the tested constant is not shown: {text}"
    );
    let plain = borer_engine::analysis::render::license_checks_tsv(
        &fixture(),
        &Analysis::compute(&fixture()),
        &o,
    );
    assert!(
        plain.starts_with("# 0 ") || !plain.contains("0xdeadbeef"),
        "{plain}"
    );
}

/// Dynamic-import recovery names an API resolved through `GetProcAddress`.
///
/// A function that calls `GetProcAddress(h, "WriteProcessMemory")` imports
/// that API without it appearing in the table; the recovery decompiles the
/// caller and lists the resolved name.
#[test]
fn dynamic_imports_name_a_resolved_api() {
    let mut bytes = vec![0xccu8; 0x3000];
    let code = [
        0x31u8, 0xc9, 0x48, 0x8d, 0x15, 0xb7, 0x0f, 0x00, 0x00, 0xff, 0x15, 0xb1, 0x17, 0x00, 0x00,
        0xc3,
    ];
    bytes[0x1040..0x1040 + code.len()].copy_from_slice(&code);
    bytes[0x2000..0x2013].copy_from_slice(b"WriteProcessMemory\0");
    let mut p = Program::raw(
        bytes,
        Arch::X86_64,
        0,
        Some(0x1040),
        vec![
            Section::mapped(".text", 0x1000, 0x1000, 0x1000, false, true),
            Section::mapped(".rdata", 0x2000, 0x2000, 0x1000, false, false),
        ],
    );
    p.symbols = vec![Symbol {
        name: "KERNEL32.dll!GetProcAddress".to_owned(),
        addr: 0x2800,
        kind: SymbolKind::Import,
    }];
    p.function_ranges = vec![(0x1040, 0x1050)];
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let text = borer_engine::analysis::render::dynamic_imports_tsv(&p, &a, &o);
    assert!(
        text.contains("WriteProcessMemory"),
        "the resolved API is not recovered: {text}"
    );
}
