//! A data address a `lea` computes from `rip` is named as the global it
//! is; a value the program also writes as an immediate stays a number.
#![expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]

use borer_engine::analysis::decompile::decompile;
use borer_engine::analysis::{Analysis, Overlay};
use borer_engine::program::{Arch, BinaryFormat, Program, Section};

/// Four x64 leaves at `0x1000`, `.bss` at `0x3000`:
///
/// ```text
/// +0x00 lea rax, [rip + 0x1ff9] ; 0x3000; ret
/// +0x10 mov eax, 0x3008         ; ret
/// +0x20 lea rax, [rip + 0x1fe9] ; 0x3010; ret
/// +0x30 mov eax, 0x3010         ; ret
/// ```
fn image() -> Program {
    let mut bytes = vec![0xccu8; 0x2000];
    let code: [(usize, &[u8]); 4] = [
        (0x00, &[0x48, 0x8d, 0x05, 0xf9, 0x1f, 0x00, 0x00, 0xc3]), // ASM: lea rax, [rip+0x1ff9]; ret
        (0x10, &[0xb8, 0x08, 0x30, 0x00, 0x00, 0xc3]),             // ASM: mov eax, 0x3008; ret
        (0x20, &[0x48, 0x8d, 0x05, 0xe9, 0x1f, 0x00, 0x00, 0xc3]), // ASM: lea rax, [rip+0x1fe9]; ret
        (0x30, &[0xb8, 0x10, 0x30, 0x00, 0x00, 0xc3]),             // ASM: mov eax, 0x3010; ret
    ];
    for (at, b) in code {
        bytes[0x1000 + at..0x1000 + at + b.len()].copy_from_slice(b);
    }
    let mut p = Program::raw(
        bytes,
        Arch::X86_64,
        0,
        Some(0x1000),
        vec![
            Section::mapped(".text", 0x1000, 0x1000, 0x1000, false, true),
            Section {
                file_size: 0,
                ..Section::mapped(".bss", 0x3000, 0, 0x1000, true, false)
            },
        ],
    );
    p.format = BinaryFormat::Elf;
    p.function_ranges = vec![
        (0x1000, 0x1008),
        (0x1010, 0x1016),
        (0x1020, 0x1028),
        (0x1030, 0x1036),
    ];
    p
}

/// Only the `.bss` address no immediate also spells is named.
#[test]
fn a_rip_relative_data_address_is_named_as_its_global() {
    let p = image();
    let a = Analysis::compute(&p);
    let text = |entry| decompile(&p, &a, &Overlay::default(), entry).expect("decompiles");
    assert!(
        text(0x1000).contains("return &g64_3000;"),
        "{}",
        text(0x1000)
    );
    assert!(text(0x1010).contains("return 0x3008;"), "{}", text(0x1010));
    assert!(!text(0x1020).contains("&g64_3010"), "{}", text(0x1020));
    assert!(!text(0x1030).contains("&g64_3010"), "{}", text(0x1030));
}

/// The export declares the global a body names only by its address, and
/// writes it `extern` in the body.
#[test]
fn an_export_declares_a_global_named_by_its_address() {
    use borer_engine::analysis::decompile::export::{Library, export};
    use std::collections::BTreeSet;
    let p = image();
    let a = Analysis::compute(&p);
    let mut body = String::new();
    let only = BTreeSet::from([0x1000]);
    let hoisted = export(
        &p,
        &a,
        &Overlay::default(),
        Library::Skip,
        Some(&only),
        &mut |t| {
            body.push_str(t);
            Ok(())
        },
    )
    .expect("exports");
    let file = format!("{}{body}", hoisted.head("t"));
    assert!(
        file.contains("\nuint64_t g64_3000; // @ 0x3000\n"),
        "{file}"
    );
    assert!(
        file.contains("  extern uint64_t g64_3000; // @ 0x3000\n"),
        "{file}"
    );
}

/// arm64 routines at `0x10000`, `.bss` at `0x20000`:
///
/// ```text
/// +0x00 adrp x0, 0x20000; add x0, x0, #0x10; ret
/// +0x10 mov x0, #0x20; ret
/// +0x20 adrp x8, 0x20000; ldr x0, [x8, #0x18]; ret
/// ```
fn a64_image() -> Program {
    let words: [u32; 10] = [
        0x9000_0080, // ASM: adrp x0, 0x20000
        0x9100_4000, // ASM: add x0, x0, #0x10
        0xd65f_03c0, // ASM: ret
        0xd503_201f, // ASM: nop
        0xd280_0400, // ASM: mov x0, #0x20
        0xd65f_03c0, // ASM: ret
        0xd503_201f, // ASM: nop
        0xd503_201f, // ASM: nop
        0x9000_0088, // ASM: adrp x8, 0x20000
        0xf940_0d00, // ASM: ldr x0, [x8, #0x18]
    ];
    let mut code: Vec<u8> = words.iter().flat_map(|w| w.to_le_bytes()).collect();
    code.extend(0xd65f_03c0u32.to_le_bytes()); // ASM: ret
    let mut p = Program::raw(
        code,
        Arch::Arm64,
        0,
        Some(0x10000),
        vec![
            Section::mapped(".text", 0x10000, 0, 0x2c, false, true),
            Section {
                file_size: 0,
                ..Section::mapped(".bss", 0x20000, 0, 0x1000, true, false)
            },
        ],
    );
    p.format = BinaryFormat::Elf;
    p.function_ranges = vec![(0x10000, 0x1000c), (0x10010, 0x10018), (0x10020, 0x1002c)];
    p
}

/// An arm64 address formed from an `adrp` page and an `add` is named as
/// the global it is, a load through the page reads that global, and a
/// `mov` of a number stays a number.
#[test]
fn an_adrp_page_address_is_named_as_its_global() {
    let p = a64_image();
    let a = Analysis::compute(&p);
    let text = |entry| decompile(&p, &a, &Overlay::default(), entry).expect("decompiles");
    assert!(
        text(0x10000).contains("return &g64_20010;"),
        "{}",
        text(0x10000)
    );
    assert!(text(0x10010).contains("return 32;"), "{}", text(0x10010));
    assert!(
        text(0x10020).contains("return g64_20018;"),
        "{}",
        text(0x10020)
    );
}
