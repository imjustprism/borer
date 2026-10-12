//! `borer://calls/{callee}` over hand-built images.
//!
//! Every call site of a function or import, with the arguments the
//! decompiler resolves and the predicate filters that narrow them.

#![expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]

use borer_engine::analysis::render::calls_tsv;
use borer_engine::analysis::{Analysis, Overlay};
use borer_engine::program::{Arch, Program, Section, Symbol, SymbolKind};

/// A raw x64 image whose one function calls an import four times.
///
/// The import `VirtualProtect` is called with a constant protection flag
/// `0x40`, with `0x04`, with the address of a data global, and with the
/// address of a string.
///
/// The slot sits in `.data` at `0x2100`, the global at `0x2000` (zeroed, so
/// it reads as a global and not a literal), and the string at `0x2010`.
fn four_calls() -> Program {
    let mut bytes = vec![0xccu8; 0x3000];
    let code: &[u8] = &[
        // ASM: mov ecx, 0x40
        0xb9, 0x40, 0x00, 0x00, 0x00, // ASM: call qword [rip+0x10f5]  (slot 0x2100)
        0xff, 0x15, 0xf5, 0x10, 0x00, 0x00, // ASM: mov ecx, 4
        0xb9, 0x04, 0x00, 0x00, 0x00, // ASM: call qword [rip+0x10ea]
        0xff, 0x15, 0xea, 0x10, 0x00, 0x00, // ASM: lea rcx, [rip+0xfe3]  (global 0x2000)
        0x48, 0x8d, 0x0d, 0xe3, 0x0f, 0x00, 0x00, // ASM: call qword [rip+0x10dd]
        0xff, 0x15, 0xdd, 0x10, 0x00, 0x00, // ASM: lea rcx, [rip+0xfe6]  (string 0x2010)
        0x48, 0x8d, 0x0d, 0xe6, 0x0f, 0x00, 0x00, // ASM: call qword [rip+0x10d0]
        0xff, 0x15, 0xd0, 0x10, 0x00, 0x00, // ASM: ret
        0xc3,
    ];
    bytes[0x1000..0x1000 + code.len()].copy_from_slice(code);
    bytes[0x2010..0x2018].copy_from_slice(b"cmd.exe\0");
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
    p.symbols = vec![Symbol {
        name: "KERNEL32.dll!VirtualProtect".to_owned(),
        addr: 0x2100,
        kind: SymbolKind::Import,
    }];
    p.function_ranges = vec![(0x1000, 0x1031)];
    p
}

/// Every call to an import through its slot is a row.
///
/// Each argument is in the position its callee reads it: a constant in hex,
/// a global by name, a string quoted, and `?` for the declared parameters
/// the site leaves unset.
#[test]
fn every_call_site_lists_its_arguments() {
    let p = four_calls();
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let out = calls_tsv(&p, &a, &o, "VirtualProtect").expect("calls");
    assert!(
        out.starts_with("# calls to VirtualProtect (slot 0x2100): 4 sites in 1 function"),
        "{out}"
    );
    assert!(out.contains("VirtualProtect(0x40, "), "{out}");
    assert!(out.contains("&g64_2000"), "{out}");
    assert!(out.contains("\"cmd.exe\""), "{out}");
    // The import is declared to take four arguments, so a site that sets
    // only the first pads the rest with `?`.
    assert!(out.contains("VirtualProtect(4, ?, ?, ?)"), "{out}");
    assert!(out.contains("# showing 4 of 4 from 0"), "{out}");
}

/// A predicate keeps only the calls whose argument matches: `a1=0x40` one
/// of the four, `a1=?` none, a text the string argument, and `a1>0x30` the
/// two above `0x30`.
#[test]
fn a_predicate_filters_the_sites() {
    let p = four_calls();
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let one = calls_tsv(&p, &a, &o, "VirtualProtect,a1=0x40").expect("calls");
    assert!(one.contains("# where a1=0x40: 1 site"), "{one}");
    assert!(one.contains("VirtualProtect(0x40, "), "{one}");
    assert!(!one.contains("VirtualProtect(4, "), "{one}");
    let text = calls_tsv(&p, &a, &o, "VirtualProtect,a1=cmd").expect("calls");
    assert!(text.contains("# where a1=cmd: 1 site"), "{text}");
    assert!(text.contains("\"cmd.exe\""), "{text}");
    let lt = calls_tsv(&p, &a, &o, "VirtualProtect,a1<0x10").expect("calls");
    assert!(lt.contains("# where a1<0x10: 1 site"), "{lt}");
    assert!(lt.contains("VirtualProtect(4, "), "{lt}");
}

/// A direct call to a discovered function is a site too, with the argument
/// the caller sets.
#[test]
fn a_direct_call_is_a_site() {
    let mut bytes = vec![0xccu8; 0x2000];
    let code: &[u8] = &[
        // ASM: mov ecx, 7
        0xb9, 0x07, 0x00, 0x00, 0x00, // ASM: call 0x1060  (rel = 0x1060 - 0x100a = 0x56)
        0xe8, 0x56, 0x00, 0x00, 0x00, // ASM: ret
        0xc3,
    ];
    bytes[0x1000..0x1000 + code.len()].copy_from_slice(code);
    // ASM: mov rax, rcx; ret  (reads the first argument)
    bytes[0x1060..0x1064].copy_from_slice(&[0x48, 0x89, 0xc8, 0xc3]);
    let mut p = Program::raw(
        bytes,
        Arch::X86_64,
        0,
        Some(0x1000),
        vec![Section::mapped(
            ".text", 0x1000, 0x1000, 0x1000, false, true,
        )],
    );
    p.function_ranges = vec![(0x1000, 0x100b), (0x1060, 0x1064)];
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let out = calls_tsv(&p, &a, &o, "0x1060").expect("calls");
    assert!(out.contains(": 1 site in 1 function"), "{out}");
    assert!(out.contains("(7)"), "{out}");
}

/// The same request, run twice, gives byte-identical text.
#[test]
fn the_listing_is_deterministic() {
    let p = four_calls();
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let first = calls_tsv(&p, &a, &o, "VirtualProtect").expect("calls");
    let second = calls_tsv(&p, &a, &o, "VirtualProtect").expect("calls");
    assert_eq!(first, second);
}

/// An address inside a function but not its entry is refused, and a bad
/// predicate position too.
#[test]
fn a_mid_function_address_and_a_bad_predicate_are_refused() {
    let p = four_calls();
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let inside = calls_tsv(&p, &a, &o, "0x1008").expect_err("not an entry");
    assert!(inside.contains("not a function's entry"), "{inside}");
    let bad = calls_tsv(&p, &a, &o, "VirtualProtect,a0=4").expect_err("a0");
    assert!(bad.contains("count from one"), "{bad}");
}
