//! The translation-unit closure: a decompiled function declares every
//! function it calls and every table of functions it indexes, so its text
//! compiles on its own.
#![expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]

use borer_engine::analysis::decompile::decompile;
use borer_engine::analysis::{Analysis, Overlay};
use borer_engine::program::{Arch, BinaryFormat, Program, Symbol, SymbolKind};

/// Where [`crate::raw::image`] maps the code.
const TEXT: u64 = 0x40_1000;
/// Where it maps the read-only data: the table of operations.
const RDATA: u64 = 0x40_2000;

/// Microsoft x64 routines at [`TEXT`]:
///
/// ```text
/// even(n)        : n ? odd(n - 1) : 1                at +0x00
/// odd(n)         : n ? even(n - 1) : 0               at +0x20
/// dispatch(o,a,b): ops[o & 3](a, b), ops at RDATA     at +0x40
/// op_add(a, b)   : a + b                             at +0x60
/// op_sub(a, b)   : a - b                             at +0x70
/// ```
const ROUTINES: [(usize, &[u8]); 22] = [
    (0x00, &[0x85, 0xc9]),                         // ASM: test ecx, ecx (even)
    (0x02, &[0x74, 0x10]),                         // ASM: je even+0x14
    (0x04, &[0x48, 0x83, 0xec, 0x28]),             // ASM: sub rsp, 0x28
    (0x08, &[0xff, 0xc9]),                         // ASM: dec ecx
    (0x0a, &[0xe8, 0x11, 0x00, 0x00, 0x00]),       // ASM: call odd
    (0x0f, &[0x48, 0x83, 0xc4, 0x28, 0xc3]),       // ASM: add rsp, 0x28; ret
    (0x14, &[0xb8, 0x01, 0x00, 0x00, 0x00, 0xc3]), // ASM: mov eax, 1; ret
    (0x20, &[0x85, 0xc9]),                         // ASM: test ecx, ecx (odd)
    (0x22, &[0x74, 0x10]),                         // ASM: je odd+0x14
    (0x24, &[0x48, 0x83, 0xec, 0x28]),             // ASM: sub rsp, 0x28
    (0x28, &[0xff, 0xc9]),                         // ASM: dec ecx
    (0x2a, &[0xe8, 0xd1, 0xff, 0xff, 0xff]),       // ASM: call even
    (0x2f, &[0x48, 0x83, 0xc4, 0x28, 0xc3]),       // ASM: add rsp, 0x28; ret
    (0x34, &[0x31, 0xc0, 0xc3]),                   // ASM: xor eax, eax; ret
    (0x40, &[0x83, 0xe1, 0x03]),                   // ASM: and ecx, 3 (dispatch)
    (0x43, &[0x48, 0x8d, 0x05, 0xb6, 0x0f, 0x00, 0x00]), // ASM: lea rax, [rip + 0xfb6]
    (0x4a, &[0x48, 0x8b, 0x04, 0xc8]),             // ASM: mov rax, [rax + rcx*8]
    (0x4e, &[0x48, 0x89, 0xd1, 0x4c, 0x89, 0xc2]), // ASM: mov rcx, rdx; mov rdx, r8
    (0x54, &[0x48, 0x83, 0xec, 0x28, 0xff, 0xd0]), // ASM: sub rsp, 0x28; call rax
    (0x5a, &[0x48, 0x83, 0xc4, 0x28, 0xc3]),       // ASM: add rsp, 0x28; ret
    (0x60, &[0x8d, 0x04, 0x11, 0xc3]),             // ASM: lea eax, [rcx + rdx]; ret (op_add)
    (0x70, &[0x89, 0xc8, 0x29, 0xd0, 0xc3]),       // ASM: mov eax, ecx; sub eax, edx; ret (op_sub)
];

/// [`ROUTINES`] as a PE-like image: `even`, `odd` and `dispatch`
/// exported, the operations local, and `ops` in read-only data.
fn image() -> Program {
    let mut code = vec![0xccu8; 0x80];
    for (at, bytes) in ROUTINES {
        code[at..at + bytes.len()].copy_from_slice(bytes);
    }
    let ops: Vec<u8> = [0x60u64, 0x70, 0x60, 0x70]
        .iter()
        .flat_map(|off| (TEXT + off).to_le_bytes())
        .collect();
    let mut p = crate::raw::image(Arch::X86_64, &code, &ops);
    p.format = BinaryFormat::Pe;
    let named = |name: &str, addr: u64, kind: SymbolKind| Symbol {
        name: name.to_owned(),
        addr,
        kind,
    };
    p.symbols = vec![
        named("even", TEXT, SymbolKind::Export),
        named("odd", TEXT + 0x20, SymbolKind::Export),
        named("dispatch", TEXT + 0x40, SymbolKind::Export),
        named("op_add", TEXT + 0x60, SymbolKind::Local),
        named("op_sub", TEXT + 0x70, SymbolKind::Local),
    ];
    p
}

/// Two exported functions that call each other each declare the other
/// with a prototype from its ABI facts, before the body.
#[test]
fn mutual_recursion_declares_the_other_function() {
    let p = image();
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    for (entry, own, other) in [(TEXT, "even", "odd"), (TEXT + 0x20, "odd", "even")] {
        let text = decompile(&p, &a, &o, entry).expect("decompiles");
        let lines: Vec<&str> = text.lines().collect();
        let proto = lines
            .iter()
            .position(|l| l.starts_with("extern ") && l.contains(&format!(" {other}(")))
            .unwrap_or_else(|| panic!("{other} is declared: {text}"));
        let call = lines
            .iter()
            .position(|l| !l.starts_with("extern ") && l.contains(&format!("{other}(")))
            .unwrap_or_else(|| panic!("{other} is called: {text}"));
        assert!(proto < call, "{text}");
        assert!(
            !lines
                .iter()
                .any(|l| l.starts_with("extern ") && l.contains(&format!(" {own}("))),
            "{text}"
        );
    }
}

/// A table of local functions in read-only data is an array of function
/// designators, and the functions it names are defined in the unit, each
/// once, before it.
#[test]
fn a_table_of_functions_is_declared_with_their_bodies() {
    let p = image();
    let a = Analysis::compute(&p);
    let text = decompile(&p, &a, &Overlay::default(), TEXT + 0x40).expect("decompiles");
    let lines: Vec<&str> = text.lines().collect();
    let def = |name: &str| {
        let found: Vec<usize> = lines
            .iter()
            .enumerate()
            .filter(|(_, l)| l.starts_with("static inline ") && l.contains(&format!(" {name}(")))
            .map(|(i, _)| i)
            .collect();
        assert_eq!(found.len(), 1, "{name} is defined once: {text}");
        found[0]
    };
    let (add, sub) = (def("op_add"), def("op_sub"));
    let table = lines
        .iter()
        .position(|l| l.contains("[4]") && l.ends_with("= {op_add, op_sub, op_add, op_sub};"))
        .unwrap_or_else(|| panic!("the table is declared: {text}"));
    assert!(add < table && sub < table, "{text}");
    assert!(!text.contains(&format!("{RDATA:#x}")), "{text}");
}

/// A function named as the C library names one gets no prototype from
/// its ABI facts: the library's own declaration, `void _exit(int)`, would
/// contradict `extern uint32_t _exit(uint64_t);`.
#[test]
fn a_c_library_name_gets_no_abi_prototype() {
    let mut p = image();
    p.symbols[1].name = "_exit".to_owned();
    let a = Analysis::compute(&p);
    let text = decompile(&p, &a, &Overlay::default(), TEXT).expect("decompiles");
    assert!(text.contains("_exit("), "{text}");
    assert!(
        !text
            .lines()
            .any(|l| l.starts_with("extern ") && l.contains("_exit(")),
        "{text}"
    );
}
