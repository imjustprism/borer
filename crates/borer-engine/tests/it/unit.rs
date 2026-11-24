//! The translation-unit closure: a decompiled function declares every
//! function it calls and every table of functions it indexes, so its text
//! compiles on its own.
#![expect(
    clippy::missing_panics_doc,
    clippy::expect_used,
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

/// Two exports of one binary are the same bytes, whatever order the cores
/// finish their functions in.
#[test]
fn the_export_is_deterministic() {
    use borer_engine::analysis::decompile::export::{Library, export};
    let p = image();
    let file = || {
        let a = Analysis::compute(&p);
        let mut bodies = String::new();
        let hoisted = export(
            &p,
            &a,
            &Overlay::default(),
            Library::Include,
            None,
            &mut |t| {
                bodies.push_str(t);
                Ok(())
            },
        )
        .expect("exports");
        format!("{}{bodies}", hoisted.head("t"))
    };
    assert_eq!(file(), file());
}

/// The whole-binary export defines every function once.
///
/// It hoists what the per-function closures declare: the table of
/// operations once, after the prototypes of the functions it names, and
/// no `static inline` copy of a function the file defines. The walk from
/// `even`, the first entry, writes its callee `odd` before it.
#[test]
fn the_export_hoists_the_closure_and_defines_each_function_once() {
    use borer_engine::analysis::decompile::export::{Library, export};
    let p = image();
    let a = Analysis::compute(&p);
    let mut bodies = String::new();
    let hoisted = export(&p, &a, &Overlay::default(), Library::Skip, None, &mut |t| {
        bodies.push_str(t);
        Ok(())
    })
    .expect("exports");
    let file = format!("{}{bodies}", hoisted.head("t"));
    let lines: Vec<&str> = file.lines().collect();
    let def = |name: &str| {
        let at: Vec<usize> = lines
            .iter()
            .enumerate()
            .filter(|(_, l)| {
                !l.ends_with(';') && !l.starts_with("//") && l.contains(&format!(" {name}("))
            })
            .map(|(i, _)| i)
            .collect();
        assert_eq!(at.len(), 1, "{name} is defined once: {file}");
        at[0]
    };
    for name in ["even", "odd", "dispatch", "op_add", "op_sub"] {
        def(name);
    }
    assert!(!file.contains("static inline uint32_t op_"), "{file}");
    let table = lines
        .iter()
        .position(|l| l.ends_with("= {op_add, op_sub, op_add, op_sub};"))
        .unwrap_or_else(|| panic!("the table is declared: {file}"));
    assert_eq!(file.matches("= {op_add, op_sub").count(), 1, "{file}");
    let proto = lines
        .iter()
        .position(|l| l.ends_with(';') && l.contains(" op_add("))
        .unwrap_or_else(|| panic!("op_add is declared: {file}"));
    assert!(proto < table && table < def("op_add"), "{file}");
    assert!(
        def("odd") < def("even"),
        "even's callee comes first: {file}"
    );
    assert_eq!(hoisted.written, 5, "{file}");
}

/// An export limited to one entry writes that body and not the others.
///
/// The body matches the whole-binary export. A callee the function still
/// names stays a prototype, because the closure hoists it.
///
/// # Panics
///
/// When the limited export writes another body, or `even` differs.
#[test]
fn an_export_of_one_entry_writes_only_that_body() {
    use std::collections::BTreeSet;

    use borer_engine::analysis::decompile::export::{Library, export};
    let p = image();
    let a = Analysis::compute(&p);
    let file = |only: Option<&BTreeSet<u64>>| {
        let mut bodies = String::new();
        let hoisted = export(
            &p,
            &a,
            &Overlay::default(),
            Library::Skip,
            only,
            &mut |text| {
                bodies.push_str(text);
                Ok(())
            },
        )
        .expect("exports");
        assert_eq!(hoisted.left_out, 0, "the limit is not a library skip");
        format!("{}{bodies}", hoisted.head("t"))
    };
    let defines = |text: &str, name: &str| {
        text.lines().any(|line| {
            !line.ends_with(';') && !line.starts_with("//") && line.contains(&format!(" {name}("))
        })
    };
    let body = |text: &str| {
        let lines: Vec<&str> = text.lines().collect();
        let start = lines
            .iter()
            .position(|line| line.contains(" even(") && !line.ends_with(';'))
            .expect("even");
        let end = lines
            .iter()
            .skip(start)
            .position(|line| *line == "}")
            .expect("the end of even");
        lines[start..=start + end].join("\n")
    };
    let all = file(None);
    let one = file(Some(&BTreeSet::from([TEXT])));
    assert!(defines(&one, "even"), "{one}");
    assert!(!defines(&one, "odd"), "{one}");
    assert!(!defines(&one, "dispatch"), "{one}");
    assert_eq!(body(&one), body(&all));
    assert!(
        one.lines()
            .any(|line| line.contains(" odd(") && line.ends_with(';')),
        "odd stays declared: {one}"
    );
}

/// An exported body declares the function it calls by that function's
/// own signature, the one the file writes it under, and keeps the
/// declaration inside the definition so it compiles alone.
#[test]
fn an_exported_body_declares_its_callee_by_its_own_signature() {
    use std::collections::BTreeSet;

    use borer_engine::analysis::decompile::export::{Library, export};
    let p = image();
    let a = Analysis::compute(&p);
    let file = |only: Option<&BTreeSet<u64>>| {
        let mut bodies = String::new();
        let hoisted = export(
            &p,
            &a,
            &Overlay::default(),
            Library::Skip,
            only,
            &mut |text| {
                bodies.push_str(text);
                Ok(())
            },
        )
        .expect("exports");
        format!("{}{bodies}", hoisted.head("t"))
    };
    let all = file(None);
    let odd = all
        .lines()
        .find(|l| l.contains(" odd(") && !l.ends_with(';') && !l.starts_with("//"))
        .expect("odd is defined");
    let one = file(Some(&BTreeSet::from([TEXT])));
    assert!(
        one.lines().any(|l| l == format!("  extern {odd};")),
        "{odd} in {one}"
    );
}

/// Microsoft x64 routines at [`TEXT`] that name what their units leave
/// undeclared, with `counter` a data symbol at [`RDATA`]:
///
/// ```text
/// tail()       : tail-calls twice(7)                 at +0x00
/// twice(n)     : n + n                               at +0x20
/// counter_at() : &counter                            at +0x30
/// store(p, v)  : *p = v, returning nothing           at +0x40
/// bump(p, v)   : store(p, v) + 1, reading eax after  at +0x50
/// counter_read(): counter, read as 32 bits           at +0x60
/// ```
const NAMED: [(usize, &[u8]); 10] = [
    (0x00, &[0xb9, 0x07, 0x00, 0x00, 0x00]), // ASM: mov ecx, 7 (tail)
    (0x05, &[0xe9, 0x16, 0x00, 0x00, 0x00]), // ASM: jmp twice
    (0x20, &[0x8d, 0x04, 0x09, 0xc3]),       // ASM: lea eax, [rcx + rcx]; ret (twice)
    (0x30, &[0x48, 0x8d, 0x05, 0xc9, 0x0f, 0x00, 0x00]), // ASM: lea rax, [rip + 0xfc9] (counter_at)
    (0x37, &[0xc3]),                         // ASM: ret
    (0x40, &[0x89, 0x11, 0xc3]),             // ASM: mov [rcx], edx; ret (store)
    (0x50, &[0x48, 0x83, 0xec, 0x28]),       // ASM: sub rsp, 0x28 (bump)
    (0x54, &[0xe8, 0xe7, 0xff, 0xff, 0xff]), // ASM: call store
    (0x59, &[0x48, 0x83, 0xc4, 0x28, 0xff, 0xc0, 0xc3]), // ASM: add rsp, 0x28; inc eax; ret
    (0x60, &[0x8b, 0x05, 0x9a, 0x0f, 0x00, 0x00, 0xc3]), // ASM: mov eax, [rip + 0xf9a]; ret (counter_read)
];

/// [`NAMED`] as a PE-like image, every routine and `counter` named.
fn named_image() -> Program {
    let mut code = vec![0xccu8; 0x80];
    for (at, bytes) in NAMED {
        code[at..at + bytes.len()].copy_from_slice(bytes);
    }
    let mut p = crate::raw::image(Arch::X86_64, &code, &[0u8; 16]);
    p.format = BinaryFormat::Pe;
    let named = |name: &str, addr: u64, kind: SymbolKind| Symbol {
        name: name.to_owned(),
        addr,
        kind,
    };
    p.symbols = vec![
        named("tail", TEXT, SymbolKind::Export),
        named("twice", TEXT + 0x20, SymbolKind::Export),
        named("counter_at", TEXT + 0x30, SymbolKind::Export),
        named("store", TEXT + 0x40, SymbolKind::Export),
        named("bump", TEXT + 0x50, SymbolKind::Export),
        named("counter_read", TEXT + 0x60, SymbolKind::Export),
        named("counter", RDATA, SymbolKind::Data),
    ];
    p
}

/// Exports the entries of [`named_image`] in `only` as one file.
///
/// # Arguments
///
/// * `only` - The entries to write.
fn named_export(only: &[u64]) -> String {
    named_export_with(&Overlay::default(), only)
}

/// Exports the entries of [`named_image`] in `only` under an overlay.
///
/// # Arguments
///
/// * `overlay` - Names and prototypes to apply.
/// * `only` - The entries to write.
fn named_export_with(overlay: &Overlay, only: &[u64]) -> String {
    let p = named_image();
    let only = only.iter().copied().collect();
    exported_file(&p, &Analysis::compute(&p), overlay, Some(&only))
}

/// Exports an image as one file, library code included.
///
/// # Arguments
///
/// * `p` - The image.
/// * `a` - Its analysis.
/// * `overlay` - Names and prototypes to apply.
/// * `only` - The entries to write, `None` for every one.
fn exported_file(
    p: &Program,
    a: &Analysis,
    overlay: &Overlay,
    only: Option<&std::collections::BTreeSet<u64>>,
) -> String {
    use borer_engine::analysis::decompile::export::{Library, export};
    let mut bodies = String::new();
    let hoisted = export(p, a, overlay, Library::Include, only, &mut |t| {
        bodies.push_str(t);
        Ok(())
    })
    .expect("exports");
    format!("{}{bodies}", hoisted.head("t"))
}

/// Returns the file-scope and block-scope lines that declare `name`.
///
/// Each ends `;`, a comment after it allowed, names it and is no
/// statement.
///
/// # Arguments
///
/// * `file` - The exported file.
/// * `name` - The name.
fn declarations_of(file: &str, name: &str) -> Vec<String> {
    file.lines()
        .map(str::trim)
        .filter(|l| {
            let code = l.split(" //").next().unwrap_or(l);
            !l.starts_with("//")
                && code.ends_with(';')
                && !code.starts_with("return ")
                && !code.contains(" = ")
                && code
                    .split(|c: char| !c.is_ascii_alphanumeric() && c != '_')
                    .any(|w| w == name)
        })
        .map(str::to_owned)
        .collect()
}

/// A function exported alone declares the callee it tail-calls by that
/// callee's own signature, though the file does not define it, and the
/// declaration is stated one way only.
#[test]
fn an_export_of_one_entry_declares_its_tail_callee() {
    let file = named_export(&[TEXT]);
    assert!(file.contains("twice(7)"), "{file}");
    let decls = declarations_of(&file, "twice");
    assert!(!decls.is_empty(), "twice is declared: {file}");
    let mut ways: Vec<&str> = decls
        .iter()
        .map(|d| d.trim_start_matches("extern "))
        .collect();
    ways.dedup();
    assert_eq!(ways.len(), 1, "one way: {decls:?} in {file}");
    let whole = named_export(&[TEXT, TEXT + 0x20]);
    let head = whole
        .lines()
        .find(|l| l.contains(" twice(") && !l.ends_with(';') && !l.starts_with("//"))
        .unwrap_or_else(|| panic!("twice is defined: {whole}"));
    assert_eq!(ways, [format!("{head};")], "its own signature: {file}");
}

/// A function the C implementation's names reserve (`__twice`, as
/// MinGW's `__main`) gets no declaration from its own signature when the
/// text names it undeclared.
#[test]
fn an_implementation_named_tail_callee_gets_no_declaration() {
    let mut p = named_image();
    p.symbols[1].name = "__twice".to_owned();
    let only = std::collections::BTreeSet::from([TEXT]);
    let file = exported_file(&p, &Analysis::compute(&p), &Overlay::default(), Some(&only));
    assert!(file.contains("__twice(7)"), "{file}");
    assert!(declarations_of(&file, "__twice").is_empty(), "{file}");
}

/// A data symbol one function names by its address is not declared by
/// the export, since the file would hoist that declaration above a
/// function that reads the name itself.
#[test]
fn a_data_symbol_named_by_address_gets_no_declaration() {
    let file = named_export(&[TEXT + 0x30, TEXT + 0x60]);
    assert!(file.contains("&counter"), "{file}");
    assert!(
        !file.contains("uint8_t counter[]"),
        "no bytes-at declaration: {file}"
    );
}

/// A callee stated variadic is declared by that signature, and one the
/// caller contradicts is declared by its own and told.
///
/// The variable list takes the arguments past the fixed ones. Where the
/// caller is stated to return another type than the callee it passes on,
/// the body says the two disagree.
#[test]
fn a_variadic_or_contradicted_callee_is_declared() {
    use borer_engine::analysis::protos::Proto;
    let stated = |entry: u64, decl: &str| {
        let mut o = Overlay::default();
        o.prototypes
            .insert(entry, Proto::parse(decl).expect("a prototype"));
        named_export_with(&o, &[TEXT])
    };
    let file = stated(TEXT + 0x20, "uint32_t twice(uint32_t n, ...)");
    assert!(
        declarations_of(&file, "twice")
            .iter()
            .any(|d| d.ends_with("twice(uint32_t n, ...);")),
        "{file}"
    );
    let file = stated(TEXT, "uint64_t tail(void)");
    let decls = declarations_of(&file, "twice");
    assert!(!decls.is_empty(), "twice is declared: {file}");
    assert!(
        decls.iter().all(|d| d.contains("uint32_t twice(")),
        "{file}"
    );
    assert!(
        file.contains("// warn: twice: the text returns its result as another type"),
        "{file}"
    );
}

/// The whole file declares every name once at file scope.
#[test]
fn the_whole_export_states_each_declaration_once() {
    let file = named_export(&[TEXT, TEXT + 0x20, TEXT + 0x30, TEXT + 0x40, TEXT + 0x50]);
    for name in ["tail", "twice", "counter_at", "store", "bump"] {
        let file_scope: Vec<&str> = file
            .lines()
            .filter(|l| !l.starts_with(' ') && !l.starts_with("//"))
            .filter(|l| l.ends_with(';') || l.contains("; //"))
            .filter(|l| l.contains(&format!(" {name}(")) || l.contains(&format!(" {name}[")))
            .collect();
        assert_eq!(file_scope.len(), 1, "{name}: {file_scope:?} in {file}");
    }
}

/// A called function over the size a caller reads through the memo keeps
/// its ABI prototype in an export of its caller alone.
///
/// Its signature is not read, so that export decompiles no large callee
/// only for one line.
#[test]
fn a_large_callee_keeps_its_abi_prototype() {
    let mut code = vec![0x48, 0x83, 0xec, 0x28]; // ASM: sub rsp, 0x28 (caller)
    code.extend([0xe8, 0x07, 0x00, 0x00, 0x00]); // ASM: call large
    code.extend([0x48, 0x83, 0xc4, 0x28, 0xc3]); // ASM: add rsp, 0x28; ret
    code.extend([0xcc; 2]);
    for _ in 0..1100 {
        code.extend([0xff, 0xc1]); // ASM: inc ecx (large)
    }
    code.extend([0x89, 0xc8, 0xc3]); // ASM: mov eax, ecx; ret
    let mut p = crate::raw::image(Arch::X86_64, &code, &[]);
    p.format = BinaryFormat::Pe;
    let a = Analysis::compute(&p);
    let only = std::collections::BTreeSet::from([TEXT]);
    let file = exported_file(&p, &a, &Overlay::default(), Some(&only));
    let large = format!("sub_{:x}", TEXT + 0x10);
    let decls = declarations_of(&file, &large);
    assert!(!decls.is_empty(), "{large} is declared: {file}");
    assert!(
        decls.iter().all(|d| !d.contains(" a1")),
        "an ABI prototype names no parameter: {decls:?}"
    );
}

/// A System V x64 routine at [`TEXT`] that sums four fields of the object
/// its first argument points at: the qword at 0, the dword at 8, the byte
/// at 0x10 and the qword at 0x18.
const FIELDS: [&[u8]; 7] = [
    &[0x48, 0x8b, 0x07],       // ASM: mov rax, [rdi]
    &[0x8b, 0x57, 0x08],       // ASM: mov edx, [rdi+8]
    &[0x48, 0x01, 0xd0],       // ASM: add rax, rdx
    &[0x0f, 0xb6, 0x57, 0x10], // ASM: movzx edx, byte [rdi+0x10]
    &[0x48, 0x01, 0xd0],       // ASM: add rax, rdx
    &[0x48, 0x03, 0x47, 0x18], // ASM: add rax, [rdi+0x18]
    &[0xc3],                   // ASM: ret
];

/// An exported definition spells each layout field as its load.
///
/// Its `decompile` text has a layout line, and the definition, as a reader
/// cuts it from its head line to its closing brace, has no member access
/// and names nothing its signature, its own declarations, the C keywords
/// and `<stdint.h>` do not declare.
#[test]
fn an_exported_definition_spells_its_layout_fields_as_loads() {
    let mut p = crate::raw::image(Arch::X86_64, &FIELDS.concat(), &[]);
    p.format = BinaryFormat::Elf;
    p.symbols = vec![Symbol {
        name: "sum".to_owned(),
        addr: TEXT,
        kind: SymbolKind::Export,
    }];
    let a = Analysis::compute(&p);
    let text = decompile(&p, &a, &Overlay::default(), TEXT).expect("decompiles");
    assert!(text.contains("// layout "), "{text}");
    let only = std::collections::BTreeSet::from([TEXT]);
    let file = exported_file(&p, &a, &Overlay::default(), Some(&only));
    let lines: Vec<&str> = file.lines().collect();
    let head = lines
        .iter()
        .position(|l| l.contains(" sum(") && !l.ends_with(';') && !l.starts_with("//"))
        .unwrap_or_else(|| panic!("sum is defined: {file}"));
    let end = head
        + lines[head..]
            .iter()
            .position(|l| *l == "}")
            .expect("the definition ends");
    let body = lines[head..=end].join("\n");
    assert!(!body.contains("->"), "{body}");
    let words = |s: &str| -> Vec<String> {
        s.split(|c: char| !c.is_ascii_alphanumeric() && c != '_')
            .filter(|w| w.starts_with(|c: char| c.is_ascii_alphabetic() || c == '_'))
            .map(str::to_owned)
            .collect()
    };
    let mut known: Vec<String> = words(lines[head]);
    for line in &lines[head + 1..end] {
        let t = line.trim();
        if let Some(decl) = t.strip_suffix(';').filter(|d| !d.contains(['=', '(', '+'])) {
            known.extend(words(decl));
        }
    }
    let c = "return if else while for do switch case default break continue goto void char int unsigned signed long short const uint8_t uint16_t uint32_t uint64_t int8_t int16_t int32_t int64_t uintptr_t";
    known.extend(c.split(' ').map(str::to_owned));
    let unknown: Vec<String> = words(&body)
        .into_iter()
        .filter(|w| !known.contains(w))
        .collect();
    assert!(unknown.is_empty(), "{unknown:?} in {body}");
}

/// A user's comment that reads as a layout line sizes no field of the
/// export: the comment prints in the body, and the field keeps the width
/// the header's layout gives it, the one the text check reads.
#[test]
fn a_comment_reading_as_a_layout_sizes_no_exported_field() {
    let mut p = crate::raw::image(Arch::X86_64, &FIELDS.concat(), &[]);
    p.format = BinaryFormat::Elf;
    let a = Analysis::compute(&p);
    let mut o = Overlay::default();
    o.comments.insert(TEXT + 3, "layout a1: 0x8 u8".to_owned());
    let only = std::collections::BTreeSet::from([TEXT]);
    let file = exported_file(&p, &a, &o, Some(&only));
    assert!(file.contains("// layout a1: 0x8 u8"), "{file}");
    let load = |ty: &str| {
        file.contains(&format!("*({ty}*)(a1 + 8)"))
            || file.contains(&format!("*({ty}*)((uintptr_t)a1 + 8)"))
    };
    assert!(load("uint32_t") && !load("uint8_t"), "{file}");
}

/// A System V x64 routine at [`TEXT`] + 0x40 that reads the dword its
/// argument points at and returns the address 32 bytes past it.
const NEXT: [&[u8]; 3] = [
    &[0x8b, 0x07],             // ASM: mov eax, [rdi]
    &[0x48, 0x8d, 0x47, 0x20], // ASM: lea rax, [rdi+0x20]
    &[0xc3],                   // ASM: ret
];

/// The export takes no sum on a `void *`.
///
/// The export is standard C: no sum is taken on a `void *`, a parameter's
/// or a local's, where the `decompile` view, GNU C, takes one. A name
/// after a cast, `(uintptr_t)obj` or the load `*(uint64_t*)a1`, is no
/// `void *` operand.
#[test]
fn the_export_takes_no_sum_on_a_void_pointer() {
    let mut code = FIELDS.concat();
    code.resize(0x40, 0xcc);
    code.extend(NEXT.concat());
    let mut p = crate::raw::image(Arch::X86_64, &code, &[]);
    p.format = BinaryFormat::Elf;
    let a = Analysis::compute(&p);
    let mut o = Overlay::default();
    let proto =
        borer_engine::analysis::protos::Proto::parse("void *next(void *obj)").expect("parses");
    o.prototypes.insert(TEXT + 0x40, proto);
    let text = decompile(&p, &a, &o, TEXT + 0x40).expect("decompiles");
    assert!(text.contains("return obj + 32;"), "{text}");
    let file = exported_file(&p, &a, &o, None);
    let mut voids: Vec<String> = Vec::new();
    for line in file.lines() {
        for part in line.split(['(', ',']) {
            if let Some(name) = part.trim().strip_prefix("void *") {
                let name = name.trim_end_matches([')', ';', ' ', '{']);
                if !name.is_empty() && name.chars().all(|c| c.is_ascii_alphanumeric() || c == '_') {
                    voids.push(name.to_owned());
                }
            }
        }
    }
    assert!(
        ["a1", "obj"]
            .iter()
            .all(|n| voids.contains(&(*n).to_owned())),
        "{file}"
    );
    for name in &voids {
        for op in [" + ", " - ", " += ", " -= "] {
            let sum = format!("{name}{op}");
            for (at, _) in file.match_indices(&sum) {
                let before = &file[..at];
                let whole = !before.ends_with(|c: char| c.is_ascii_alphanumeric() || c == '_');
                assert!(!whole || before.ends_with(')'), "{sum} in {file}");
            }
        }
    }
}

/// Microsoft x64 code at [`TEXT`] that calls the import at [`RDATA`] with
/// 1 when its argument is zero, and else returns 0.
const CALLS_ON_ZERO: [&[u8]; 7] = [
    &[0x48, 0x83, 0xec, 0x28],             // ASM: sub rsp, 0x28
    &[0x85, 0xc9],                         // ASM: test ecx, ecx
    &[0x75, 0x0b],                         // ASM: jnz +0xb
    &[0xb9, 0x01, 0x00, 0x00, 0x00],       // ASM: mov ecx, 1
    &[0xff, 0x15, 0xed, 0x0f, 0x00, 0x00], // ASM: call [rip+0xfed]
    &[0x31, 0xc0],                         // ASM: xor eax, eax
    &[0x48, 0x83, 0xc4, 0x28, 0xc3],       // ASM: add rsp, 0x28; ret
];

/// Returns a PE image of `code` at [`TEXT`], `f` exported there, with the
/// symbols given beside it.
///
/// # Arguments
///
/// * `code` - The code.
/// * `symbols` - Each further symbol's name, address and kind.
fn image_with(code: &[u8], symbols: &[(&str, u64, SymbolKind)]) -> Program {
    let mut p = crate::raw::image(Arch::X86_64, code, &[0u8; 16]);
    p.format = BinaryFormat::Pe;
    p.symbols = std::iter::once(("f", TEXT, SymbolKind::Export))
        .chain(symbols.iter().copied())
        .map(|(name, addr, kind)| Symbol {
            name: name.to_owned(),
            addr,
            kind,
        })
        .collect();
    p
}

/// Exports `f` of an image under an overlay.
///
/// # Arguments
///
/// * `p` - The image.
/// * `o` - The overlay.
fn exported_f(p: &Program, o: &Overlay) -> String {
    let only = std::collections::BTreeSet::from([TEXT]);
    exported_file(p, &Analysis::compute(p), o, Some(&only))
}

/// Returns `code` with the `mov ecx, 1` at `at` made `mov edi, 1`, the
/// System V call of the same argument.
///
/// # Arguments
///
/// * `code` - Microsoft x64 code.
/// * `at` - The offset of its `mov ecx, 1`.
fn sysv(mut code: Vec<u8>, at: usize) -> Vec<u8> {
    code[at..at + 5].copy_from_slice(&[0xbf, 0x01, 0x00, 0x00, 0x00]); // ASM: mov edi, 1
    code
}

/// Returns an image of [`image_with`] in another format.
///
/// # Arguments
///
/// * `format` - The format.
/// * `code`, `symbols` - As [`image_with`] takes them.
fn image_as(format: BinaryFormat, code: &[u8], symbols: &[(&str, u64, SymbolKind)]) -> Program {
    let mut p = image_with(code, symbols);
    p.format = format;
    p
}

/// The export declares the C runtime's `exit`, which never returns,
/// `_Noreturn`; the `decompile` view, GNU C as it stands, declares it as
/// the library states it.
#[test]
fn an_import_that_never_returns_is_declared_so_in_the_export_alone() {
    let p = image_with(
        &CALLS_ON_ZERO.concat(),
        &[("msvcrt.dll!exit", RDATA, SymbolKind::Import)],
    );
    let file = exported_f(&p, &Overlay::default());
    assert!(
        file.contains("  extern _Noreturn void exit(int status);"),
        "{file}"
    );
    let a = Analysis::compute(&p);
    let text = decompile(&p, &a, &Overlay::default(), TEXT).expect("decompiles");
    assert!(text.contains("\nextern void exit(int status);\n"), "{text}");
}

/// An `exit` another module exports is no C runtime's `exit`: no
/// `_Noreturn`, where the C runtime's is declared so.
#[test]
fn an_exit_of_another_module_is_declared_as_it_returns() {
    let code = CALLS_ON_ZERO.concat();
    let p = image_with(&code, &[("mylib.dll!exit", RDATA, SymbolKind::Import)]);
    let file = exported_f(&p, &Overlay::default());
    assert!(file.contains("  extern void exit(int status);"), "{file}");
    let p = image_with(&code, &[("msvcrt.dll!exit", RDATA, SymbolKind::Import)]);
    let file = exported_f(&p, &Overlay::default());
    assert!(file.contains("extern _Noreturn void exit("), "{file}");
}

/// An `exit` another module exports, called while the C runtime's `exit`
/// is imported too and called by nobody: the name is no one function, so
/// the export claims nothing.
#[test]
fn an_exit_two_modules_export_is_declared_as_it_returns() {
    let p = image_with(
        &CALLS_ON_ZERO.concat(),
        &[
            ("mylib.dll!exit", RDATA, SymbolKind::Import),
            ("msvcrt.dll!exit", RDATA + 8, SymbolKind::Import),
        ],
    );
    let file = exported_f(&p, &Overlay::default());
    assert!(file.contains("exit(1)"), "{file}");
    assert!(!file.contains("_Noreturn"), "{file}");
    let p = image_with(
        &CALLS_ON_ZERO.concat(),
        &[
            ("msvcrt.dll!exit", RDATA, SymbolKind::Import),
            ("msvcrt.dll!abort", RDATA + 8, SymbolKind::Import),
        ],
    );
    let file = exported_f(&p, &Overlay::default());
    assert!(file.contains("extern _Noreturn void exit("), "{file}");
}

/// An `exit` the text demangles from a C++ import, called while the C
/// runtime's `exit` is imported too, is no C `exit`: the name is unsafe,
/// on ELF (`_Z4exiti`) and on PE (`?exit@@YAXH@Z`) alike.
#[test]
fn a_demangled_exit_of_a_cpp_import_is_declared_as_it_returns() {
    let elf = image_as(
        BinaryFormat::Elf,
        &sysv(CALLS_ON_ZERO.concat(), 8),
        &[
            ("_Z4exiti", RDATA, SymbolKind::Import),
            ("exit", RDATA + 8, SymbolKind::Import),
        ],
    );
    let pe = image_with(
        &CALLS_ON_ZERO.concat(),
        &[
            ("mylib.dll!?exit@@YAXH@Z", RDATA, SymbolKind::Import),
            ("msvcrt.dll!exit", RDATA + 8, SymbolKind::Import),
        ],
    );
    for p in [elf, pe] {
        let file = exported_f(&p, &Overlay::default());
        assert!(file.contains("exit(1)"), "{file}");
        assert!(!file.contains("_Noreturn"), "{file}");
    }
}

/// A data symbol the text demangles to `exit` bears the name too: the C
/// runtime's `exit`, called, is declared as it returns.
#[test]
fn a_data_symbol_named_exit_leaves_exit_declared_as_it_returns() {
    let p = image_with(
        &CALLS_ON_ZERO.concat(),
        &[
            ("msvcrt.dll!exit", RDATA, SymbolKind::Import),
            ("_ZL4exit", RDATA + 8, SymbolKind::Local),
        ],
    );
    let file = exported_f(&p, &Overlay::default());
    assert!(file.contains("exit(1)"), "{file}");
    assert!(!file.contains("_Noreturn"), "{file}");
}

/// Microsoft x64 code at [`TEXT`] that calls the function at [`TEXT`] +
/// 0x40 with 1 and returns 0, and at [`TEXT`] + 0x40 an import thunk, `jmp
/// [RDATA]`.
const CALLS_THUNK: [(usize, &[u8]); 5] = [
    (0x00, &[0x48, 0x83, 0xec, 0x28]),       // ASM: sub rsp, 0x28
    (0x04, &[0xb9, 0x01, 0x00, 0x00, 0x00]), // ASM: mov ecx, 1
    (0x09, &[0xe8, 0x32, 0x00, 0x00, 0x00]), // ASM: call +0x32 (TEXT + 0x40)
    (0x0e, &[0x31, 0xc0, 0x48, 0x83, 0xc4, 0x28, 0xc3]), // ASM: xor eax, eax; add rsp, 0x28; ret
    (0x40, &[0xff, 0x25, 0xba, 0x0f, 0x00, 0x00]), // ASM: jmp [rip+0xfba]
];

/// Lays out [`CALLS_THUNK`], the thunk's bytes replaced by `callee`.
///
/// # Arguments
///
/// * `callee` - The bytes at [`TEXT`] + 0x40.
fn calls_thunk(callee: &[u8]) -> Vec<u8> {
    let mut code = vec![0xccu8; 0x48];
    for (at, bytes) in CALLS_THUNK {
        let bytes = if at == 0x40 { callee } else { bytes };
        code[at..at + bytes.len()].copy_from_slice(bytes);
    }
    code
}

/// A thunk to the C runtime's `exit` the user named `exit` is declared as
/// it returns.
///
/// The name the text spells is the user's, not the file's, so the export
/// states nothing it cannot read from the file.
#[test]
fn a_function_the_user_named_exit_is_declared_as_it_returns() {
    let thunk = CALLS_THUNK[4].1;
    let p = image_with(
        &calls_thunk(thunk),
        &[("msvcrt.dll!exit", RDATA, SymbolKind::Import)],
    );
    let mut o = Overlay::default();
    o.names.insert(TEXT + 0x40, "exit".to_owned());
    let file = exported_f(&p, &o);
    assert!(file.contains("  extern void exit(int status);"), "{file}");
    let file = exported_f(&p, &Overlay::default());
    assert!(file.contains("extern _Noreturn void exit("), "{file}");
}

/// A call through a thunk to the C runtime's `exit` declares it
/// `_Noreturn`, on PE and on ELF alike.
#[test]
fn a_thunk_to_exit_is_declared_noreturn() {
    let pe = image_with(
        &calls_thunk(CALLS_THUNK[4].1),
        &[("msvcrt.dll!exit", RDATA, SymbolKind::Import)],
    );
    let file = exported_f(&pe, &Overlay::default());
    assert!(
        file.contains("  extern _Noreturn void exit(int status);"),
        "{file}"
    );
    let code = sysv(calls_thunk(CALLS_THUNK[4].1), 4);
    let elf = image_as(
        BinaryFormat::Elf,
        &code,
        &[("exit", RDATA, SymbolKind::Import)],
    );
    let file = exported_f(&elf, &Overlay::default());
    assert!(
        file.contains("  extern _Noreturn void exit(int status);"),
        "{file}"
    );
}

/// A Mach-O `_exit` and an `exit` of `MSVCR120.dll` are declared
/// `_Noreturn`.
///
/// Mach-O spells a C name with a leading `_`: an `_exit` import is C's
/// `exit`, which the text names `_exit` as the file does and declares as
/// POSIX states `_exit`, `_Noreturn` either way.
#[test]
fn a_macho_or_msvcr_exit_is_declared_noreturn() {
    let code = sysv(calls_thunk(CALLS_THUNK[4].1), 4);
    let macho = image_as(
        BinaryFormat::MachO,
        &code,
        &[("_exit", RDATA, SymbolKind::Import)],
    );
    let file = exported_f(&macho, &Overlay::default());
    assert!(
        file.contains("  extern _Noreturn void _exit(int status);"),
        "{file}"
    );
    let msvcr = image_with(
        &CALLS_ON_ZERO.concat(),
        &[("MSVCR120.dll!exit", RDATA, SymbolKind::Import)],
    );
    let file = exported_f(&msvcr, &Overlay::default());
    assert!(
        file.contains("  extern _Noreturn void exit(int status);"),
        "{file}"
    );
}

/// A name two functions share is declared as it returns.
///
/// The program imports `exit` through a thunk, which `f` calls, and has a
/// returning function of its own named `exit` too: the export claims
/// nothing, where it claims the import's alone.
#[test]
fn a_name_two_functions_share_is_declared_as_it_returns() {
    let mut code = sysv(calls_thunk(CALLS_THUNK[4].1), 4);
    code.resize(0x51, 0xcc);
    code[0x50] = 0xc3; // ASM: ret
    let import = ("exit", RDATA, SymbolKind::Import);
    let own = ("exit", TEXT + 0x50, SymbolKind::Local);
    let file = exported_f(
        &image_as(BinaryFormat::Elf, &code, &[import, own]),
        &Overlay::default(),
    );
    assert!(file.contains("exit(1)"), "{file}");
    assert!(!file.contains("_Noreturn"), "{file}");
    let file = exported_f(
        &image_as(BinaryFormat::Elf, &code, &[import]),
        &Overlay::default(),
    );
    assert!(file.contains("extern _Noreturn void exit("), "{file}");
}

/// A Mach-O import named `exit`, without the `_` every C name has there,
/// is no C `exit`: no `_Noreturn`.
#[test]
fn a_macho_exit_without_the_underscore_is_declared_as_it_returns() {
    let code = sysv(calls_thunk(CALLS_THUNK[4].1), 4);
    let p = image_as(
        BinaryFormat::MachO,
        &code,
        &[("exit", RDATA, SymbolKind::Import)],
    );
    let file = exported_f(&p, &Overlay::default());
    assert!(file.contains("exit(1)"), "{file}");
    assert!(!file.contains("_Noreturn"), "{file}");
}

/// A function no symbol names, which a signature string names `exit`,
/// bears the name as much as a symbol does: the C runtime's `exit`, called
/// through its thunk, is declared as it returns.
#[test]
fn a_function_a_signature_names_exit_leaves_exit_declared_as_it_returns() {
    let mut code = calls_thunk(CALLS_THUNK[4].1);
    code[0x0e..0x18].copy_from_slice(&[0xe8, 0x3d, 0, 0, 0, 0x48, 0x83, 0xc4, 0x28, 0xc3]); // ASM: call +0x3d (TEXT + 0x50); add rsp, 0x28; ret
    code.resize(0x58, 0xcc);
    code[0x50..0x58].copy_from_slice(&[0x48, 0x8d, 0x05, 0xb1, 0x0f, 0, 0, 0xc3]); // ASM: lea rax, [rip+0xfb1] (RDATA + 8); ret
    let data = [&[0u8; 8][..], b"void __cdecl exit(int)\0"].concat();
    let mut p = crate::raw::image(Arch::X86_64, &code, &data);
    p.format = BinaryFormat::Pe;
    p.symbols = vec![
        Symbol {
            name: "f".to_owned(),
            addr: TEXT,
            kind: SymbolKind::Export,
        },
        Symbol {
            name: "msvcrt.dll!exit".to_owned(),
            addr: RDATA,
            kind: SymbolKind::Import,
        },
    ];
    let a = Analysis::compute(&p);
    assert_eq!(
        a.function(TEXT + 0x50).and_then(|f| f.name.as_deref()),
        Some("exit")
    );
    let file = exported_f(&p, &Overlay::default());
    assert!(!file.contains("_Noreturn"), "{file}");
}

/// The binary's own `exit`, a function that returns, is declared as the
/// library states `exit`, without `_Noreturn`. A baseline: the export
/// never flagged the program's own code.
#[test]
fn baseline_the_programs_own_exit_is_declared_as_it_returns() {
    let p = image_with(
        &calls_thunk(&[0xc3]),
        &[("exit", TEXT + 0x40, SymbolKind::Export)],
    );
    let file = exported_f(&p, &Overlay::default());
    assert!(file.contains("  extern void exit(int status);"), "{file}");
}

/// The ELF program's own `_exit`, a function that returns, is declared as
/// POSIX states `_exit`, without `_Noreturn`, where an imported `_exit` is
/// declared so.
#[test]
fn the_programs_own_posix_exit_is_declared_as_it_returns() {
    let own = sysv(calls_thunk(&[0xc3]), 4);
    let p = image_as(
        BinaryFormat::Elf,
        &own,
        &[("_exit", TEXT + 0x40, SymbolKind::Local)],
    );
    let file = exported_f(&p, &Overlay::default());
    assert!(file.contains("extern void _exit(int status);"), "{file}");
    let thunk = sysv(calls_thunk(CALLS_THUNK[4].1), 4);
    let p = image_as(
        BinaryFormat::Elf,
        &thunk,
        &[("_exit", RDATA, SymbolKind::Import)],
    );
    let file = exported_f(&p, &Overlay::default());
    assert!(
        file.contains("extern _Noreturn void _exit(int status);"),
        "{file}"
    );
}

/// An import the table does not name is declared as it returns, whatever
/// its name begins with. A baseline: the export declares no import its
/// library does not state.
#[test]
fn baseline_an_import_the_table_does_not_name_is_declared_as_it_returns() {
    let p = image_with(
        &CALLS_ON_ZERO.concat(),
        &[("msvcrt.dll!exiting", RDATA, SymbolKind::Import)],
    );
    let file = exported_f(&p, &Overlay::default());
    assert!(file.contains("exiting("), "{file}");
    assert!(!file.contains("_Noreturn"), "{file}");
}

/// Microsoft x64 code at [`TEXT`] that calls the import at [`RDATA`] with
/// 0 and traps after it, so its own path ends at the call.
const CALLS_THEN_TRAPS: [&[u8]; 4] = [
    &[0x48, 0x83, 0xec, 0x28],             // ASM: sub rsp, 0x28
    &[0x31, 0xc9],                         // ASM: xor ecx, ecx
    &[0xff, 0x15, 0xf4, 0x0f, 0x00, 0x00], // ASM: call [rip+0xff4]
    &[0xcc],                               // ASM: int3
];

/// A caller whose path ends at a call proves nothing of the callee: the C
/// library's `free`, called before a trap, is declared as it returns. A
/// baseline: no caller's path ever set the flag.
#[test]
fn baseline_a_caller_ending_at_a_call_declares_no_noreturn() {
    let p = image_with(
        &CALLS_THEN_TRAPS.concat(),
        &[("msvcrt.dll!free", RDATA, SymbolKind::Import)],
    );
    let file = exported_f(&p, &Overlay::default());
    assert!(file.contains("free("), "{file}");
    assert!(!file.contains("_Noreturn"), "{file}");
}
