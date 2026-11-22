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

/// A called function over the size a caller reads through the memo is
/// rendered once in a whole export.
///
/// Its caller's declaration of it comes from the text the export writes,
/// kept once, and states the head the file defines it under.
#[test]
fn a_large_callee_is_rendered_once_for_its_caller_and_the_file() {
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
    let file = exported_file(&p, &a, &Overlay::default(), None);
    assert_eq!(a.derived.held("export_named"), 1, "{file}");
    let large = TEXT + 0x10;
    let head = file
        .lines()
        .find(|l| {
            l.contains(&format!("sub_{large:x}(")) && !l.ends_with(';') && !l.starts_with("//")
        })
        .unwrap_or_else(|| panic!("the large function is defined: {file}"));
    assert!(
        file.lines().any(|l| l.trim() == format!("extern {head};")),
        "{head} in {file}"
    );
}
