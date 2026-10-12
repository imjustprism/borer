//! Prototypes and variables an agent states, in the decompiler.
//!
//! A stated prototype feeds the path debug information feeds: the
//! signature, the parameters' names and types, the fields read through a
//! typed pointer, and the arity and result every call shows. Where the
//! binary contradicts it, the text says so and the check against the
//! binary makes no claim for what the text then leaves out.

#![expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]

use std::collections::BTreeMap;

use borer_engine::analysis::decompile::{checked_header, decompile};
use borer_engine::analysis::protos::{Proto, Var, VarKey};
use borer_engine::analysis::utypes::{TypeExpr, build_struct};
use borer_engine::analysis::{Analysis, Overlay};
use borer_engine::program::{Arch, BinaryFormat, Program, Section};

/// Builds a 64-bit PE-shaped image with `code` at 0x401000.
///
/// # Arguments
///
/// * `code` - The bytes of `.text`.
fn image(code: &[u8]) -> Program {
    let mut bytes = vec![0u8; 0x1000];
    bytes[..code.len()].copy_from_slice(code);
    let mut p = Program::raw(
        bytes,
        Arch::X86_64,
        0x400_000,
        Some(0x401_000),
        vec![Section::mapped(".text", 0x401_000, 0, 0x1000, false, true)],
    );
    p.format = BinaryFormat::Pe;
    p
}

/// An overlay stating `decl` for the function at `entry`; one that does
/// not parse states nothing, which the tests' assertions then show.
///
/// # Arguments
///
/// * `entry` - The function.
/// * `decl` - The prototype, as C.
fn stating(entry: u64, decl: &str) -> Overlay {
    let mut o = Overlay::default();
    if let Ok(p) = Proto::parse(decl) {
        o.prototypes.insert(entry, p);
    }
    o
}

/// The text and the checked header of one function under an overlay.
///
/// # Arguments
///
/// * `p` - The image.
/// * `o` - The overlay.
/// * `entry` - The function.
fn decompiled(p: &Program, o: &Overlay, entry: u64) -> (String, String) {
    let a = Analysis::compute(p);
    (
        decompile(p, &a, o, entry).unwrap_or_default(),
        checked_header(p, &a, o, entry).unwrap_or_default(),
    )
}

/// Tells whether a checked header counts every block of the function as
/// checked, with no disagreement.
///
/// # Arguments
///
/// * `header` - The `// checked vs binary:` line.
fn fully_checked(header: &str) -> bool {
    let counts = header
        .split("emitted, ")
        .nth(1)
        .and_then(|r| r.split(' ').next())
        .and_then(|c| c.split_once('/'));
    matches!(counts, Some((a, b)) if a == b) && !header.contains("disagree")
}

/// Two callers of `sub_401020`, which returns in `rax` and leaves 7 in
/// `rdx`: the first reads `rdx` after the call, the second only `rax`.
fn pair() -> Program {
    let mut code = vec![
        0xb9, 0x05, 0x00, 0x00, 0x00, // ASM: mov ecx, 5
        0xe8, 0x16, 0x00, 0x00, 0x00, // ASM: call 0x401020
        0x48, 0x89, 0xd0, // ASM: mov rax, rdx
        0xc3, // ASM: ret
    ];
    code.resize(0x20, 0xcc);
    code.extend_from_slice(&[
        0x48, 0x8d, 0x41, 0x01, // ASM: lea rax, [rcx+1]
        0xba, 0x07, 0x00, 0x00, 0x00, // ASM: mov edx, 7
        0xc3, // ASM: ret
    ]);
    code.resize(0x40, 0xcc);
    code.extend_from_slice(&[
        0xb9, 0x03, 0x00, 0x00, 0x00, // ASM: mov ecx, 3
        0xe8, 0xd6, 0xff, 0xff, 0xff, // ASM: call 0x401020
        0x48, 0x83, 0xc0, 0x01, // ASM: add rax, 1
        0xc3, // ASM: ret
    ]);
    image(&code)
}

/// A stated `int f(int)` removes the speculative second result.
///
/// A caller that reads only `rax` loses its `__rdx` line and stays fully
/// checked; the caller that does read `rdx` says the declaration is
/// contradicted, and the callee's own header says what contradicts it.
#[test]
fn a_stated_prototype_rules_out_a_second_result() {
    let p = pair();
    let plain = Overlay::default();
    let (before, _) = decompiled(&p, &plain, 0x401_040);
    assert!(before.contains("sub_401020__rdx"), "{before}");
    let o = stating(0x401_020, "int f(int n)");
    let (after, header) = decompiled(&p, &o, 0x401_040);
    assert!(!after.contains("__rdx"), "{after}");
    assert!(after.contains("sub_401020(3)"), "{after}");
    assert!(fully_checked(&header), "{header}");
    assert!(!header.contains("contradicted"), "{header}");
    let (reader, header) = decompiled(&p, &o, 0x401_000);
    assert!(!reader.contains("__rdx"), "{reader}");
    assert!(header.contains("declaration contradicted"), "{header}");
    let (callee, _) = decompiled(&p, &o, 0x401_020);
    assert!(
        callee.contains("// signature: int sub_401020(int n)"),
        "{callee}"
    );
    assert!(callee.contains("return n + 1;"), "{callee}");
    assert!(
        callee.contains("// stated prototype contradicted: a caller reads rdx after the call"),
        "{callee}"
    );
}

/// A prototype stating fewer parameters than the body reads makes every
/// call following it leave arguments out, so the caller's block is not
/// counted as checked, and the callee's header names the gap.
#[test]
fn a_prototype_short_of_what_the_body_reads_is_contradicted() {
    let mut code = vec![
        0xb9, 0x05, 0x00, 0x00, 0x00, // ASM: mov ecx, 5
        0xba, 0x06, 0x00, 0x00, 0x00, // ASM: mov edx, 6
        0xe8, 0x11, 0x00, 0x00, 0x00, // ASM: call 0x401020
        0xc3, // ASM: ret
    ];
    code.resize(0x20, 0xcc);
    code.extend_from_slice(&[
        0x8d, 0x04, 0x11, // ASM: lea eax, [rcx+rdx]
        0xc3, // ASM: ret
    ]);
    let p = image(&code);
    let o = stating(0x401_020, "int add(int a)");
    let (caller, header) = decompiled(&p, &o, 0x401_000);
    assert!(caller.contains("sub_401020(5)"), "{caller}");
    assert!(header.contains("declaration contradicted"), "{header}");
    let (callee, _) = decompiled(&p, &o, 0x401_020);
    assert!(
        callee.contains("the body reads 2 parameter position(s), the prototype states 1"),
        "{callee}"
    );
}

/// A pointer parameter typed with a user struct names the fields read
/// through it.
#[test]
fn a_typed_pointer_parameter_names_its_fields() {
    let code = [
        0x8b, 0x41, 0x10, // ASM: mov eax, [rcx+0x10]
        0x48, 0x03, 0x41, 0x18, // ASM: add rax, [rcx+0x18]
        0xc3, // ASM: ret
    ];
    let p = image(&code);
    let mut o = stating(0x401_000, "uint64_t score(Player *p)");
    let player = build_struct(
        "Player",
        None,
        &[
            (0x10, "hp".to_owned(), TypeExpr::U32),
            (
                0x18,
                "name".to_owned(),
                TypeExpr::Ptr(Box::new(TypeExpr::Char)),
            ),
        ],
        &o.types,
        8,
    )
    .expect("the struct builds");
    o.types.insert("Player".to_owned(), player);
    let (text, _) = decompiled(&p, &o, 0x401_000);
    assert!(
        text.contains("// signature: uint64_t sub_401000(Player *p)"),
        "{text}"
    );
    assert!(text.contains("p->hp"), "{text}");
    assert!(text.contains("p->name"), "{text}");
}

/// A stated variable renames every use of its slot and declares it of the
/// stated type; a stated parameter renames it in the signature and body.
#[test]
fn a_stated_variable_renames_every_use() {
    let mut code = vec![
        0x48, 0x83, 0xec, 0x38, // ASM: sub rsp, 0x38
        0x48, 0xc7, 0x44, 0x24, 0x28, 0x05, 0x00, 0x00, 0x00, // ASM: mov qword [rsp+0x28], 5
        0x48, 0x8d, 0x4c, 0x24, 0x28, // ASM: lea rcx, [rsp+0x28]
        0xe8, 0x29, 0x00, 0x00, 0x00, // ASM: call 0x401040
        0x48, 0x8b, 0x44, 0x24, 0x28, // ASM: mov rax, [rsp+0x28]
        0x48, 0x83, 0xc4, 0x38, // ASM: add rsp, 0x38
        0xc3, // ASM: ret
    ];
    code.resize(0x40, 0xcc);
    code.extend_from_slice(&[
        0x48, 0x8b, 0x01, // ASM: mov rax, [rcx]
        0xc3, // ASM: ret
    ]);
    let p = image(&code);
    let (before, _) = decompiled(&p, &Overlay::default(), 0x401_000);
    assert!(before.contains("local_10"), "{before}");
    let mut o = Overlay::default();
    let mut vars = BTreeMap::new();
    vars.insert(
        VarKey::parse("local_10", 8).expect("a slot"),
        Var::parse("wchar_t *path").expect("a declaration"),
    );
    o.vars.insert(0x401_000, vars);
    let mut callee = BTreeMap::new();
    callee.insert(
        VarKey::parse("a1", 8).expect("a parameter"),
        Var::parse("cell").expect("a name"),
    );
    o.vars.insert(0x401_040, callee);
    let (text, header) = decompiled(&p, &o, 0x401_000);
    assert!(!text.contains("local_10"), "{text}");
    assert!(text.contains("&path"), "{text}");
    assert!(text.contains("wchar_t *path;"), "{text}");
    assert!(fully_checked(&header), "{header}");
    let (callee_text, _) = decompiled(&p, &o, 0x401_040);
    assert!(
        callee_text.contains("sub_401040(uint64_t *cell)"),
        "{callee_text}"
    );
    assert!(
        callee_text.contains("return *(uint64_t*)cell;"),
        "{callee_text}"
    );
}

/// A prototype or a variable changes the overlay's fingerprint, so no
/// text read under another overlay is handed back; the same overlay twice
/// gives the same text.
#[test]
fn stated_annotations_key_the_memo() {
    let p = pair();
    let a = Analysis::compute(&p);
    let plain = Overlay::default();
    let o = stating(0x401_020, "int f(int n)");
    assert_ne!(plain.fingerprint(), o.fingerprint());
    let mut renamed = o.clone();
    let mut vars = BTreeMap::new();
    vars.insert(VarKey::Param(0), Var::parse("count").expect("a name"));
    renamed.vars.insert(0x401_020, vars);
    assert_ne!(o.fingerprint(), renamed.fingerprint());
    let first = decompile(&p, &a, &plain, 0x401_040);
    let stated = decompile(&p, &a, &o, 0x401_040);
    assert_ne!(first, stated);
    assert_eq!(decompile(&p, &a, &o, 0x401_040), stated);
    assert_eq!(decompile(&p, &a, &plain, 0x401_040), first);
}

/// A `void` prototype on a function whose caller reads its result leaves
/// the callee's returns bare, which the check does not count as agreeing,
/// and the header says a caller reads a result.
#[test]
fn a_void_prototype_whose_result_is_read_is_contradicted() {
    let p = pair();
    let o = stating(0x401_020, "void f(int n)");
    let (callee, header) = decompiled(&p, &o, 0x401_020);
    assert!(
        callee.contains("// signature: void sub_401020(int n)"),
        "{callee}"
    );
    assert!(callee.contains("a caller reads a result"), "{callee}");
    assert!(header.contains("declaration contradicted"), "{header}");
    let (caller, header) = decompiled(&p, &o, 0x401_040);
    assert!(caller.contains("sub_401020(3);"), "{caller}");
    assert!(header.contains("declaration contradicted"), "{header}");
}
