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
use borer_engine::analysis::protos::{Proto, Var, VarKey, slot_words};
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
    let (before, _) = decompiled(&p, &plain, 0x401_000);
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
    assert!(before.contains("local_8"), "{before}");
    let mut o = Overlay::default();
    let mut vars = BTreeMap::new();
    vars.insert(
        VarKey::parse("local_8", 8, 8).expect("a slot"),
        Var::parse("wchar_t *path").expect("a declaration"),
    );
    o.vars.insert(0x401_000, vars);
    let mut callee = BTreeMap::new();
    callee.insert(
        VarKey::parse("a1", 8, 0).expect("a parameter"),
        Var::parse("cell").expect("a name"),
    );
    o.vars.insert(0x401_040, callee);
    let (text, header) = decompiled(&p, &o, 0x401_000);
    assert!(!text.contains("local_8"), "{text}");
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

/// A stack slot is stated by the name its text shows, on every
/// instruction set and convention.
///
/// [`slot_words`] gives the distances a function's text numbers its slots
/// by; the name parses to a slot by them and spells back from it, and the
/// decompilation then declares that slot by the stated name. On arm64,
/// ARM32 and RISC-V the slot `N` bytes above the entry stack pointer reads
/// `arg_N`, with no return address below it: read by x86's rule, `arg_8`
/// named the slot those texts call `arg_10`.
#[test]
fn a_slot_is_stated_by_the_name_its_text_shows() {
    let words = |ws: &[u32]| -> Vec<u8> { ws.iter().flat_map(|w| w.to_le_bytes()).collect() };
    let arm64 = words(&[
        0xf940_07e0, // ASM: ldr x0, [sp, #8]
        0xd65f_03c0, // ASM: ret
    ]);
    let cases: [(Arch, BinaryFormat, Vec<u8>, &str); 8] = [
        (
            Arch::X86,
            BinaryFormat::Pe,
            vec![
                0x8d, 0x44, 0x24, 0xf8, // ASM: lea eax, [esp-8]
                0xc3, // ASM: ret
            ],
            "local_4",
        ),
        (
            Arch::X86_64,
            BinaryFormat::Elf,
            vec![
                0x48, 0x8d, 0x44, 0x24, 0xf0, // ASM: lea rax, [rsp-0x10]
                0xc3, // ASM: ret
            ],
            "local_8",
        ),
        (
            Arch::X86_64,
            BinaryFormat::Pe,
            vec![
                0x48, 0x8b, 0x44, 0x24, 0x08, // ASM: mov rax, [rsp+8]
                0xc3, // ASM: ret
            ],
            "home_0",
        ),
        (Arch::Arm64, BinaryFormat::Elf, arm64.clone(), "arg_8"),
        (Arch::Arm64, BinaryFormat::Pe, arm64, "arg_8"),
        (
            Arch::Arm,
            BinaryFormat::Elf,
            words(&[
                0xe28d_0004, // ASM: add r0, sp, #4
                0xe12f_ff1e, // ASM: bx lr
            ]),
            "arg_4",
        ),
        (
            Arch::RiscV64,
            BinaryFormat::Elf,
            words(&[
                0x0081_3503, // ASM: ld a0, 8(sp)
                0x0000_8067, // ASM: ret
            ]),
            "arg_8",
        ),
        (
            Arch::RiscV32,
            BinaryFormat::Elf,
            words(&[
                0x0041_2503, // ASM: lw a0, 4(sp)
                0x0000_8067, // ASM: ret
            ]),
            "arg_4",
        ),
    ];
    for (arch, format, code, shown) in cases {
        let size = u64::try_from(code.len()).expect("a few bytes");
        let text = Section::mapped(".text", 0x1000, 0, size, false, true);
        let mut p = Program::raw(code, arch, 0, Some(0x1000), vec![text]);
        p.format = format;
        let a = Analysis::compute(&p);
        let before = decompile(&p, &a, &Overlay::default(), 0x1000).unwrap_or_default();
        let declared = before
            .lines()
            .find_map(|l| l.strip_suffix(&format!(" {shown};")))
            .unwrap_or_default();
        assert!(
            !declared.is_empty(),
            "{arch:?} {format:?} declares no {shown}: {before}"
        );
        let (word, shadow, frame) = slot_words(&p, 0x1000);
        let key = VarKey::parse(shown, word, frame).expect("a slot");
        assert_eq!(key.spell(word, shadow, frame), shown, "{arch:?} {format:?}");
        let mut o = Overlay::default();
        let var = Var::parse("kept").expect("a name");
        o.vars.insert(0x1000, BTreeMap::from([(key, var)]));
        let after = decompile(&p, &a, &o, 0x1000).unwrap_or_default();
        assert!(
            after.contains(&format!("\n{declared} kept;\n")) && !after.contains(shown),
            "{arch:?} {format:?}: {after}"
        );
    }
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
    let first = decompile(&p, &a, &plain, 0x401_000);
    let stated = decompile(&p, &a, &o, 0x401_000);
    assert_ne!(first, stated);
    assert_eq!(decompile(&p, &a, &o, 0x401_000), stated);
    assert_eq!(decompile(&p, &a, &plain, 0x401_000), first);
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

/// A layout recovered through a pointer parameter, applied, makes the
/// re-decompiled text name the fields read through it.
///
/// The plan defines `Rec` from the accesses (a dword at 0x10, a qword at
/// 0x18, a byte at 0x20) and states the signature the text already prints
/// with `a1` typed `Rec *`; the body then reads `a1->f_10`, the text stays
/// fully checked, and the caller's call is unchanged. A spec that starts
/// inside the function, or names a register no access goes through, is
/// refused rather than typing the wrong value.
#[test]
fn an_applied_layout_names_the_fields_read_through_its_pointer() {
    use borer_engine::analysis::apply::from_pointer;
    let mut code = vec![
        0x8b, 0x41, 0x10, // ASM: mov eax, [rcx+0x10]
        0x48, 0x03, 0x41, 0x18, // ASM: add rax, [rcx+0x18]
        0xc6, 0x41, 0x20, 0x01, // ASM: mov byte [rcx+0x20], 1
        0xc3, // ASM: ret
    ];
    code.resize(0x20, 0xcc);
    code.extend_from_slice(&[
        0x48, 0x8d, 0x0d, 0xd9, 0x0f, 0x00, 0x00, // ASM: lea rcx, [rip+0xfd9]
        0xe8, 0xd4, 0xff, 0xff, 0xff, // ASM: call 0x401000
        0xc3, // ASM: ret
    ]);
    let p = image(&code);
    let a = Analysis::compute(&p);
    let plain = Overlay::default();
    let (before, _) = decompiled(&p, &plain, 0x401_000);
    assert!(before.contains("sub_401000(void *a1)"), "{before}");
    assert!(before.contains("a1->field_0x10"), "{before}");
    let (caller_before, _) = decompiled(&p, &plain, 0x401_020);
    let plan = from_pointer(&p, &a, &plain, "0x401000,rcx", "Rec").expect("a plan");
    assert_eq!(
        plan.describe(&a, &plain),
        [
            "struct Rec (0x21 bytes): 0x10 f_10 u32, 0x18 f_18 u64, 0x20 f_20 u8",
            "prototype sub_401000 (0x401000): uint64_t (Rec *)",
        ]
    );
    let mut o = plain.clone();
    plan.apply(&mut o);
    let (after, header) = decompiled(&p, &o, 0x401_000);
    assert!(
        after.contains("// signature: uint64_t sub_401000(Rec *a1)"),
        "{after}"
    );
    assert!(after.contains("a1->f_10"), "{after}");
    assert!(after.contains("a1->f_18"), "{after}");
    assert!(after.contains("a1->f_20 = 1;"), "{after}");
    assert!(fully_checked(&header), "{header}");
    let (caller_after, _) = decompiled(&p, &o, 0x401_020);
    let body = |t: &str| {
        t.lines()
            .filter(|l| !l.starts_with("//"))
            .collect::<Vec<_>>()
            .join("\n")
    };
    assert_eq!(body(&caller_after), body(&caller_before));
    let inside = from_pointer(&p, &a, &plain, "0x401003,rcx", "Rec").expect_err("mid-function");
    assert!(inside.contains("carries no parameter"), "{inside}");
    let unused = from_pointer(&p, &a, &plain, "0x401000,rdx", "Rec").expect_err("no access");
    assert!(unused.contains("no struct to apply"), "{unused}");
}

/// A prototype or a declaration whose spelling passes the length a text is
/// read from is refused as it is parsed, as its spelling would be when the
/// saved project loads.
///
/// Read within the cap, both spelled past it, so the save succeeded and the
/// next load refused the whole file.
#[test]
fn a_spelling_past_the_cap_is_refused_as_it_is_parsed() {
    let proto = format!("{}int({})", "const ".repeat(10_900), ["int"; 32].join(","));
    let refused = Proto::parse(&proto).expect_err("a prototype spelled past the cap");
    assert!(
        refused.to_string().contains("a prototype as spelled is"),
        "{refused}"
    );
    let var = format!("{}TT*x", "const ".repeat(10_922));
    let refused = Var::parse(&var).expect_err("a declaration spelled past the cap");
    assert!(
        refused.to_string().contains("a declaration as spelled is"),
        "{refused}"
    );
}

/// A stack slot past the span of a frame is refused as it is stated, as its
/// saved key would be when the project loads.
#[test]
fn a_slot_past_the_frame_span_is_refused() {
    for far in ["arg_10000", "local_fffffffffffffff"] {
        let refused = VarKey::parse(far, 8, 8).expect_err("a slot past the span");
        assert!(
            refused.to_string().contains("bytes from the frame"),
            "{refused}"
        );
    }
    assert!(VarKey::parse("arg_ff00", 8, 8).is_ok());
}
