//! The class a parameter or register carries, from callers, callees and names.

use super::*;

#[test]
fn a_callgraph_walks_callers_as_well_as_callees() {
    let p = fixture();
    let a = Analysis::compute(&p);
    let leaf = a
        .functions
        .iter()
        .find(|f| !f.callers.is_empty() && !f.callees.is_empty())
        .expect("a fixture function with both a caller and a callee");
    let o = Overlay::default();
    let up = borer_engine::analysis::render::callgraph_mermaid(&p, &a, &o, leaf.entry, 30, true);
    let down = borer_engine::analysis::render::callgraph_mermaid(&p, &a, &o, leaf.entry, 30, false);
    assert!(up.contains("callers of the root"), "{up}");
    assert!(down.contains("callees of the root"), "{down}");
    let caller = name_of(&a, &o, leaf.callers[0]);
    assert!(
        up.contains(caller.as_str()),
        "the caller is missing from the reverse graph:\n{up}"
    );
    assert!(up.contains(" --> "), "no edges drawn:\n{up}");
}

/// A dynamic frame does not inflate the parameter list.
///
/// A function that sizes its frame at runtime (`sub rsp, rax` after
/// `__chkstk`) hides how big the frame is, so a read of `[rsp+0x800]` is a
/// local, not the 256th stack argument. Counting it as one gave functions
/// like this thirty-odd phantom parameters; now the count declines when the
/// frame is unknown.
#[test]
fn a_dynamic_frame_does_not_invent_parameters() {
    let mut bytes = vec![0xccu8; 0x1000];
    let code = [
        0x48u8, 0x29, 0xc4, 0x8b, 0x84, 0x24, 0x00, 0x08, 0x00, 0x00, 0x31, 0xc0, 0xc3,
    ];
    bytes[0x40..0x40 + code.len()].copy_from_slice(&code);
    let mut p = Program::raw(
        bytes,
        Arch::X86_64,
        0,
        Some(0x1040),
        vec![Section::mapped(".text", 0x1000, 0, 0x1000, false, true)],
    );
    p.function_ranges = vec![(0x1040, 0x104d)];
    let text = decompiled(&p, 0x1040);
    let sig = text
        .lines()
        .find(|l| l.starts_with("// signature:"))
        .unwrap_or_default();
    let params = if sig.contains("()") {
        0
    } else {
        sig.matches(',').count() + 1
    };
    assert!(
        params <= 2,
        "a dynamic frame invented {params} parameters: {sig}"
    );
}

/// The width callers read of a result is recorded on the callee.
///
/// `BL`'s only caller `CW` tests `al`, so it returns a byte; `Q`'s callers
/// read `eax` and wider, and its bare `ret` writes nothing narrower.
#[test]
fn callers_read_width_is_recorded_on_the_callee() {
    let a = Analysis::compute(&fixture());
    assert_eq!(a.function(0x1f30).and_then(|f| f.ret_width), Some(8));
    let q = a.function(0x11e0).and_then(|f| f.ret_width);
    assert!(q.is_none(), "{q:?}");
}

/// A summary lists the imports its function calls straight through the slot.
#[test]
fn summary_callees_name_a_directly_called_import() {
    let p = fixture();
    let a = Analysis::compute(&p);
    let out = borer_engine::analysis::render::function_summary(&p, &a, &Overlay::default(), 0x1230)
        .expect("summary");
    assert!(out.contains("KERNEL32.dll!ReportAssertFailure"), "{out}");
}

/// `NR` has no name; `Y3` calls it with `Z3` starting right after the call, so
/// it is discovered to never return, and `W3` (walked earlier) is re-walked and
/// loses its dead tail.
#[test]
fn discovered_noreturn_callee_cuts_every_caller() {
    let a = Analysis::compute(&fixture());
    let y3 = a.function(0x12c0).unwrap();
    assert_eq!(y3.end, 0x12ca, "Y3 absorbed Z3: {y3:?}");
    let w3 = a.function(0x12d0).unwrap();
    assert_eq!(w3.end, 0x12da, "W3 kept its dead tail: {w3:?}");
    assert_eq!(w3.instr_count, 2);
    assert_eq!(a.function(0x12b0).unwrap().callers, vec![0x12c0, 0x12d0]);
}

/// A method passing its own `this` to an undeclared function types that
/// function's parameter.
///
/// `Der::Tick` calls `HT` with `this`, so `HT`'s first parameter is hinted
/// `Der` and `HT` counts as a method of `Der`; a slot of `Der`'s table (`DV`)
/// and one of `Base`'s (`Q`) are hinted their table's class; `HU2`, two
/// calls away from `Der::Tick2`, is hinted in the second round.
#[test]
fn callers_hint_the_parameter_class() {
    use borer_engine::analysis::classes::methods_of;
    let p = fixture();
    let a = Analysis::compute(&p);
    let ht = a.function(0x18d0).expect("HT");
    assert_eq!(ht.param_hints.get(&0).map(String::as_str), Some("Der"));
    assert!(methods_of(&a, &Overlay::default(), "Der").contains(&0x18d0));
    let dv = a.function(0x1870).expect("DV");
    assert_eq!(dv.param_hints.get(&0).map(String::as_str), Some("Der"));
    let q = a.function(0x11e0).expect("Q");
    assert_eq!(q.param_hints.get(&0).map(String::as_str), Some("Base"));
    let hu2 = a.function(0x1a40).expect("HU2");
    assert_eq!(hu2.param_hints.get(&0).map(String::as_str), Some("Der"));
}

/// A call result or a field passed as another method's `this` is typed.
///
/// `Der::Poll` passes `GT`'s result and its field at 0x10 to `Base::Base`,
/// so `GT` returns a `Base *` and `Der`'s field at 0x10 is a `Base *`, which
/// the layout shows; `Der::Chk`'s guarded assert names the field at 8
/// `count`.
#[test]
fn call_results_and_fields_are_typed_by_their_use() {
    use borer_engine::analysis::classes::{class_layout, render_layout};
    let p = fixture();
    let a = Analysis::compute(&p);
    let gt = a.function(0x18e0).expect("GT");
    assert_eq!(gt.ret_hint.as_deref(), Some("Base"));
    assert_eq!(
        a.classes
            .field_hints
            .get(&("Der".to_owned(), 0x10))
            .map(String::as_str),
        Some("Base")
    );
    assert_eq!(
        a.classes
            .field_types
            .get(&("Der".to_owned(), 0x28))
            .map(String::as_str),
        Some("Core::Ptr<Der>")
    );
    let o = Overlay::default();
    let layout = class_layout(&p, &a, &o, "Der").expect("layout");
    let text = render_layout(&layout, &a, &o);
    assert!(text.contains("+0x10   Base *"), "{text}");
    assert!(text.contains("+0x28   Core::Ptr<Der>"), "{text}");
    assert!(text.contains("+0x8    u32 count"), "{text}");
}

/// A call through the deleting destructor's slot with `1` alone reads as
/// `delete` whatever class the receiver is known to have.
///
/// Thirty-two classes `Ci`, each with a constructor `Ci::Ci` storing its
/// table (`lea rax, [table]; mov [rcx], rax; ret`) and a destructor
/// `Ci::~Ci` in slot 0, make slot 0 the program's deleting destructor.
/// `C0::Kill`, slot 1 of `C0`'s table, is `mov rax, [rcx]; mov edx, 1;
/// call [rax]; ret`: its `this` is a `C0`, so the slot resolves to
/// `C0::~C0`, and the call is still the `delete(this)` it reads as on an
/// object of unknown class, never `this->~C0(1)`.
#[test]
fn a_typed_deleting_destructor_call_reads_as_delete() {
    /// Classes holding a destructor in slot 0.
    const CLASSES: u64 = 32;
    let (text, table) = (0x1000_u64, 0x3000_u64);
    let mut bytes = vec![0xccu8; 0x3000];
    let mut symbols = Vec::new();
    let mut put = |va: u64, code: &[u8]| {
        let at = usize::try_from(va - text).expect("in .text");
        bytes[at..at + code.len()].copy_from_slice(code);
    };
    for i in 0..CLASSES {
        let ctor = text + i * 0x20;
        let vt = table + i * 0x18;
        let disp = i32::try_from(vt - (ctor + 7)).expect("near").to_le_bytes();
        put(
            ctor,
            &[
                0x48, 0x8d, 0x05, disp[0], disp[1], disp[2], disp[3], // ASM: lea rax, [table]
                0x48, 0x89, 0x01, // ASM: mov [rcx], rax
                0xc3, // ASM: ret
            ],
        );
        put(ctor + 0x10, &[0xc3]); // ASM: ret
        symbols.push((format!("C{i}::C{i}"), ctor));
        symbols.push((format!("C{i}::~C{i}"), ctor + 0x10));
    }
    put(0x1900, &[0xc3]); // ASM: ret
    put(
        0x1800,
        &[
            0x48, 0x8b, 0x01, // ASM: mov rax, [rcx]
            0xba, 0x01, 0x00, 0x00, 0x00, // ASM: mov edx, 1
            0xff, 0x10, // ASM: call [rax]
            0xc3, // ASM: ret
        ],
    );
    symbols.push(("C0::Kill".to_owned(), 0x1800));
    for i in 0..CLASSES {
        let at = usize::try_from(table - text + i * 0x18).expect("in .rdata");
        bytes[at..at + 8].copy_from_slice(&(text + i * 0x20 + 0x10).to_le_bytes());
        let second: u64 = if i == 0 { 0x1800 } else { 0x1900 };
        bytes[at + 8..at + 16].copy_from_slice(&second.to_le_bytes());
        bytes[at + 16..at + 24].copy_from_slice(&0_u64.to_le_bytes());
    }
    let mut p = Program::raw(
        bytes,
        Arch::X86_64,
        0,
        Some(0x1800),
        vec![
            Section::mapped(".text", 0x1000, 0, 0x2000, false, true),
            Section::mapped(".rdata", 0x3000, 0x2000, 0x1000, false, false),
        ],
    );
    p.symbols = symbols
        .into_iter()
        .map(|(name, addr)| Symbol {
            name,
            addr,
            kind: SymbolKind::Export,
        })
        .collect();
    let out = decompiled(&p, 0x1800);
    assert!(out.contains("C0 *this"), "{out}");
    assert!(out.contains("delete(this)"), "{out}");
}

/// A method tail-jumping to an undeclared function with its own `this` in
/// the argument register types that function's parameter, as a call does,
/// when the function reads it.
///
/// `Cls::Go` is `test rdx, rdx; jne T2; push rbx; mov rbx, rcx; mov rcx,
/// rbx; pop rbx; jmp T1`: both jumps hand `this` on unchanged, so `T1` and
/// `T2`, exported without a class and reached by nothing else, take `Cls`
/// for their first parameter. `Cls::Make` is `jmp T3`, and `T3` writes
/// `ecx` before it reads it: what `rcx` held is no argument of its.
#[test]
fn a_tail_jump_hints_the_callee_parameter_class() {
    let mut bytes = vec![0xccu8; 0x2000];
    let code = [
        0x48, 0x85, 0xd2, // ASM: test rdx, rdx
        0x75, 0x5b, // ASM: jne 0x1060
        0x53, // ASM: push rbx
        0x48, 0x8b, 0xd9, // ASM: mov rbx, rcx
        0x48, 0x8b, 0xcb, // ASM: mov rcx, rbx
        0x5b, // ASM: pop rbx
        0xe9, 0x2e, 0x00, 0x00, 0x00, // ASM: jmp 0x1040
    ];
    bytes[0x1000..0x1000 + code.len()].copy_from_slice(&code);
    bytes[0x1040..0x1044].copy_from_slice(&[
        0x8b, 0x41, 0x08, // ASM: mov eax, [rcx+8]
        0xc3, // ASM: ret
    ]);
    bytes[0x1060..0x1064].copy_from_slice(&[
        0x8b, 0x41, 0x10, // ASM: mov eax, [rcx+0x10]
        0xc3, // ASM: ret
    ]);
    bytes[0x10a0..0x10a5].copy_from_slice(&[0xe9, 0x1b, 0x00, 0x00, 0x00]); // ASM: jmp 0x10c0
    bytes[0x10c0..0x10c8].copy_from_slice(&[
        0xb9, 0x05, 0x00, 0x00, 0x00, // ASM: mov ecx, 5
        0x89, 0xc8, // ASM: mov eax, ecx
        0xc3, // ASM: ret
    ]);
    let mut p = Program::raw(
        bytes,
        Arch::X86_64,
        0,
        Some(0x1000),
        vec![Section::mapped(
            ".text", 0x1000, 0x1000, 0x1000, false, true,
        )],
    );
    p.symbols = [
        ("Cls::Go", 0x1000),
        ("t1", 0x1040),
        ("t2", 0x1060),
        ("Cls::Make", 0x10a0),
        ("t3", 0x10c0),
    ]
    .map(|(name, addr)| Symbol {
        name: name.to_owned(),
        addr,
        kind: SymbolKind::Export,
    })
    .to_vec();
    let a = Analysis::compute(&p);
    for target in [0x1040, 0x1060] {
        let f = a.function(target).expect("the tail callee is a function");
        assert_eq!(
            f.param_hints.get(&0).map(String::as_str),
            Some("Cls"),
            "{target:#x}"
        );
    }
    let t3 = a
        .function(0x10c0)
        .expect("the third tail callee is a function");
    assert!(t3.param_hints.is_empty(), "{:?}", t3.param_hints);
}

/// A thunk that hands its argument on to a function reading it reads it
/// too, so a tail jump into the thunk types the thunk's parameter.
///
/// `Cls::Go` is `jmp T1`, `T1` is `jmp T2` and `T2` reads `[rcx+8]`: the
/// `this` of `Cls::Go` reaches `T2` through `T1`, and both are `Cls`.
#[test]
fn a_thunk_handing_its_argument_on_reads_it() {
    let go: &[u8] = &[0xe9, 0x1b, 0x00, 0x00, 0x00]; // ASM: jmp 0x1020
    let t1: &[u8] = &[0xe9, 0x1b, 0x00, 0x00, 0x00]; // ASM: jmp 0x1040
    let t2: &[u8] = &[
        0x8b, 0x41, 0x08, // ASM: mov eax, [rcx+8]
        0xc3, // ASM: ret
    ];
    let p = raw_classes(
        &[(0x1000, go), (0x1020, t1), (0x1040, t2)],
        &[],
        &[("Cls::Go", 0x1000), ("t1", 0x1020), ("t2", 0x1040)],
    );
    let a = Analysis::compute(&p);
    for e in [0x1020, 0x1040] {
        let f = a.function(e).expect("a thunk");
        assert_eq!(
            f.param_hints.get(&0).map(String::as_str),
            Some("Cls"),
            "{e:#x}"
        );
    }
}

/// A callee using a parameter as the pointer a key-value pair starts with
/// leaves it the pair its single caller hands on.
///
/// As above, but the caller's class is `Util::KeyValuePair<Core::Ptr<Obj>,int>`
/// and `F` hands the parameter to `Core::Ptr<Obj>::Get`: the pair and its
/// key are one object seen at two depths, so the pair stands.
#[test]
fn a_use_of_a_pair_s_key_leaves_the_pair() {
    let go: &[u8] = &[
        0x48, 0x89, 0xca, // ASM: mov rdx, rcx
        0x48, 0x83, 0xec, 0x28, // ASM: sub rsp, 0x28
        0xe8, 0xf4, 0x00, 0x00, 0x00, // ASM: call 0x1100
        0x48, 0x83, 0xc4, 0x28, // ASM: add rsp, 0x28
        0xc3, // ASM: ret
    ];
    let c: &[u8] = &[
        0x48, 0x83, 0xec, 0x28, // ASM: sub rsp, 0x28
        0xe8, 0xf7, 0x00, 0x00, 0x00, // ASM: call 0x1200
        0x48, 0x83, 0xc4, 0x28, // ASM: add rsp, 0x28
        0xc3, // ASM: ret
    ];
    let f: &[u8] = &[
        0x48, 0x83, 0xec, 0x28, // ASM: sub rsp, 0x28
        0x48, 0x89, 0xd1, // ASM: mov rcx, rdx
        0xe8, 0xf4, 0x00, 0x00, 0x00, // ASM: call 0x1300
        0x48, 0x83, 0xc4, 0x28, // ASM: add rsp, 0x28
        0xc3, // ASM: ret
    ];
    let get: &[u8] = &[
        0x48, 0x8b, 0x01, // ASM: mov rax, [rcx]
        0xc3, // ASM: ret
    ];
    let pair = "Util::KeyValuePair<Core::Ptr<Obj>,int>";
    let go_name = format!("{pair}::Go");
    let p = raw_classes(
        &[(0x1000, go), (0x1100, c), (0x1200, f), (0x1300, get)],
        &[],
        &[
            (go_name.as_str(), 0x1000),
            ("c", 0x1100),
            ("f", 0x1200),
            ("Core::Ptr<Obj>::Get", 0x1300),
        ],
    );
    let a = Analysis::compute(&p);
    let f = a.function(0x1200).expect("F");
    assert_eq!(f.param_hints.get(&1).map(String::as_str), Some(pair));
}

/// A function reads an argument register only on a path from its entry
/// that has not set it.
///
/// `Base::Go` calls `F` and `G` with its `this` in `rcx`. `F` sets `ecx`
/// and jumps back to code laid out before its entry that reads `[rcx+8]`:
/// it never reads the `this` it was handed, so it is no `Base`. `G` loads
/// `rcx` from `[rcx+8]`, reading it as it writes it: it is a `Base`.
#[test]
fn a_register_set_before_its_read_on_the_path_is_no_argument() {
    let base_ctor: &[u8] = &[
        0x48, 0x8d, 0x05, 0xf9, 0x0f, 0x00, 0x00, // ASM: lea rax, [0x2000]
        0x48, 0x89, 0x01, // ASM: mov [rcx], rax
        0xc3, // ASM: ret
    ];
    let go: &[u8] = &[
        0x53, // ASM: push rbx
        0x48, 0x8b, 0xd9, // ASM: mov rbx, rcx
        0xe8, 0x37, 0x01, 0x00, 0x00, // ASM: call 0x1240
        0x48, 0x8b, 0xcb, // ASM: mov rcx, rbx
        0xe8, 0x6f, 0x01, 0x00, 0x00, // ASM: call 0x1280
        0x5b, // ASM: pop rbx
        0xc3, // ASM: ret
    ];
    let shared: &[u8] = &[
        0x8b, 0x41, 0x08, // ASM: mov eax, [rcx+8]
        0xc3, // ASM: ret
    ];
    let f: &[u8] = &[
        0xb9, 0x10, 0x00, 0x00, 0x00, // ASM: mov ecx, 0x10
        0xe9, 0xb6, 0xff, 0xff, 0xff, // ASM: jmp 0x1200
    ];
    let g: &[u8] = &[
        0x48, 0x8b, 0x49, 0x08, // ASM: mov rcx, [rcx+8]
        0x8b, 0x01, // ASM: mov eax, [rcx]
        0xc3, // ASM: ret
    ];
    let p = raw_classes(
        &[
            (0x1000, base_ctor),
            (0x1100, go),
            (0x1180, &[0xc3]),
            (0x1200, shared),
            (0x1240, f),
            (0x1280, g),
        ],
        &[(0x2000, &[0x1180, 0x1180])],
        &[
            ("Base::Base", 0x1000),
            ("Base::Go", 0x1100),
            ("f", 0x1240),
            ("g", 0x1280),
        ],
    );
    let a = Analysis::compute(&p);
    let f = a.function(0x1240).expect("F");
    assert_eq!(f.param_hints.get(&0), None);
    let g = a.function(0x1280).expect("G");
    assert_eq!(g.param_hints.get(&0).map(String::as_str), Some("Base"));
}

/// Code laid out before a function's entry hands its callees nothing: the
/// function reaches it with registers it set itself.
///
/// `Base::Go` calls `F` with its `this` in `rcx`. `F` sets `ecx` and jumps
/// back to code laid out before its entry that calls `Obj::Use`, which
/// reads `[rcx+8]`: `F` hands on no `this`, so it is no `Base`.
#[test]
fn code_before_the_entry_hands_its_callees_nothing() {
    let base_ctor: &[u8] = &[
        0x48, 0x8d, 0x05, 0xf9, 0x0f, 0x00, 0x00, // ASM: lea rax, [0x2000]
        0x48, 0x89, 0x01, // ASM: mov [rcx], rax
        0xc3, // ASM: ret
    ];
    let go: &[u8] = &[
        0x48, 0x83, 0xec, 0x28, // ASM: sub rsp, 0x28
        0xe8, 0x37, 0x01, 0x00, 0x00, // ASM: call 0x1240
        0x48, 0x83, 0xc4, 0x28, // ASM: add rsp, 0x28
        0xc3, // ASM: ret
    ];
    let shared: &[u8] = &[
        0xe8, 0xfb, 0x00, 0x00, 0x00, // ASM: call 0x1300
        0xc3, // ASM: ret
    ];
    let f: &[u8] = &[
        0xb9, 0x10, 0x00, 0x00, 0x00, // ASM: mov ecx, 0x10
        0xe9, 0xb6, 0xff, 0xff, 0xff, // ASM: jmp 0x1200
    ];
    let used: &[u8] = &[
        0x8b, 0x41, 0x08, // ASM: mov eax, [rcx+8]
        0xc3, // ASM: ret
    ];
    let p = raw_classes(
        &[
            (0x1000, base_ctor),
            (0x1100, go),
            (0x1180, &[0xc3]),
            (0x1200, shared),
            (0x1240, f),
            (0x1300, used),
        ],
        &[(0x2000, &[0x1180, 0x1180])],
        &[
            ("Base::Base", 0x1000),
            ("Base::Go", 0x1100),
            ("f", 0x1240),
            ("Obj::Use", 0x1300),
        ],
    );
    let a = Analysis::compute(&p);
    let f = a.function(0x1240).expect("F");
    assert_eq!(f.param_hints.get(&0), None);
}

/// A 32-bit method hands its `this` on in `ecx`, by a call or a tail jump,
/// to a callee that reads it; one that never reads `ecx`, or only pushes
/// it to make room on the stack, takes nothing.
///
/// `Base::Go` (`push esi; mov esi, ecx; call F; mov ecx, esi; call G; pop
/// esi; ret`) calls `F`, which reads `[ecx+4]`, and `G`, which reads only
/// `[esp+4]`. `Base::Jmp` jumps to `T`, which reads `[ecx+8]`.
/// `Base::Go2` calls `P`, which pushes `ecx` as MSVC reserves a word of
/// frame and reads it no other way. `F` and `T` are `Base`; `G` and `P`
/// have no class.
#[test]
fn a_32_bit_this_reaches_the_callees_reading_ecx() {
    let ctor: &[u8] = &[
        0xc7, 0x01, 0x00, 0x20, 0x00, 0x00, // ASM: mov dword [ecx], 0x2000
        0xc3, // ASM: ret
    ];
    let go: &[u8] = &[
        0x56, // ASM: push esi
        0x8b, 0xf1, // ASM: mov esi, ecx
        0xe8, 0xf8, 0x00, 0x00, 0x00, // ASM: call 0x1200
        0x8b, 0xce, // ASM: mov ecx, esi
        0xe8, 0x11, 0x01, 0x00, 0x00, // ASM: call 0x1220
        0x5e, // ASM: pop esi
        0xc3, // ASM: ret
    ];
    let f: &[u8] = &[
        0x8b, 0x41, 0x04, // ASM: mov eax, [ecx+4]
        0xc3, // ASM: ret
    ];
    let g: &[u8] = &[
        0x8b, 0x44, 0x24, 0x04, // ASM: mov eax, [esp+4]
        0xc3, // ASM: ret
    ];
    let jmp: &[u8] = &[0xe9, 0x1b, 0x00, 0x00, 0x00]; // ASM: jmp 0x1260
    let t: &[u8] = &[
        0x8b, 0x41, 0x08, // ASM: mov eax, [ecx+8]
        0xc3, // ASM: ret
    ];
    let go2: &[u8] = &[
        0xe8, 0x1b, 0x00, 0x00, 0x00, // ASM: call 0x12a0
        0xc3, // ASM: ret
    ];
    let room: &[u8] = &[
        0x51, // ASM: push ecx
        0xc7, 0x04, 0x24, 0x00, 0x00, 0x00, 0x00, // ASM: mov dword [esp], 0
        0x58, // ASM: pop eax
        0xc3, // ASM: ret
    ];
    let mut bytes = vec![0xccu8; 0x2000];
    for (va, piece) in [
        (0x1000, ctor),
        (0x1100, go),
        (0x1180, &[0xc3][..]),
        (0x1200, f),
        (0x1220, g),
        (0x1240, jmp),
        (0x1260, t),
        (0x1280, go2),
        (0x12a0, room),
    ] {
        let at = borer_engine::num::saturating_usize(va - 0x1000);
        bytes[at..at + piece.len()].copy_from_slice(piece);
    }
    for (k, slot) in [0x1180u32, 0x1180].into_iter().enumerate() {
        bytes[0x1000 + 4 * k..0x1000 + 4 * k + 4].copy_from_slice(&slot.to_le_bytes());
    }
    let mut p = Program::raw(
        bytes,
        Arch::X86,
        0,
        Some(0x1000),
        vec![
            Section::mapped(".text", 0x1000, 0, 0x1000, false, true),
            Section::mapped(".rdata", 0x2000, 0x1000, 0x1000, false, false),
        ],
    );
    p.symbols = [
        ("Base::Base", 0x1000),
        ("Base::Go", 0x1100),
        ("f", 0x1200),
        ("g", 0x1220),
        ("Base::Jmp", 0x1240),
        ("t", 0x1260),
        ("Base::Go2", 0x1280),
        ("p", 0x12a0),
    ]
    .into_iter()
    .map(|(name, addr)| Symbol {
        name: name.to_owned(),
        addr,
        kind: SymbolKind::Export,
    })
    .collect();
    let a = Analysis::compute(&p);
    let class = |e: u64| a.function(e).and_then(|f| f.param_hints.get(&0).cloned());
    assert_eq!(class(0x1200).as_deref(), Some("Base"));
    assert_eq!(class(0x1260).as_deref(), Some("Base"));
    assert_eq!(class(0x1220), None);
    assert_eq!(class(0x12a0), None);
}

/// A 32-bit method its name gives no class prints the class its `this`
/// was typed as.
///
/// `Base::Base` stores `Base`'s table; `Base::Go` calls `F` with its `this`
/// in `ecx`, and `F` reads `[ecx+4]`: `F` prints as taking a `Base *this`.
#[test]
fn a_32_bit_method_prints_the_class_of_its_this() {
    let ctor: &[u8] = &[
        0xc7, 0x01, 0x00, 0x20, 0x00, 0x00, // ASM: mov dword [ecx], 0x2000
        0xc3, // ASM: ret
    ];
    let go: &[u8] = &[
        0xe8, 0xfb, 0x00, 0x00, 0x00, // ASM: call 0x1200
        0xc3, // ASM: ret
    ];
    let f: &[u8] = &[
        0x8b, 0x41, 0x04, // ASM: mov eax, [ecx+4]
        0xc3, // ASM: ret
    ];
    let mut bytes = vec![0xccu8; 0x2000];
    for (va, piece) in [
        (0x1000, ctor),
        (0x1100, go),
        (0x1180, &[0xc3][..]),
        (0x1200, f),
    ] {
        let at = borer_engine::num::saturating_usize(va - 0x1000);
        bytes[at..at + piece.len()].copy_from_slice(piece);
    }
    for (k, slot) in [0x1180u32, 0x1180].into_iter().enumerate() {
        bytes[0x1000 + 4 * k..0x1000 + 4 * k + 4].copy_from_slice(&slot.to_le_bytes());
    }
    let mut p = Program::raw(
        bytes,
        Arch::X86,
        0,
        Some(0x1000),
        vec![
            Section::mapped(".text", 0x1000, 0, 0x1000, false, true),
            Section::mapped(".rdata", 0x2000, 0x1000, 0x1000, false, false),
        ],
    );
    p.symbols = [("Base::Base", 0x1000), ("Base::Go", 0x1100), ("f", 0x1200)]
        .into_iter()
        .map(|(name, addr)| Symbol {
            name: name.to_owned(),
            addr,
            kind: SymbolKind::Export,
        })
        .collect();
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let text =
        borer_engine::analysis::decompile::decompile(&p, &a, &o, 0x1200).expect("decompiles");
    assert!(text.contains("(Base *this)"), "{text}");
}

/// A variadic function's variable arguments are not typed slots: what one
/// caller hands there types nothing, and hands nothing back to a caller
/// passing a register on.
///
/// `L` homes `rdx`, `r8` and `r9` and takes `rdx`'s home for `va_start`
/// (`mov [rsp+0x10], rdx; mov [rsp+0x18], r8; mov [rsp+0x20], r9; sub rsp,
/// 0x28; lea r8, [rsp+0x38]; call X; add rsp, 0x28; ret`): one fixed
/// argument, then the list. `Cls::Go` calls it with `this` in `rcx` and in
/// `r8` (`mov r8, rcx; call L; ret`); `T` is `xor ecx, ecx; jmp L`, leaving
/// `r8` as its caller set it. `L`'s fixed argument is a `Cls`, its third
/// slot nothing, and `T` takes no class from it.
#[test]
fn a_variadic_callee_types_only_its_fixed_arguments() {
    let mut bytes = vec![0xccu8; 0x2000];
    let mut put = |va: usize, code: &[u8]| bytes[va..va + code.len()].copy_from_slice(code);
    put(
        0x1000,
        &[
            0x4c, 0x8b, 0xc1, // ASM: mov r8, rcx
            0xe8, 0xf8, 0x00, 0x00, 0x00, // ASM: call 0x1100
            0xc3, // ASM: ret
        ],
    );
    put(
        0x1040,
        &[
            0x31, 0xc9, // ASM: xor ecx, ecx
            0xe9, 0xb9, 0x00, 0x00, 0x00, // ASM: jmp 0x1100
        ],
    );
    put(
        0x1100,
        &[
            0x48, 0x89, 0x54, 0x24, 0x10, // ASM: mov [rsp+0x10], rdx
            0x4c, 0x89, 0x44, 0x24, 0x18, // ASM: mov [rsp+0x18], r8
            0x4c, 0x89, 0x4c, 0x24, 0x20, // ASM: mov [rsp+0x20], r9
            0x48, 0x83, 0xec, 0x28, // ASM: sub rsp, 0x28
            0x4c, 0x8d, 0x44, 0x24, 0x38, // ASM: lea r8, [rsp+0x38]
            0xe8, 0xe3, 0x00, 0x00, 0x00, // ASM: call 0x1200
            0x48, 0x83, 0xc4, 0x28, // ASM: add rsp, 0x28
            0xc3, // ASM: ret
        ],
    );
    put(0x1200, &[0xc3]); // ASM: ret
    let mut p = Program::raw(
        bytes,
        Arch::X86_64,
        0,
        Some(0x1000),
        vec![Section::mapped(
            ".text", 0x1000, 0x1000, 0x1000, false, true,
        )],
    );
    p.symbols = [
        ("Cls::Go", 0x1000),
        ("t", 0x1040),
        ("l", 0x1100),
        ("x", 0x1200),
    ]
    .map(|(name, addr)| Symbol {
        name: name.to_owned(),
        addr,
        kind: SymbolKind::Export,
    })
    .to_vec();
    let a = Analysis::compute(&p);
    let hints = |e: u64| a.function(e).expect("a function").param_hints.clone();
    assert_eq!(
        hints(0x1100),
        BTreeMap::from([(0, "Cls".to_owned())]),
        "the fixed argument only"
    );
    assert!(hints(0x1040).is_empty(), "{:?}", hints(0x1040));
}

/// A field's address passed to an undeclared function types that
/// function's parameter with the field's embedded type.
///
/// `Der::Pass` passes the address of its `Core::Ptr<Der>` field at 0x28 to
/// `UP`, so `UP`'s first parameter points at a `Core::Ptr<Der>`.
#[test]
fn field_addresses_type_the_callee_parameter() {
    let a = Analysis::compute(&fixture());
    assert_eq!(
        a.function(0x1118).and_then(|f| f.name.as_deref()),
        Some("Der::Pass")
    );
    let up = a.function(0x12f0).expect("UP");
    assert_eq!(
        up.param_hints.get(&0).map(String::as_str),
        Some("Core::Ptr<Der>")
    );
}
