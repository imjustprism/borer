//! How class evidence that disagrees is weighed.

use super::*;

/// A function a class's table holds is a method of that class, whatever a
/// derived class's override hands it.
///
/// `Base::Base` stores `Base`'s table (`M`, `N`) and `Der::Der` calls it
/// before storing `Der`'s (`Der::Foo`, `N`). `Der::Foo` overrides `M` and
/// ends `jmp M`, handing on its `this`, a `Der`: `M` stays a method of
/// `Base`, the class whose table holds it, never `Der`.
#[test]
fn a_derived_override_does_not_narrow_its_base_method() {
    let base_ctor: &[u8] = &[
        0x48, 0x8d, 0x05, 0xf9, 0x0f, 0x00, 0x00, // ASM: lea rax, [0x2000]
        0x48, 0x89, 0x01, // ASM: mov [rcx], rax
        0xc3, // ASM: ret
    ];
    let der_ctor: &[u8] = &[
        0x53, // ASM: push rbx
        0x48, 0x8b, 0xd9, // ASM: mov rbx, rcx
        0xe8, 0xd7, 0xff, 0xff, 0xff, // ASM: call 0x1000
        0x48, 0x8d, 0x05, 0xe0, 0x0f, 0x00, 0x00, // ASM: lea rax, [0x2010]
        0x48, 0x89, 0x03, // ASM: mov [rbx], rax
        0x5b, // ASM: pop rbx
        0xc3, // ASM: ret
    ];
    let m: &[u8] = &[
        0x8b, 0x41, 0x08, // ASM: mov eax, [rcx+8]
        0xc3, // ASM: ret
    ];
    let foo: &[u8] = &[0xe9, 0xbb, 0xff, 0xff, 0xff]; // ASM: jmp 0x1100
    let n: &[u8] = &[0xc3]; // ASM: ret
    let p = raw_classes(
        &[
            (0x1000, base_ctor),
            (0x1020, der_ctor),
            (0x1100, m),
            (0x1140, foo),
            (0x1160, n),
        ],
        &[(0x2000, &[0x1100, 0x1160]), (0x2010, &[0x1140, 0x1160])],
        &[
            ("Base::Base", 0x1000),
            ("Der::Der", 0x1020),
            ("m", 0x1100),
            ("Der::Foo", 0x1140),
            ("n", 0x1160),
        ],
    );
    let a = Analysis::compute(&p);
    assert_eq!(
        a.classes
            .by_name
            .get("Der")
            .and_then(|c| c.parent.as_deref()),
        Some("Base")
    );
    let m = a.function(0x1100).expect("M");
    assert_eq!(m.param_hints.get(&0).map(String::as_str), Some("Base"));
}

/// A parameter no caller types takes the most derived of the classes the
/// callees it is handed to accept, which bound it from above.
///
/// `Der` derives from `Base` as in the test above. `H`, which nothing
/// calls, hands its first parameter to `Base::M` and to `Der::N` (`push rbx;
/// mov rbx, rcx; call M; mov rcx, rbx; call N; pop rbx; ret`): it is a
/// `Der`, not merely the `Base` both accept.
#[test]
fn a_parameter_handed_to_two_callees_is_the_most_derived_they_accept() {
    let base_ctor: &[u8] = &[
        0x48, 0x8d, 0x05, 0xf9, 0x0f, 0x00, 0x00, // ASM: lea rax, [0x2000]
        0x48, 0x89, 0x01, // ASM: mov [rcx], rax
        0xc3, // ASM: ret
    ];
    let der_ctor: &[u8] = &[
        0x53, // ASM: push rbx
        0x48, 0x8b, 0xd9, // ASM: mov rbx, rcx
        0xe8, 0xd7, 0xff, 0xff, 0xff, // ASM: call 0x1000
        0x48, 0x8d, 0x05, 0xe0, 0x0f, 0x00, 0x00, // ASM: lea rax, [0x2010]
        0x48, 0x89, 0x03, // ASM: mov [rbx], rax
        0x5b, // ASM: pop rbx
        0xc3, // ASM: ret
    ];
    let m: &[u8] = &[
        0x8b, 0x41, 0x08, // ASM: mov eax, [rcx+8]
        0xc3, // ASM: ret
    ];
    let n: &[u8] = &[
        0x8b, 0x41, 0x10, // ASM: mov eax, [rcx+0x10]
        0xc3, // ASM: ret
    ];
    let h: &[u8] = &[
        0x53, // ASM: push rbx
        0x48, 0x8b, 0xd9, // ASM: mov rbx, rcx
        0xe8, 0xf7, 0xfe, 0xff, 0xff, // ASM: call 0x1100
        0x48, 0x8b, 0xcb, // ASM: mov rcx, rbx
        0xe8, 0x4f, 0xff, 0xff, 0xff, // ASM: call 0x1160
        0x5b, // ASM: pop rbx
        0xc3, // ASM: ret
    ];
    let p = raw_classes(
        &[
            (0x1000, base_ctor),
            (0x1020, der_ctor),
            (0x1100, m),
            (0x1160, n),
            (0x1180, &[0xc3]),
            (0x1200, h),
        ],
        &[(0x2000, &[0x1100, 0x1180]), (0x2010, &[0x1160, 0x1180])],
        &[
            ("Base::Base", 0x1000),
            ("Der::Der", 0x1020),
            ("Base::M", 0x1100),
            ("Der::N", 0x1160),
            ("h", 0x1200),
        ],
    );
    let a = Analysis::compute(&p);
    let h = a.function(0x1200).expect("H");
    assert_eq!(h.param_hints.get(&0).map(String::as_str), Some("Der"));
}

/// A member's `this` is at least the class its name gives, whatever
/// ancestor its callers only know the object as.
///
/// `Der` derives from `Base` as above. `Base::Call` hands its own `this`, a
/// `Base`, to `Der::Run` (`call Run; ret`), which reads `[rcx+0x10]`: `Run`
/// is `Der`'s method, so its `this` is a `Der`.
#[test]
fn a_member_keeps_the_class_its_name_gives() {
    let base_ctor: &[u8] = &[
        0x48, 0x8d, 0x05, 0xf9, 0x0f, 0x00, 0x00, // ASM: lea rax, [0x2000]
        0x48, 0x89, 0x01, // ASM: mov [rcx], rax
        0xc3, // ASM: ret
    ];
    let der_ctor: &[u8] = &[
        0x53, // ASM: push rbx
        0x48, 0x8b, 0xd9, // ASM: mov rbx, rcx
        0xe8, 0xd7, 0xff, 0xff, 0xff, // ASM: call 0x1000
        0x48, 0x8d, 0x05, 0xe0, 0x0f, 0x00, 0x00, // ASM: lea rax, [0x2010]
        0x48, 0x89, 0x03, // ASM: mov [rbx], rax
        0x5b, // ASM: pop rbx
        0xc3, // ASM: ret
    ];
    let call: &[u8] = &[
        0x48, 0x83, 0xec, 0x28, // ASM: sub rsp, 0x28
        0xe8, 0xf7, 0x00, 0x00, 0x00, // ASM: call 0x1180
        0x48, 0x83, 0xc4, 0x28, // ASM: add rsp, 0x28
        0xc3, // ASM: ret
    ];
    let run: &[u8] = &[
        0x8b, 0x41, 0x10, // ASM: mov eax, [rcx+0x10]
        0xc3, // ASM: ret
    ];
    let p = raw_classes(
        &[
            (0x1000, base_ctor),
            (0x1020, der_ctor),
            (0x1080, call),
            (0x1160, &[0xc3]),
            (0x1180, run),
        ],
        &[(0x2000, &[0x1160, 0x1160]), (0x2010, &[0x1160, 0x1160])],
        &[
            ("Base::Base", 0x1000),
            ("Der::Der", 0x1020),
            ("Base::Call", 0x1080),
            ("Der::Run", 0x1180),
        ],
    );
    let a = Analysis::compute(&p);
    let run = a.function(0x1180).expect("Run");
    assert_eq!(run.param_hints.get(&0).map(String::as_str), Some("Der"));
}

/// A function a class's table holds keeps that class even when its name,
/// from the base table it stores, says otherwise.
///
/// `Der::Der` stores `Der`'s table and calls no base constructor, so no
/// parent links `Der` to `Base`. `D` stores `Base`'s table, the base phase
/// of a derived destructor, which names it after `Base`, and only `Der`'s
/// table holds it: its `this` is a `Der`.
#[test]
fn a_held_function_keeps_its_table_class_over_its_name() {
    let base_ctor: &[u8] = &[
        0x48, 0x8d, 0x05, 0xf9, 0x0f, 0x00, 0x00, // ASM: lea rax, [0x2000]
        0x48, 0x89, 0x01, // ASM: mov [rcx], rax
        0xc3, // ASM: ret
    ];
    let der_ctor: &[u8] = &[
        0x48, 0x8d, 0x05, 0xe9, 0x0f, 0x00, 0x00, // ASM: lea rax, [0x2010]
        0x48, 0x89, 0x01, // ASM: mov [rcx], rax
        0xc3, // ASM: ret
    ];
    let d: &[u8] = &[
        0x48, 0x8d, 0x05, 0x79, 0x0e, 0x00, 0x00, // ASM: lea rax, [0x2000]
        0x48, 0x89, 0x01, // ASM: mov [rcx], rax
        0xc3, // ASM: ret
    ];
    let p = raw_classes(
        &[
            (0x1000, base_ctor),
            (0x1020, der_ctor),
            (0x1180, d),
            (0x1190, &[0xc3]),
        ],
        &[(0x2000, &[0x1190, 0x1190]), (0x2010, &[0x1180, 0x1190])],
        &[("Base::Base", 0x1000), ("Der::Der", 0x1020)],
    );
    let a = Analysis::compute(&p);
    let d = a.function(0x1180).expect("D");
    assert!(
        d.name.as_deref().is_some_and(|n| n.starts_with("Base::")),
        "{:?}",
        d.name
    );
    assert_eq!(d.param_hints.get(&0).map(String::as_str), Some("Der"));
}

/// A handler takes its class prefix from a class its callers hand it, never
/// from an ancestor wider than all of them.
///
/// `A` and `B` derive from `Base`. `H` prints the type check of `Cmd::Xc`'s
/// handler and `A::Go` and `B::Go` call it with their `this`: it is a
/// `Base`, which neither caller said, so its name stays `HandleXc`. `H2`,
/// the handler of `Cmd::Yc`, is called by `A::Go2` alone and is
/// `A::HandleYc`.
#[test]
fn a_handler_takes_no_prefix_wider_than_its_callers() {
    /// Packs text, NUL-terminated, into little-endian words.
    fn words(text: &str) -> Vec<u64> {
        let mut bytes = text.as_bytes().to_vec();
        bytes.resize(bytes.len() / 8 * 8 + 8, 0);
        bytes
            .chunks_exact(8)
            .map(|c| u64::from_le_bytes(c.try_into().expect("eight bytes")))
            .collect()
    }
    let base_ctor: &[u8] = &[
        0x48, 0x8d, 0x05, 0xf9, 0x0f, 0x00, 0x00, // ASM: lea rax, [0x2000]
        0x48, 0x89, 0x01, // ASM: mov [rcx], rax
        0xc3, // ASM: ret
    ];
    let a_ctor: &[u8] = &[
        0x53, // ASM: push rbx
        0x48, 0x8b, 0xd9, // ASM: mov rbx, rcx
        0xe8, 0xd7, 0xff, 0xff, 0xff, // ASM: call 0x1000
        0x48, 0x8d, 0x05, 0xe0, 0x0f, 0x00, 0x00, // ASM: lea rax, [0x2010]
        0x48, 0x89, 0x03, // ASM: mov [rbx], rax
        0x5b, // ASM: pop rbx
        0xc3, // ASM: ret
    ];
    let b_ctor: &[u8] = &[
        0x53, // ASM: push rbx
        0x48, 0x8b, 0xd9, // ASM: mov rbx, rcx
        0xe8, 0xb7, 0xff, 0xff, 0xff, // ASM: call 0x1000
        0x48, 0x8d, 0x05, 0xd0, 0x0f, 0x00, 0x00, // ASM: lea rax, [0x2020]
        0x48, 0x89, 0x03, // ASM: mov [rbx], rax
        0x5b, // ASM: pop rbx
        0xc3, // ASM: ret
    ];
    let call = |rel: u8| -> Vec<u8> {
        vec![
            0x48, 0x83, 0xec, 0x28, // ASM: sub rsp, 0x28
            0xe8, rel, 0x00, 0x00, 0x00, // ASM: call the handler
            0x48, 0x83, 0xc4, 0x28, // ASM: add rsp, 0x28
            0xc3, // ASM: ret
        ]
    };
    let handler: &[u8] = &[
        0x48, 0x8d, 0x15, 0xf9, 0x0e, 0x00, 0x00, // ASM: lea rdx, [the type check]
        0x8b, 0x41, 0x08, // ASM: mov eax, [rcx+8]
        0xc3, // ASM: ret
    ];
    let (a_go, b_go, a_go2) = (call(0xf7), call(0xd7), call(0xf7));
    let xc = words("Command handler for type 'Cmd::Xc' called with command of wrong type");
    let yc = words("Command handler for type 'Cmd::Yc' called with command of wrong type");
    let p = raw_classes(
        &[
            (0x1000, base_ctor),
            (0x1020, a_ctor),
            (0x1040, b_ctor),
            (0x1100, &a_go),
            (0x1120, &b_go),
            (0x1140, &a_go2),
            (0x1180, &[0xc3]),
            (0x1200, handler),
            (0x1240, handler),
        ],
        &[
            (0x2000, &[0x1180, 0x1180]),
            (0x2010, &[0x1180, 0x1180]),
            (0x2020, &[0x1180, 0x1180]),
            (0x2100, &xc),
            (0x2140, &yc),
        ],
        &[
            ("Base::Base", 0x1000),
            ("A::A", 0x1020),
            ("B::B", 0x1040),
            ("A::Go", 0x1100),
            ("B::Go", 0x1120),
            ("A::Go2", 0x1140),
        ],
    );
    let a = Analysis::compute(&p);
    let name = |e: u64| a.function(e).and_then(|f| f.name.clone());
    assert_eq!(name(0x1240).as_deref(), Some("A::HandleYc"));
    assert_eq!(name(0x1200).as_deref(), Some("HandleXc"));
}

/// A member that never reads its first register bounds nothing by the
/// class its name gives.
///
/// `H`, which nothing calls, keeps its first parameter in `rbx`, calls the
/// factory `Cmd::Create` with it still in `rcx`, then hands it to `Obj::Run`,
/// which reads `[rcx+8]`. `Create` reads no argument, so only `Run` bounds
/// the parameter: it is an `Obj`.
#[test]
fn a_callee_never_reading_its_first_argument_bounds_no_class() {
    let create: &[u8] = &[
        0x31, 0xc0, // ASM: xor eax, eax
        0xc3, // ASM: ret
    ];
    let run: &[u8] = &[
        0x8b, 0x41, 0x08, // ASM: mov eax, [rcx+8]
        0xc3, // ASM: ret
    ];
    let h: &[u8] = &[
        0x53, // ASM: push rbx
        0x48, 0x8b, 0xd9, // ASM: mov rbx, rcx
        0xe8, 0xf7, 0xfe, 0xff, 0xff, // ASM: call 0x1000
        0x48, 0x8b, 0xcb, // ASM: mov rcx, rbx
        0xe8, 0x0f, 0xff, 0xff, 0xff, // ASM: call 0x1020
        0x5b, // ASM: pop rbx
        0xc3, // ASM: ret
    ];
    let p = raw_classes(
        &[(0x1000, create), (0x1020, run), (0x1100, h)],
        &[],
        &[("Cmd::Create", 0x1000), ("Obj::Run", 0x1020), ("h", 0x1100)],
    );
    let a = Analysis::compute(&p);
    let h = a.function(0x1100).expect("H");
    assert_eq!(h.param_hints.get(&0).map(String::as_str), Some("Obj"));
}

/// A parameter whose class still flips from round to round when the rounds
/// stop has no class, whichever one the last round gave.
///
/// `A` and `U` derive from `Base`. `A::Go` calls `D` with its `this`; `B`,
/// which nothing calls, hands its first parameter to `U::Use` and to `D`.
/// `B` is the deepest class its callees accept and votes for `D` with it:
/// `D` is an `A`, so `B` is untyped (`U` and `A` share no line), so `D` is
/// an `A`, so `B` is a `U`, so `D` is a `Base`, and around again for ever.
#[test]
fn a_parameter_whose_class_keeps_flipping_has_none() {
    let base_ctor: &[u8] = &[
        0x48, 0x8d, 0x05, 0xf9, 0x0f, 0x00, 0x00, // ASM: lea rax, [0x2000]
        0x48, 0x89, 0x01, // ASM: mov [rcx], rax
        0xc3, // ASM: ret
    ];
    let a_ctor: &[u8] = &[
        0x53, // ASM: push rbx
        0x48, 0x8b, 0xd9, // ASM: mov rbx, rcx
        0xe8, 0xd7, 0xff, 0xff, 0xff, // ASM: call 0x1000
        0x48, 0x8d, 0x05, 0xe0, 0x0f, 0x00, 0x00, // ASM: lea rax, [0x2010]
        0x48, 0x89, 0x03, // ASM: mov [rbx], rax
        0x5b, // ASM: pop rbx
        0xc3, // ASM: ret
    ];
    let u_ctor: &[u8] = &[
        0x53, // ASM: push rbx
        0x48, 0x8b, 0xd9, // ASM: mov rbx, rcx
        0xe8, 0xb7, 0xff, 0xff, 0xff, // ASM: call 0x1000
        0x48, 0x8d, 0x05, 0xd0, 0x0f, 0x00, 0x00, // ASM: lea rax, [0x2020]
        0x48, 0x89, 0x03, // ASM: mov [rbx], rax
        0x5b, // ASM: pop rbx
        0xc3, // ASM: ret
    ];
    let go: &[u8] = &[
        0x48, 0x83, 0xec, 0x28, // ASM: sub rsp, 0x28
        0xe8, 0xf7, 0x00, 0x00, 0x00, // ASM: call 0x1200
        0x48, 0x83, 0xc4, 0x28, // ASM: add rsp, 0x28
        0xc3, // ASM: ret
    ];
    let read: &[u8] = &[
        0x8b, 0x41, 0x08, // ASM: mov eax, [rcx+8]
        0xc3, // ASM: ret
    ];
    let b: &[u8] = &[
        0x53, // ASM: push rbx
        0x48, 0x8b, 0xd9, // ASM: mov rbx, rcx
        0xe8, 0xd7, 0xff, 0xff, 0xff, // ASM: call 0x1220
        0x48, 0x8b, 0xcb, // ASM: mov rcx, rbx
        0xe8, 0xaf, 0xff, 0xff, 0xff, // ASM: call 0x1200
        0x5b, // ASM: pop rbx
        0xc3, // ASM: ret
    ];
    let p = raw_classes(
        &[
            (0x1000, base_ctor),
            (0x1020, a_ctor),
            (0x1040, u_ctor),
            (0x1100, go),
            (0x1180, &[0xc3]),
            (0x1200, read),
            (0x1220, read),
            (0x1240, b),
        ],
        &[
            (0x2000, &[0x1180, 0x1180]),
            (0x2010, &[0x1180, 0x1180]),
            (0x2020, &[0x1180, 0x1180]),
        ],
        &[
            ("Base::Base", 0x1000),
            ("A::A", 0x1020),
            ("U::U", 0x1040),
            ("A::Go", 0x1100),
            ("d", 0x1200),
            ("U::Use", 0x1220),
            ("b", 0x1240),
        ],
    );
    let a = Analysis::compute(&p);
    for e in [0x1200, 0x1240] {
        let f = a.function(e).expect("a flipping function");
        assert_eq!(f.param_hints.get(&0), None, "{e:#x}");
    }
}

/// A function that never reads a register takes no class from what its
/// callers leave there; the tables holding it still type its `this`.
///
/// `Base::Go` calls `F`, a factory (`xor eax, eax; ret`), with its `this`
/// still in `rcx`: `F` has no `this` to type. `H`, a `ret` that `Base`'s
/// table holds, stays a `Base` method though it reads nothing either.
#[test]
fn a_register_its_function_never_reads_takes_no_class_from_callers() {
    let base_ctor: &[u8] = &[
        0x48, 0x8d, 0x05, 0xf9, 0x0f, 0x00, 0x00, // ASM: lea rax, [0x2000]
        0x48, 0x89, 0x01, // ASM: mov [rcx], rax
        0xc3, // ASM: ret
    ];
    let go: &[u8] = &[
        0x48, 0x83, 0xec, 0x28, // ASM: sub rsp, 0x28
        0xe8, 0xf7, 0x00, 0x00, 0x00, // ASM: call 0x1200
        0x48, 0x83, 0xc4, 0x28, // ASM: add rsp, 0x28
        0xc3, // ASM: ret
    ];
    let factory: &[u8] = &[
        0x31, 0xc0, // ASM: xor eax, eax
        0xc3, // ASM: ret
    ];
    let p = raw_classes(
        &[
            (0x1000, base_ctor),
            (0x1100, go),
            (0x1180, &[0xc3]),
            (0x1200, factory),
        ],
        &[(0x2000, &[0x1180, 0x1180])],
        &[("Base::Base", 0x1000), ("Base::Go", 0x1100), ("f", 0x1200)],
    );
    let a = Analysis::compute(&p);
    let f = a.function(0x1200).expect("F");
    assert_eq!(f.param_hints.get(&0), None);
    let h = a.function(0x1180).expect("H");
    assert_eq!(h.param_hints.get(&0).map(String::as_str), Some("Base"));
}

/// A callee's own use of a parameter outranks the class a single caller
/// hands on from its own hint.
///
/// `Wrong::Go` calls `C` with its `this` in `rdx`, so `C`'s second
/// parameter is a `Wrong`. `C` hands it on untouched to `F`, which moves it
/// to `rcx` and calls `Obj::Use`, which reads `[rcx+8]`: `F` uses it as an
/// `Obj`, which outranks what `C` was only told.
#[test]
fn a_callee_s_own_use_outranks_one_caller_s_hint() {
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
    let used: &[u8] = &[
        0x8b, 0x41, 0x08, // ASM: mov eax, [rcx+8]
        0xc3, // ASM: ret
    ];
    let p = raw_classes(
        &[(0x1000, go), (0x1100, c), (0x1200, f), (0x1300, used)],
        &[],
        &[
            ("Wrong::Go", 0x1000),
            ("c", 0x1100),
            ("f", 0x1200),
            ("Obj::Use", 0x1300),
        ],
    );
    let a = Analysis::compute(&p);
    let c = a.function(0x1100).expect("C");
    assert_eq!(c.param_hints.get(&1).map(String::as_str), Some("Wrong"));
    let f = a.function(0x1200).expect("F");
    assert_eq!(f.param_hints.get(&1).map(String::as_str), Some("Obj"));
}

/// Of an object and the member it starts with, a parameter is the object
/// whenever a vote or a use names it, and the member only when nothing else
/// does.
///
/// `Util::Dict::Add` hands its `this` to `Util::List::Push`: a `Util::Dict`
/// starts with a `Util::List`. `H` is called by `Util::Dict::Find` and by
/// `Util::List::Scan`, `G` hands its parameter to `Util::List::Push` and to
/// `Util::Dict::Size`: both are a `Util::Dict`. `K`, called by
/// `Util::List::Scan` alone, is a `Util::List`. `Util::Map<Key>::Add` hands
/// its `this` to `Util::Vec<Util::Pair<Key> >::Push`, so every
/// `Util::Map<T>` starts with a `Util::Vec<Util::Pair<T> >`: `N`, handed to
/// `Util::Vec<Util::Pair<Other> >::Push` and to `Util::Map<Other>::Size`,
/// is a `Util::Map<Other>`. `Holder::Setup` hands its field at `+0x10` to
/// `Util::List::Push`, to `Util::Dict::Size` and to `Q`: the field is a
/// `Util::Dict`, and so is `Q`.
#[test]
fn a_container_outranks_the_member_it_starts_with() {
    let call = |rel: [u8; 4]| -> Vec<u8> {
        vec![
            0x48, 0x83, 0xec, 0x28, // ASM: sub rsp, 0x28
            0xe8, rel[0], rel[1], rel[2], rel[3], // ASM: call the member
            0x48, 0x83, 0xc4, 0x28, // ASM: add rsp, 0x28
            0xc3, // ASM: ret
        ]
    };
    let both = |first: [u8; 4], second: [u8; 4]| -> Vec<u8> {
        vec![
            0x53, // ASM: push rbx
            0x48, 0x8b, 0xd9, // ASM: mov rbx, rcx
            0xe8, first[0], first[1], first[2], first[3], // ASM: call the first
            0x48, 0x8b, 0xcb, // ASM: mov rcx, rbx
            0xe8, second[0], second[1], second[2], second[3], // ASM: call the second
            0x5b,      // ASM: pop rbx
            0xc3,      // ASM: ret
        ]
    };
    let read: &[u8] = &[
        0x8b, 0x01, // ASM: mov eax, [rcx]
        0xc3, // ASM: ret
    ];
    let read8: &[u8] = &[
        0x8b, 0x41, 0x08, // ASM: mov eax, [rcx+8]
        0xc3, // ASM: ret
    ];
    let add = call([0xf7, 0x00, 0x00, 0x00]); // ASM: call 0x1100
    let find = call([0xf7, 0x00, 0x00, 0x00]); // ASM: call 0x1300
    let scan = both([0xb7, 0x00, 0x00, 0x00], [0x2f, 0x01, 0x00, 0x00]); // ASM: call 0x1300; call 0x1380
    let g = both([0xb7, 0xfd, 0xff, 0xff], [0xcf, 0xfd, 0xff, 0xff]); // ASM: call 0x1100; call 0x1120
    let map_add = call([0x37, 0x00, 0x00, 0x00]); // ASM: call 0x1440
    let n = both([0x37, 0x00, 0x00, 0x00], [0x4f, 0x00, 0x00, 0x00]); // ASM: call 0x14c0; call 0x14e0
    let setup: &[u8] = &[
        0x53, // ASM: push rbx
        0x48, 0x8b, 0xd9, // ASM: mov rbx, rcx
        0x48, 0x8d, 0x4b, 0x10, // ASM: lea rcx, [rbx+0x10]
        0xe8, 0xf3, 0xfb, 0xff, 0xff, // ASM: call 0x1100
        0x48, 0x8d, 0x4b, 0x10, // ASM: lea rcx, [rbx+0x10]
        0xe8, 0x0a, 0xfc, 0xff, 0xff, // ASM: call 0x1120
        0x48, 0x8d, 0x4b, 0x10, // ASM: lea rcx, [rbx+0x10]
        0xe8, 0x61, 0x00, 0x00, 0x00, // ASM: call 0x1580
        0x5b, // ASM: pop rbx
        0xc3, // ASM: ret
    ];
    let p = raw_classes(
        &[
            (0x1000, &add),
            (0x1100, read),
            (0x1120, read8),
            (0x1200, &find),
            (0x1240, &scan),
            (0x1300, read),
            (0x1340, &g),
            (0x1380, read),
            (0x1400, &map_add),
            (0x1440, read),
            (0x1480, &n),
            (0x14c0, read),
            (0x14e0, read8),
            (0x1500, setup),
            (0x1580, read),
        ],
        &[],
        &[
            ("Util::Dict::Add", 0x1000),
            ("Util::List::Push", 0x1100),
            ("Util::Dict::Size", 0x1120),
            ("Util::Dict::Find", 0x1200),
            ("Util::List::Scan", 0x1240),
            ("h", 0x1300),
            ("g", 0x1340),
            ("k", 0x1380),
            ("Util::Map<Key>::Add", 0x1400),
            ("Util::Vec<Util::Pair<Key> >::Push", 0x1440),
            ("n", 0x1480),
            ("Util::Vec<Util::Pair<Other> >::Push", 0x14c0),
            ("Util::Map<Other>::Size", 0x14e0),
            ("Holder::Setup", 0x1500),
            ("q", 0x1580),
        ],
    );
    let a = Analysis::compute(&p);
    let class = |e: u64| a.function(e).and_then(|f| f.param_hints.get(&0).cloned());
    assert_eq!(class(0x1300).as_deref(), Some("Util::Dict"));
    assert_eq!(class(0x1340).as_deref(), Some("Util::Dict"));
    assert_eq!(class(0x1380).as_deref(), Some("Util::List"));
    assert_eq!(class(0x1480).as_deref(), Some("Util::Map<Other>"));
    assert_eq!(class(0x1580).as_deref(), Some("Util::Dict"));
}

/// Evidence a later round finds revises a parameter's class: two unrelated
/// classes leave it untyped, whichever arrived first.
///
/// `A::F` calls `U` with its `this` in the first round; `B::G` calls `H`,
/// which is typed `B` in that round and calls `U` with the same `this` in
/// the next. `A` and `B` have no common ancestor, so `U` is neither.
#[test]
fn a_later_conflicting_vote_revises_the_first_class() {
    let call = |target: u64, from: u64| -> Vec<u8> {
        let rel = i32::try_from(target).expect("near") - i32::try_from(from + 9).expect("near");
        let r = rel.to_le_bytes();
        vec![
            0x48, 0x83, 0xec, 0x28, // ASM: sub rsp, 0x28
            0xe8, r[0], r[1], r[2], r[3], // ASM: call target
            0x48, 0x83, 0xc4, 0x28, // ASM: add rsp, 0x28
            0xc3, // ASM: ret
        ]
    };
    let u: &[u8] = &[
        0x8b, 0x01, // ASM: mov eax, [rcx]
        0xc3, // ASM: ret
    ];
    let (af, h, bg) = (
        call(0x1100, 0x1000),
        call(0x1100, 0x1040),
        call(0x1040, 0x1080),
    );
    let p = raw_classes(
        &[(0x1000, &af), (0x1040, &h), (0x1080, &bg), (0x1100, u)],
        &[],
        &[
            ("A::F", 0x1000),
            ("h", 0x1040),
            ("B::G", 0x1080),
            ("u", 0x1100),
        ],
    );
    let a = Analysis::compute(&p);
    let hint = |e: u64| {
        a.function(e)
            .expect("a function")
            .param_hints
            .get(&0)
            .cloned()
    };
    assert_eq!(hint(0x1040).as_deref(), Some("B"));
    assert_eq!(hint(0x1100), None, "A and B share no ancestor");
}

/// A class one caller only hands on settles on a callee no other caller
/// contradicts, and on no callee another caller hands data of no class or
/// of an unrelated one.
///
/// `N::A::BindM` (a signature string names it) hands its declared
/// `const N::M &` to the third argument of `sink`, `sink2` and `sink3`.
/// `N::A::BindF` copies the `N::F` its own third argument points at into a
/// local and hands `sink` that copy, as a blob binder hands
/// `sqlite3_bind_blob` the bytes of a `float4`; `k` hands `sink3` constant
/// bytes; `g` hands `sink2` a local nothing says the class of. `sink` and
/// `sink3` take no class, `sink2` stays an `N::M`.
#[test]
fn a_class_handed_on_once_yields_to_a_contradicting_caller() {
    let words = |text: &[u8]| -> Vec<u64> {
        text.chunks(8)
            .map(|c| {
                let mut w = [0u8; 8];
                w[..c.len()].copy_from_slice(c);
                u64::from_le_bytes(w)
            })
            .collect()
    };
    let root: &[u8] = &[
        0x48, 0x83, 0xec, 0x28, // ASM: sub rsp, 0x28
        0xe8, 0xf7, 0x00, 0x00, 0x00, // ASM: call 0x1100
        0xe8, 0xf2, 0x01, 0x00, 0x00, // ASM: call 0x1200
        0xe8, 0xed, 0x02, 0x00, 0x00, // ASM: call 0x1300
        0xe8, 0xe8, 0x03, 0x00, 0x00, // ASM: call 0x1400
        0x48, 0x83, 0xc4, 0x28, // ASM: add rsp, 0x28
        0xc3, // ASM: ret
    ];
    let bind_m: &[u8] = &[
        0x53, // ASM: push rbx
        0x48, 0x83, 0xec, 0x20, // ASM: sub rsp, 0x20
        0x48, 0x8d, 0x05, 0xf4, 0x0e, 0x00, 0x00, // ASM: lea rax, [0x2000]
        0x4c, 0x89, 0xc3, // ASM: mov rbx, r8
        0xe8, 0xec, 0x03, 0x00, 0x00, // ASM: call 0x1500
        0x49, 0x89, 0xd8, // ASM: mov r8, rbx
        0xe8, 0x04, 0x04, 0x00, 0x00, // ASM: call 0x1520
        0x49, 0x89, 0xd8, // ASM: mov r8, rbx
        0xe8, 0x1c, 0x04, 0x00, 0x00, // ASM: call 0x1540
        0x48, 0x83, 0xc4, 0x20, // ASM: add rsp, 0x20
        0x5b, // ASM: pop rbx
        0xc3, // ASM: ret
    ];
    let bind_f: &[u8] = &[
        0x48, 0x83, 0xec, 0x48, // ASM: sub rsp, 0x48
        0x48, 0x8d, 0x05, 0x75, 0x0e, 0x00, 0x00, // ASM: lea rax, [0x2080]
        0x41, 0x0f, 0x10, 0x00, // ASM: movups xmm0, [r8]
        0x0f, 0x11, 0x44, 0x24, 0x30, // ASM: movups [rsp+0x30], xmm0
        0x4c, 0x8d, 0x44, 0x24, 0x30, // ASM: lea r8, [rsp+0x30]
        0xe8, 0xe2, 0x02, 0x00, 0x00, // ASM: call 0x1500
        0x48, 0x83, 0xc4, 0x48, // ASM: add rsp, 0x48
        0xc3, // ASM: ret
    ];
    let g: &[u8] = &[
        0x48, 0x83, 0xec, 0x48, // ASM: sub rsp, 0x48
        0x4c, 0x8d, 0x44, 0x24, 0x30, // ASM: lea r8, [rsp+0x30]
        0xe8, 0x12, 0x02, 0x00, 0x00, // ASM: call 0x1520
        0x48, 0x83, 0xc4, 0x48, // ASM: add rsp, 0x48
        0xc3, // ASM: ret
    ];
    let k: &[u8] = &[
        0x48, 0x83, 0xec, 0x28, // ASM: sub rsp, 0x28
        0x4c, 0x8d, 0x05, 0xf5, 0x0c, 0x00, 0x00, // ASM: lea r8, [0x2100]
        0xe8, 0x30, 0x01, 0x00, 0x00, // ASM: call 0x1540
        0x48, 0x83, 0xc4, 0x28, // ASM: add rsp, 0x28
        0xc3, // ASM: ret
    ];
    let sink: &[u8] = &[
        0x41, 0x8b, 0x00, // ASM: mov eax, [r8]
        0xc3, // ASM: ret
    ];
    let sig_m = words(b"void __cdecl N::A::BindM(int,const class N::M &)\0");
    let sig_f = words(b"void __cdecl N::A::BindF(int,const class N::F &)\0");
    let bytes = [0x8899_aabb_ccdd_eeff_u64, 0x0011_2233_4455_6677];
    let p = raw_classes(
        &[
            (0x1000, root),
            (0x1100, bind_m),
            (0x1200, bind_f),
            (0x1300, g),
            (0x1400, k),
            (0x1500, sink),
            (0x1520, sink),
            (0x1540, sink),
        ],
        &[(0x2000, &sig_m), (0x2080, &sig_f), (0x2100, &bytes)],
        &[
            ("root", 0x1000),
            ("g", 0x1300),
            ("k", 0x1400),
            ("sink", 0x1500),
            ("sink2", 0x1520),
            ("sink3", 0x1540),
        ],
    );
    let a = Analysis::compute(&p);
    let name = |e: u64| a.function(e).and_then(|f| f.name.clone());
    assert_eq!(name(0x1100).as_deref(), Some("N::A::BindM"));
    assert_eq!(name(0x1200).as_deref(), Some("N::A::BindF"));
    let hint = |e: u64| {
        a.function(e)
            .expect("a function")
            .param_hints
            .get(&2)
            .cloned()
    };
    assert_eq!(hint(0x1500), None, "a copied N::F reaches it");
    assert_eq!(hint(0x1520).as_deref(), Some("N::M"), "nothing contradicts");
    assert_eq!(hint(0x1540), None, "constant bytes reach it");
}

/// A parameter some call site hands a string literal holds no object, so
/// no other call site's class types it.
///
/// `Cls::G` passes its own `this` as `R`'s second argument (`mov rdx, rcx;
/// call R; ret`); `g` passes the file name `"util/a.cc"` there (`lea rdx,
/// [str]; call R; ret`), as every caller of an assertion reporter does.
/// `R`'s second parameter takes no class. `Cls::G2` passes its `this` to
/// `R2` the same way, and `g2` (`test ecx, ecx; jne L; lea rdx, [str]; ret;
/// L: call R2; ret`) loads the string only on the path that returns: the
/// call hands on its own `rdx`, so `R2` keeps `Cls`.
#[test]
fn a_string_literal_argument_vetoes_a_class() {
    let r: &[u8] = &[
        0x8b, 0x02, // ASM: mov eax, [rdx]
        0xc3, // ASM: ret
    ];
    let g_cls: &[u8] = &[
        0x48, 0x8b, 0xd1, // ASM: mov rdx, rcx
        0xe8, 0xd8, 0x00, 0x00, 0x00, // ASM: call 0x1100
        0xc3, // ASM: ret
    ];
    let g: &[u8] = &[
        0x48, 0x8d, 0x15, 0xb9, 0x0f, 0x00, 0x00, // ASM: lea rdx, [0x2000]
        0xe8, 0xb4, 0x00, 0x00, 0x00, // ASM: call 0x1100
        0xc3, // ASM: ret
    ];
    let g2_cls: &[u8] = &[
        0x48, 0x8b, 0xd1, // ASM: mov rdx, rcx
        0xe8, 0x98, 0x00, 0x00, 0x00, // ASM: call 0x1120
        0xc3, // ASM: ret
    ];
    let g2: &[u8] = &[
        0x85, 0xc9, // ASM: test ecx, ecx
        0x75, 0x08, // ASM: jne 0x106c
        0x48, 0x8d, 0x15, 0x95, 0x0f, 0x00, 0x00, // ASM: lea rdx, [0x2000]
        0xc3, // ASM: ret
        0xe8, 0xaf, 0x00, 0x00, 0x00, // ASM: call 0x1120
        0xc3, // ASM: ret
    ];
    let name = u64::from_le_bytes(*b"util/a.c");
    let tail = u64::from_le_bytes(*b"c\0\0\0\0\0\0\0");
    let p = raw_classes(
        &[
            (0x1020, g_cls),
            (0x1040, g),
            (0x1060, g2),
            (0x1080, g2_cls),
            (0x1100, r),
            (0x1120, r),
        ],
        &[(0x2000, &[name, tail])],
        &[
            ("Cls::G", 0x1020),
            ("g", 0x1040),
            ("g2", 0x1060),
            ("Cls::G2", 0x1080),
            ("r", 0x1100),
            ("r2", 0x1120),
        ],
    );
    let a = Analysis::compute(&p);
    let hint = |e: u64| {
        a.function(e)
            .expect("a function")
            .param_hints
            .get(&1)
            .cloned()
    };
    assert_eq!(hint(0x1100), None, "a literal reaches it");
    assert_eq!(
        hint(0x1120).as_deref(),
        Some("Cls"),
        "no literal reaches it"
    );
}

/// A list of entries keeps one function per clone class and names the rest.
///
/// `CL_A` and `CL_B` are clones, so `CL_B` folds under `CL_A`; `CL_C`
/// stands alone.
#[test]
fn dedupe_keeps_one_function_per_clone_class() {
    let a = Analysis::compute(&fixture());
    let kept = a.dedupe_clones(&[0x4220, 0x4260, 0x4240]);
    assert_eq!(kept, vec![(0x4220, vec![0x4240]), (0x4260, vec![])]);
}

/// Creators voting several descriptors name the table after their common
/// ancestor.
///
/// `DC` creates from `Ns::Thing`'s descriptor and `DC3` from `Ns::T2`'s,
/// both calling `DK`; `Ns::T2` derives from `Ns::Thing`, so the table `DK`
/// stores is `Ns::Thing`'s.
#[test]
fn conflicting_creator_votes_resolve_to_the_common_ancestor() {
    let a = Analysis::compute(&fixture());
    assert_eq!(
        a.classes.vtables.get(&0x28c0).map(String::as_str),
        Some("Ns::Thing")
    );
    assert_eq!(
        a.function(0x1050).map(|f| f.callees.clone()),
        Some(vec![0x1bb0])
    );
}
