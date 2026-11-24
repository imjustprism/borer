/// The lifter agrees with the emulator on integer and stack arithmetic.
///
/// Every register it writes, the ones it leaves alone and the stack
/// pointer match. Each 32-bit write clears the upper half (`shr r9d`
/// shifts only the low half in, a byte merged into `r12d` keeps it
/// clear, `mov edx, edx` and a `cmov` not taken clear it) and `movsxd`
/// sign-extends.
#[test]
fn the_lifter_agrees_with_the_emulator() {
    let p = crate::program::Program::raw_x64(&[
        0x48, 0x89, 0xc8, // ASM: mov rax, rcx
        0x48, 0x01, 0xd0, // ASM: add rax, rdx
        0x48, 0xc1, 0xe0, 0x03, // ASM: shl rax, 3
        0x8d, 0x0c, 0x12, // ASM: lea ecx, [rdx+rdx]
        0x0f, 0xaf, 0xc1, // ASM: imul eax, ecx
        0x48, 0x83, 0xec, 0x10, // ASM: sub rsp, 0x10
        0x48, 0x89, 0x04, 0x24, // ASM: mov [rsp], rax
        0x48, 0x8b, 0x5c, 0x24, 0x08, // ASM: mov rbx, [rsp+8]
        0x48, 0x0f, 0xb6, 0xf3, // ASM: movzx rsi, bl
        0x49, 0x89, 0xc9, // ASM: mov r9, rcx
        0x41, 0xc1, 0xe9, 0x04, // ASM: shr r9d, 4
        0x41, 0x89, 0xc4, // ASM: mov r12d, eax
        0x41, 0x80, 0xf4, 0x01, // ASM: xor r12b, 1
        0x89, 0xd2, // ASM: mov edx, edx
        0x48, 0x63, 0x7c, 0x24, 0x08, // ASM: movsxd rdi, [rsp+8]
        0x31, 0xc0, // ASM: xor eax, eax
        0x85, 0xc0, // ASM: test eax, eax
        0x44, 0x0f, 0x45, 0xc1, // ASM: cmovne r8d, ecx (not taken)
        0x48, 0x83, 0xc4, 0x10, // ASM: add rsp, 0x10
        0xc3, // ASM: ret
    ]);
    let a = crate::analysis::Analysis::compute(&p);
    for seed in 1..=4 {
        let v = super::verify::verify(&p, &a, &[0x1000], seed);
        assert_eq!(v.checked, 1, "{v:?}");
        assert!(v.compared >= 16, "{v:?}");
        assert!(v.mismatches.is_empty(), "{}", super::verify::verify_tsv(&v));
    }
}

/// A scenario folds the branches on its parameter: under `a2 = 2` only
/// the arm for 2 is written, and the header counts the cut blocks.
#[test]
fn a_scenario_keeps_the_code_that_can_run() {
    let p = crate::program::Program::raw_x64(&[
        0x83, 0xfa, 0x02, // ASM: cmp edx, 2
        0x74, 0x0b, // ASM: je 0x1010
        0x83, 0xfa, 0x03, // ASM: cmp edx, 3
        0x74, 0x0c, // ASM: je 0x1016
        0xb8, 0x01, 0x00, 0x00, 0x00, // ASM: mov eax, 1
        0xc3, // ASM: ret
        0xb8, 0x14, 0x00, 0x00, 0x00, // ASM: mov eax, 20 (0x1010)
        0xc3, // ASM: ret
        0xb8, 0x1e, 0x00, 0x00, 0x00, // ASM: mov eax, 30 (0x1016)
        0xc3, // ASM: ret
    ]);
    let a = crate::analysis::Analysis::compute(&p);
    let o = crate::analysis::Overlay::default();
    let all = super::decompile(&p, &a, &o, 0x1000).expect("decompiles");
    assert!(
        all.contains("return 20;") && all.contains("return 30;"),
        "{all}"
    );
    let two = super::decompile_scenario(&p, &a, &o, 0x1000, &[(1, 2)]).expect("decompiles");
    assert!(
        two.starts_with("// scenario: a2 = 2; 3 of 5 blocks cannot run\n"),
        "{two}"
    );
    assert!(
        two.contains("return 20;") && !two.contains("return 30;"),
        "{two}"
    );
    assert!(!two.contains("return 1;"), "{two}");
    assert_eq!(
        super::parse_scenario("a2=5, a1=0x10"),
        Ok(vec![(1, 5), (0, 0x10)])
    );
    assert_eq!(super::parse_scenario("a3=-1"), Ok(vec![(2, u64::MAX)]));
    assert!(super::parse_scenario("b2=5").is_err());
    assert!(super::parse_scenario("").is_err());
    let cases = super::explode(&p, &a, &o, 0x1000, 1, &[0, 2, 3, 4, 5]);
    let text = super::explode_tsv(&cases, 1, 5);
    assert!(
        text.starts_with("# a2 over 5 values: 3 behaviours in a function of 5 blocks\n"),
        "{text}"
    );
    assert!(text.contains("\n0,4-5\t"), "{text}");
    assert!(text.contains("\t20\n"), "{text}");
    assert_eq!(super::parse_explosion("a2=0..4"), Ok((1, vec![0, 1, 2, 3])));
    assert_eq!(super::parse_explosion("a1=1|0x20"), Ok((0, vec![1, 0x20])));
    assert!(super::parse_explosion("a1=0..100000").is_err());
}

/// A sign test after a compare that overflows its width folds by the
/// width's top bit: `0x7fffffff - -1` is negative at 32 bits, so the
/// `js` is taken.
#[test]
fn a_sign_test_folds_at_the_compare_width() {
    let p = crate::program::Program::raw_x64(&[
        0xb9, 0xff, 0xff, 0xff, 0x7f, // ASM: mov ecx, 0x7fffffff
        0x83, 0xf9, 0xff, // ASM: cmp ecx, -1
        0x78, 0x06, // ASM: js 0x1010
        0xb8, 0x01, 0x00, 0x00, 0x00, // ASM: mov eax, 1
        0xc3, // ASM: ret
        0xb8, 0x02, 0x00, 0x00, 0x00, // ASM: mov eax, 2 (0x1010)
        0xc3, // ASM: ret
    ]);
    let a = crate::analysis::Analysis::compute(&p);
    let text =
        super::decompile(&p, &a, &crate::analysis::Overlay::default(), 0x1000).expect("decompiles");
    assert!(
        text.contains("return 2;") && !text.contains("return 1;"),
        "{text}"
    );
}

/// A value used when set and a fallback otherwise is written once; a
/// value that calls something, or a test of one value that uses
/// another, stays as it is.
#[test]
fn a_value_or_its_fallback_is_written_once() {
    assert_eq!(
        super::elvis("rbx = (rax->heapBuffer != 0 ? rax->heapBuffer : rax);"),
        "rbx = (rax->heapBuffer ?: rax);"
    );
    assert_eq!(
        super::elvis("g(\"s\", (*(uint64_t*)(rax + 0x30) != 0 ? *(uint64_t*)(rax + 0x30) : rax));"),
        "g(\"s\", (*(uint64_t*)(rax + 0x30) ?: rax));"
    );
    let call = "x = (f(a) != 0 ? f(a) : b);";
    assert_eq!(super::elvis(call), call);
    let other = "x = (a != 0 ? b : c);";
    assert_eq!(super::elvis(other), other);
}

/// A plain name combined with one value is a compound assignment.
/// A sum of two values, a call, and a store through a pointer stay
/// assignments, and an add is not `++`.
#[test]
fn a_name_added_to_itself_is_a_compound_assignment() {
    assert_eq!(
        super::finish::compound_assign("  var1 = var1 + var2;"),
        "  var1 += var2;"
    );
    assert_eq!(
        super::finish::compound_assign("var1 = var1 - 1;"),
        "var1 -= 1;"
    );
    assert_eq!(
        super::finish::compound_assign("var1 = var1 << 2;"),
        "var1 <<= 2;"
    );
    assert_eq!(
        super::finish::compound_assign("var1 = var1 & 0xff;"),
        "var1 &= 0xff;"
    );
    let sum = "var1 = var1 + var2 + var3;";
    assert_eq!(super::finish::compound_assign(sum), sum);
    let call = "var1 = var1 + f();";
    assert_eq!(super::finish::compound_assign(call), call);
    let star = "*p = *p + 1;";
    assert_eq!(super::finish::compound_assign(star), star);
    let other = "var1 = var2 + var1;";
    assert_eq!(super::finish::compound_assign(other), other);
    assert!(!super::finish::compound_assign("var1 = var1 + 1;").contains("++"));
}

/// An `if` block that opens with the assignment the line before its
/// `if` made drops the repeat; a loop, a condition that names the
/// variable, and a value that is no constant or name keep theirs.
#[test]
fn a_repeated_assignment_into_an_if_goes() {
    let text = concat!(
        "var1 = 0;\n",
        "if ((uint32_t)a1 != 0) {\n",
        "  var1 = 0;\n",
        "  var2 = a1;\n",
        "}\n",
        "var3 = 0;\n",
        "while (a2 != 0) {\n",
        "  var3 = 0;\n",
        "}\n",
        "var4 = 1;\n",
        "if (var4 != a2) {\n",
        "  var4 = 1;\n",
        "}\n",
        "var5 = f();\n",
        "if (a2 != 0) {\n",
        "  var5 = f();\n",
        "}\n",
    );
    let out = super::finish::polish(text, 64, &crate::pack::Packs::default());
    assert_eq!(out.matches("var1 = 0;").count(), 1, "{out}");
    assert_eq!(out.matches("var3 = 0;").count(), 2, "{out}");
    assert_eq!(out.matches("var4 = 1;").count(), 2, "{out}");
    assert_eq!(out.matches("var5 = f();").count(), 2, "{out}");
}

/// A pointer compared with zero is `nullptr`. An integer, a field, a
/// cast to an integer and a string stay on `0`.
#[test]
fn a_pointer_compared_with_zero_is_nullptr() {
    let text = concat!(
        "// signature: int32_t f(uint32_t*a1, int32_t a2, void *this)\n",
        "uint64_t *var1;\n",
        "if (a1 == 0 || *(uint8_t**)a1 != 0) {\n",
        "  return 0;\n",
        "}\n",
        "if (a2 == 0 || *(uint32_t*)a1 == 0) {\n",
        "  return 1;\n",
        "}\n",
        "if (this == 0 && var1 != 0 && 0 == a1) {\n",
        "  return 2;\n",
        "}\n",
        "if (this->head == 0 || (uint32_t)a1 == 0 || a1 + a2 == 0) {\n",
        "  return 3;\n",
        "}\n",
        "f(\"a1 == 0\");\n",
        "return *(uint32_t*)a1;\n",
    );
    let out = super::finish::spell_nullptr(text);
    assert!(
        out.contains("if (a1 == nullptr || *(uint8_t**)a1 != nullptr)"),
        "{out}"
    );
    assert!(out.contains("return 0;"), "{out}");
    assert!(out.contains("if (a2 == 0 || *(uint32_t*)a1 == 0)"), "{out}");
    assert!(
        out.contains("if (this == nullptr && var1 != nullptr && nullptr == a1)"),
        "{out}"
    );
    assert!(
        out.contains("if (this->head == 0 || (uint32_t)a1 == 0 || a1 + a2 == 0)"),
        "{out}"
    );
    assert!(out.contains("f(\"a1 == 0\");"), "{out}");
    assert!(!out.contains("NULL"), "{out}");
}

/// A byte a call returned, moved into another byte register whose upper
/// bits nothing reads, needs no mask: it fills the lane already.
#[test]
fn a_returned_byte_moved_to_a_byte_register_is_not_masked() {
    let p = crate::program::Program::raw_x64(&[
        0x53, // ASM: push rbx
        0x48, 0x83, 0xec, 0x20, // ASM: sub rsp, 0x20
        0xe8, 0x16, 0x00, 0x00, 0x00, // ASM: call 0x1020
        0x88, 0xc3, // ASM: mov bl, al
        0x0f, 0xb6, 0xcb, // ASM: movzx ecx, bl
        0xe8, 0x0c, 0x00, 0x00, 0x00, // ASM: call 0x1020
        0x48, 0x83, 0xc4, 0x20, // ASM: add rsp, 0x20
        0x5b, // ASM: pop rbx
        0xc3, // ASM: ret
        0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, // ASM: int3 padding
        0x33, 0xc0, // ASM: xor eax, eax (0x1020)
        0x85, 0xc9, // ASM: test ecx, ecx
        0x0f, 0x94, 0xc0, // ASM: sete al
        0xc3, // ASM: ret
    ]);
    let a = crate::analysis::Analysis::compute(&p);
    let o = crate::analysis::Overlay::default();
    let text = super::decompile(&p, &a, &o, 0x1000).expect("decompiles");
    assert!(text.contains("return sub_1020("), "{text}");
    assert!(!text.contains("& 0xff"), "{text}");
}

/// Parentheses left around a bare variable go, unless they are a
/// call's: a mask stripped from `sub_1020(rax & 0xff)` leaves the call.
#[test]
fn unwrapping_a_variable_keeps_call_parentheses() {
    assert_eq!(
        super::unwrap_parens("x = sub_1020(rax) + (rax);", "rax"),
        "x = sub_1020(rax) + rax;"
    );
    assert_eq!(
        super::strip_width("return sub_1020(rax & 0xff);", "rax", &[], Some(8)),
        "return sub_1020(rax);"
    );
}

/// A callee that only loads registers and jumps on to a named function
/// reads as that call, and one that loads a global and returns reads as
/// the global; a field getter stays a call.
#[test]
fn a_callee_that_only_loads_is_read_in_place() {
    let p = crate::program::Program::raw_x64(&[
        0x48, 0x83, 0xec, 0x28, // ASM: sub rsp, 0x28
        0xe8, 0x2f, 0x00, 0x00, 0x00, // ASM: call 0x1038 (the target, so it is a function)
        0xe8, 0x12, 0x00, 0x00, 0x00, // ASM: call 0x1020 (a field getter)
        0x48, 0x8b, 0xc8, // ASM: mov rcx, rax
        0xe8, 0x12, 0x00, 0x00, 0x00, // ASM: call 0x1028 (the forwarder)
        0x48, 0x83, 0xc4, 0x28, // ASM: add rsp, 0x28
        0xc3, // ASM: ret
        0xcc, 0xcc, 0xcc, 0xcc, 0xcc, // ASM: int3 padding
        0x8b, 0x41, 0x08, // ASM: mov eax, [rcx+8] (0x1020)
        0xc3, // ASM: ret
        0xcc, 0xcc, 0xcc, 0xcc, // ASM: int3 padding
        0xba, 0x07, 0x00, 0x00, 0x00, // ASM: mov edx, 7 (0x1028)
        0xe9, 0x06, 0x00, 0x00, 0x00, // ASM: jmp 0x1038
        0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, // ASM: int3 padding
        0x48, 0x8d, 0x04, 0x11, // ASM: lea rax, [rcx+rdx] (0x1038)
        0xc3, // ASM: ret
    ]);
    let a = crate::analysis::Analysis::compute(&p);
    let mut o = crate::analysis::Overlay::default();
    o.names.insert(0x1038, "Sum::Add".to_owned());
    let text = super::decompile(&p, &a, &o, 0x1000).expect("decompiles");
    assert!(text.contains("Sum::Add(sub_1020(a1), 7);"), "{text}");
    assert!(!text.contains("sub_1028("), "{text}");
    assert!(text.contains("sub_1028 is read in place"), "{text}");
}

/// A call to a function whose body is `ret` is no statement, and the
/// header says which callee was left out.
#[test]
fn a_call_to_a_function_that_only_returns_is_left_out() {
    let p = crate::program::Program::raw_x64(&[
        0x48, 0x83, 0xec, 0x28, // ASM: sub rsp, 0x28
        0xba, 0x10, 0x00, 0x00, 0x00, // ASM: mov edx, 16
        0xe8, 0x0a, 0x00, 0x00, 0x00, // ASM: call 0x1018
        0xb8, 0x07, 0x00, 0x00, 0x00, // ASM: mov eax, 7
        0x48, 0x83, 0xc4, 0x28, // ASM: add rsp, 0x28
        0xc3, // ASM: ret
        0xc3, // ASM: ret (0x1018, the empty callee)
    ]);
    let a = crate::analysis::Analysis::compute(&p);
    let o = crate::analysis::Overlay::default();
    let text = super::decompile(&p, &a, &o, 0x1000).expect("decompiles");
    assert!(!text.contains("sub_1018("), "{text}");
    assert!(text.contains("calls to sub_1018 are left out"), "{text}");
    assert!(text.contains("return 7;"), "{text}");
}

/// A byte count the structurer closed as `while (1)` with its exit
/// folded in reads as the `strlen` it is.
#[test]
fn a_strlen_loop_closed_as_while_reads_as_strlen() {
    let text = [
        "rax = 0;",
        "if (a2 != 0) {",
        "  r8 = -1;",
        "  while (1) {",
        "    r8 += 1;",
        "    if (*(uint8_t*)(a2 + r8) != 0) continue;",
        "    rax = r8;",
        "    break;",
        "  }",
        "}",
        "return f(a1, a2, rax);",
    ];
    let mut lines: Vec<String> = text.iter().map(|l| (*l).to_owned()).collect();
    assert!(super::strlen_loops(&mut lines));
    assert_eq!(
        lines.join(
            "
"
        ),
        "rax = 0;
if (a2 != 0) {
  r8 = strlen(a2);
  rax = r8;
}
return f(a1, a2, rax);"
    );
}

/// A signed division by a power of two reads as one, however the
/// compiler rounded it toward zero.
#[test]
fn signed_power_of_two_divisions_read_as_divisions() {
    let dc = |code: &[u8]| {
        let p = crate::program::Program::raw_x64(code);
        let a = crate::analysis::Analysis::compute(&p);
        let o = crate::analysis::Overlay::default();
        super::decompile(&p, &a, &o, 0x1000).expect("decompiles")
    };
    let half = dc(&[
        0x8b, 0xc1, // ASM: mov eax, ecx
        0x99, // ASM: cdq
        0x2b, 0xc2, // ASM: sub eax, edx
        0xd1, 0xf8, // ASM: sar eax, 1
        0xc3, // ASM: ret
    ]);
    assert!(half.contains("a1 / 2;"), "{half}");
    assert!(!half.contains(">> 31"), "{half}");
    let quarter = dc(&[
        0x8b, 0xc1, // ASM: mov eax, ecx
        0x99, // ASM: cdq
        0x83, 0xe2, 0x03, // ASM: and edx, 3
        0x03, 0xc2, // ASM: add eax, edx
        0xc1, 0xf8, 0x02, // ASM: sar eax, 2
        0xc3, // ASM: ret
    ]);
    assert!(quarter.contains("/ 4"), "{quarter}");
    let wide = dc(&[
        0x48, 0x8b, 0xc1, // ASM: mov rax, rcx
        0x48, 0x99, // ASM: cqo
        0x48, 0x2b, 0xc2, // ASM: sub rax, rdx
        0x48, 0xd1, 0xf8, // ASM: sar rax, 1
        0xc3, // ASM: ret
    ]);
    assert!(wide.contains("/ 2"), "{wide}");
    assert!(!wide.contains(">> 63"), "{wide}");
}

/// An integer store of a float's bits reads as the float; a flag word
/// that happens to spell a float stays an integer.
#[test]
fn a_float_stored_as_bits_reads_as_a_float() {
    let p = crate::program::Program::raw_x64(&[
        0xc7, 0x41, 0x10, 0x00, 0x00, 0x80, 0x3f, // ASM: mov dword [rcx+0x10], 0x3f800000
        0xc7, 0x01, 0x00, 0x00, 0x00, 0x40, // ASM: mov dword [rcx], 0x40000000
        0xc7, 0x41, 0x08, 0x43, 0x46, 0x45, 0x52, // ASM: mov dword [rcx+8], 'REFC'
        0xc3, // ASM: ret
    ]);
    let a = crate::analysis::Analysis::compute(&p);
    let o = crate::analysis::Overlay::default();
    let text = super::decompile(&p, &a, &o, 0x1000).expect("decompiles");
    assert!(text.contains("= 1.0f;"), "{text}");
    assert!(!text.contains("0x3f800000"), "{text}");
    assert!(text.contains("0x40000000"), "{text}");
    assert!(!text.contains("= 212"), "{text}");
    let p = crate::program::Program::raw_x64(&[
        0xc7, 0x44, 0x24, 0x08, 0x00, 0x00, 0x00, 0x3f, // ASM: mov dword [rsp+8], 0x3f000000
        0xf3, 0x0f, 0x10, 0x44, 0x24, 0x08, // ASM: movss xmm0, [rsp+8]
        0xf3, 0x0f, 0x59, 0xc1, // ASM: mulss xmm0, xmm1
        0xf3, 0x0f, 0x11, 0x01, // ASM: movss [rcx], xmm0
        0xc3, // ASM: ret
    ]);
    let a = crate::analysis::Analysis::compute(&p);
    let text = super::decompile(&p, &a, &o, 0x1000).expect("decompiles");
    assert!(text.contains("0.5f"), "{text}");
    assert!(!text.contains("0x3f000000"), "{text}");
}

/// A temporary that only copies a register gives way to the register,
/// unless a loop, a write of the register or a label comes between.
#[test]
fn temporaries_that_copy_a_register_fold() {
    let run = |text: &str| {
        let mut lines: Vec<String> = text.lines().map(str::to_owned).collect();
        super::fold_temp_copies(&mut lines);
        lines.join("\n")
    };
    assert_eq!(
        run("rax = f();
tmp_1 = rcx = rax;
rax = 0;
if (tmp_1 != 0) {
  rax = g(rcx);
}
return rax;"),
        "rax = f();
rcx = rax;
rax = 0;
if (rcx != 0) {
  rax = g(rcx);
}
return rax;"
    );
    assert_eq!(
        run("tmp_4 = rbx;
h(tmp_4);"),
        "h(rbx);"
    );
    let looped = "tmp_2 = rbx = rdi;
while (1) {
  f(tmp_2);
  rbx = 5;
}";
    assert_eq!(run(looped), looped);
    let rewritten = "tmp_3 = rsi = rax;
rsi = 0;
g(tmp_3);";
    assert_eq!(run(rewritten), rewritten);
    let labeled = "tmp_5 = rsi = rax;
L_1:
g(tmp_5);";
    assert_eq!(run(labeled), labeled);
}

/// An atomic whose flags nothing reads is a statement: a reference
/// count taken leaves no temporary behind.
///
/// # Panics
///
/// When the atomic is missing or assigned to a temporary.
#[test]
fn an_atomic_nothing_tests_is_a_statement() {
    let p = crate::program::Program::raw_x64(&[
        0xf0, 0xff, 0x41, 0x08, // ASM: lock inc dword [rcx+8]
        0xc3, // ASM: ret
    ]);
    let a = crate::analysis::Analysis::compute(&p);
    let o = crate::analysis::Overlay::default();
    let text = super::decompile(&p, &a, &o, 0x1000).expect("decompiles");
    assert!(text.contains("atomic_add32("), "{text}");
    assert!(!text.contains("tmp_"), "{text}");
}

/// Junk that computes nothing produces no statements.
///
/// An obfuscator pads code with instructions whose effect cancels: a
/// register moved to itself, a zero added, a push and its pop, a `not`
/// twice. A lifter that tracks values rather than instructions drops all
/// of it without a rule per pattern, and this is the test that says so,
/// because the property is easy to lose and invisible when lost.
///
/// # Panics
///
/// When any of the junk reaches the output.
#[test]
fn junk_that_computes_nothing_is_not_rendered() {
    // ASM: mov eax,3; mov rax,rax; add rax,0; or rax,0; and rax,-1;
    //      xor rax,0; push rcx; pop rcx; not rax; not rax; xchg rax,rax;
    //      lea rax,[rax]; nop; ret
    let code: &[u8] = &[
        0xb8, 0x03, 0x00, 0x00, 0x00, 0x48, 0x89, 0xc0, 0x48, 0x83, 0xc0, 0x00, 0x48, 0x83, 0xc8,
        0x00, 0x48, 0x83, 0xe0, 0xff, 0x48, 0x83, 0xf0, 0x00, 0x51, 0x59, 0x48, 0xf7, 0xd0, 0x48,
        0xf7, 0xd0, 0x48, 0x90, 0x48, 0x8d, 0x00, 0x90, 0xc3,
    ];
    let mut bytes = vec![0u8; 0x2000];
    bytes[0x1000..0x1000 + code.len()].copy_from_slice(code);
    let sections = vec![crate::program::Section::mapped(
        ".text", 0x1000, 0x1000, 0x1000, false, true,
    )];
    let p = crate::program::Program::raw(
        bytes,
        crate::program::Arch::X86_64,
        0,
        Some(0x1000),
        sections,
    );
    let a = crate::analysis::Analysis::compute(&p);
    let o = crate::analysis::Overlay::default();
    let text = super::decompile(&p, &a, &o, 0x1000).expect("decompiles");
    for junk in ["rax = rax", "+ 0", "| 0", "^ 0", "~~", "push", "pop", "nop"] {
        assert!(
            !text.contains(junk),
            "{junk} survived:
{text}"
        );
    }
    assert!(
        text.contains("return 3"),
        "the one real effect is missing:
{text}"
    );
}

/// The accesses through a pointer name what it points at.
///
/// One width at offset zero is a pointer to that; anything else is a
/// structure, a lone field away from the start included, and `void *`
/// says so rather than inventing a layout.
#[test]
fn accesses_name_the_pointee() {
    use std::collections::BTreeSet;
    let set = |v: &[usize]| v.iter().copied().collect::<BTreeSet<usize>>();
    let at = |v: &[i64]| v.iter().copied().collect::<BTreeSet<i64>>();
    for (widths, offsets, want) in [
        (set(&[1]), at(&[0]), "uint8_t *"),
        (set(&[2]), at(&[0]), "uint16_t *"),
        (set(&[4]), at(&[0]), "uint32_t *"),
        (set(&[8]), at(&[0]), "uint64_t *"),
        (set(&[8]), at(&[0, 0x18]), "void *"),
        (set(&[4]), at(&[0x14]), "void *"),
        (set(&[8]), at(&[-0x18]), "void *"),
        (set(&[1, 8]), at(&[0]), "void *"),
        (set(&[]), at(&[]), "void *"),
    ] {
        assert_eq!(
            super::pointee_type(&widths, &offsets, None),
            want,
            "{widths:?} at {offsets:?}"
        );
    }
}

/// A block whose whole body was elided folds onto one line.
///
/// Three lines saying "there was a body here" become one, and only when
/// the closing brace belongs to the block that opened.
#[test]
fn an_elided_block_folds_onto_one_line() {
    let mut lines: Vec<String> = [
        "if (a) {",
        "  ...",
        "}",
        "while (b) {",
        "  ...",
        "} else {",
        "  keep();",
        "}",
    ]
    .iter()
    .map(|l| (*l).to_owned())
    .collect();
    super::fold_elided_blocks(&mut lines);
    assert_eq!(
        lines,
        vec![
            "if (a) { ... }",
            "while (b) { ... } else {",
            "  keep();",
            "}",
        ]
    );
}

/// A block with real content is left alone.
#[test]
fn a_block_with_content_is_not_folded() {
    let mut lines: Vec<String> = ["if (a) {", "  work();", "}"]
        .iter()
        .map(|l| (*l).to_owned())
        .collect();
    let before = lines.clone();
    super::fold_elided_blocks(&mut lines);
    assert_eq!(lines, before);
}

/// Identical statements in a row fold to one and a count.
///
/// A label between two of them ends the run, so nothing a `goto` names
/// can be inside what was removed.
#[test]
fn repeated_statements_fold() {
    let mut lines: Vec<String> = [
        "  throw_error(\"append\");",
        "  throw_error(\"append\");",
        "  throw_error(\"append\");",
        "  L_1400:",
        "  throw_error(\"append\");",
    ]
    .iter()
    .map(|l| (*l).to_owned())
    .collect();
    super::fold_repeated_statements(&mut lines);
    assert_eq!(
        lines,
        vec![
            "  throw_error(\"append\");   // and 2 more the same",
            "  L_1400:",
            "  throw_error(\"append\");",
        ]
    );
}

use super::{
    LIFT_TMP_BASE, SKELETON_LINE_MAX, clip_statement, fold_guarded_runs, impure, normalize_temps,
};

/// Builds the three lines of one guarded call over `local`.
///
/// # Arguments
///
/// * `local` - The local the guard and the call name.
/// * `name` - The called function.
fn guarded(local: &str, name: &str) -> Vec<String> {
    vec![
        format!("  if ({local} != &buf) {{"),
        format!("    {name}({local});"),
        String::from("  }"),
    ]
}

/// A run of inlined destructors folds to the call it repeats.
#[test]
fn a_run_of_guarded_calls_folds() {
    let mut lines = vec![String::from("x = 1;")];
    for i in 0..40 {
        lines.extend(guarded(&format!("local_{i}"), "release"));
    }
    lines.push(String::from("return;"));
    fold_guarded_runs(&mut lines);
    assert_eq!(lines.len(), 3, "{lines:?}");
    assert_eq!(lines[1], "  // 40 guarded release(...) calls elided");
}

/// Two guarded calls are left alone; a run must be worth folding.
#[test]
fn a_short_run_of_guarded_calls_is_left_alone() {
    let mut lines = guarded("a", "release");
    lines.extend(guarded("b", "release"));
    let before = lines.clone();
    fold_guarded_runs(&mut lines);
    assert_eq!(lines, before);
}

/// A run calling different functions is not one run.
#[test]
fn guarded_calls_to_different_functions_do_not_fold() {
    let mut lines = guarded("a", "release");
    lines.extend(guarded("b", "flush"));
    lines.extend(guarded("c", "release"));
    let before = lines.clone();
    fold_guarded_runs(&mut lines);
    assert_eq!(lines, before);
}

/// An over-long conditional jump keeps its destination and loses condition.
///
/// Cutting the tail instead leaves `goto L_140...;`, a label that names
/// nowhere and that the dangling-goto check cannot resolve.
#[test]
fn clipping_a_statement_keeps_a_trailing_goto() {
    let mut line = format!("if ({}) goto L_14000a58f;", "a || ".repeat(40));
    assert!(line.len() > SKELETON_LINE_MAX);
    clip_statement(&mut line);
    assert!(line.ends_with(" goto L_14000a58f;"), "{line}");
    assert!(line.contains("..."), "{line}");
}

/// A statement with no `goto` still loses its tail to the cap.
#[test]
fn clipping_a_statement_without_a_goto_cuts_the_tail() {
    let mut line = format!("x = {};", "a + ".repeat(40));
    clip_statement(&mut line);
    assert!(line.ends_with("...;"), "{line}");
    assert!(line.len() <= SKELETON_LINE_MAX, "{line}");
}

/// A statement that already fits is untouched.
#[test]
fn clipping_leaves_a_short_statement_alone() {
    let mut line = String::from("goto L_1000;");
    clip_statement(&mut line);
    assert_eq!(line, "goto L_1000;");
}

/// A call is impure whether or not its name carries template arguments.
///
/// So `drop_returned_values` keeps it as a statement in a `void` function
/// instead of discarding the whole tail call. A plain value stays pure.
#[test]
fn a_templated_call_counts_as_impure() {
    assert!(impure("f(x)"), "plain call not impure");
    assert!(impure("ns::g(a, b)"), "qualified call not impure");
    assert!(
        impure("FrameSync::Data::OwnerSetup<Shared::ModelEntityShared>(rax)"),
        "templated call not impure"
    );
    assert!(
        impure("(rax + 8)->vtable[4](this, 34)"),
        "vtable call not impure"
    );
    assert!(!impure("rax + 1"), "arithmetic wrongly impure");
    assert!(!impure("*(uint32_t*)(this + 0x30)"), "load wrongly impure");
}

/// A leaked lift-pass temporary is renumbered just past the readable ones,
/// while a real `tmp_1` and unrelated tokens are left untouched.
#[test]
fn normalize_temps_renumbers_a_leaked_id() {
    let big = LIFT_TMP_BASE + 1;
    let input = format!("local_4 = tmp_1;\nif (rbx == tmp_{big}) {{\n");
    let out = normalize_temps(&input);
    assert!(
        out.contains("rbx == tmp_2"),
        "leaked id not renumbered: {out}"
    );
    assert!(
        out.contains("local_4 = tmp_1;"),
        "readable temp changed: {out}"
    );
    assert!(
        !out.contains(&format!("tmp_{big}")),
        "raw internal id survived: {out}"
    );
}

/// The same leaked id maps to the same name; distinct ids stay distinct.
#[test]
fn normalize_temps_is_consistent() {
    let a = LIFT_TMP_BASE + 5;
    let b = LIFT_TMP_BASE + 9;
    let input = format!("a = tmp_{a}; b = tmp_{b}; c = tmp_{a};\n");
    let out = normalize_temps(&input);
    assert_eq!(
        out, "a = tmp_1; b = tmp_2; c = tmp_1;\n",
        "inconsistent remap: {out}"
    );
}

/// Text with no leaked temporary is returned unchanged, and a longer
/// identifier ending in `tmp_<n>` is not mistaken for one.
#[test]
fn normalize_temps_leaves_clean_text_alone() {
    let input = "local_4 = tmp_1 + tmp_2; call sub_tmp_3();\n";
    assert_eq!(normalize_temps(input), input);
}
