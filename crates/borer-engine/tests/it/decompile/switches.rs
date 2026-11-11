//! Switches, jump tables, compare ladders and dispatch loops.

use super::*;

/// A 32-bit load widened into a 64-bit range ladder keeps its unsigned
/// reading.
///
/// `mov eax,[rdx]; add rax,-29; sub rax,2; jb` tests the widened value for
/// 29 or 30, and the wrap the compare's unsigned treatment adds says so
/// whatever the cast inside spells.
///
/// # Panics
///
/// When the range reads signed.
#[test]
fn a_widened_range_ladder_compares_unsigned() {
    use borer_engine::program::{Arch, BinaryFormat, Program, Section};
    let code = [
        0x8b, 0x02, // ASM: mov eax,[rdx]
        0x48, 0x83, 0xc0, 0xe3, // ASM: add rax,-29
        0x48, 0x83, 0xe8, 0x02, // ASM: sub rax,2
        0x72, 0x03, // ASM: jb +3
        0x31, 0xc0, // ASM: xor eax,eax
        0xc3, // ASM: ret
        0xb8, 0x01, 0x00, 0x00, 0x00, // ASM: mov eax,1
        0xc3, // ASM: ret
    ];
    let mut bytes = vec![0u8; 0x1000];
    bytes[..code.len()].copy_from_slice(&code);
    let mut p = Program::raw(
        bytes,
        Arch::X86_64,
        0x400_000,
        Some(0x401_000),
        vec![Section::mapped(".text", 0x401_000, 0, 0x1000, false, true)],
    );
    p.format = BinaryFormat::Pe;
    let text = runs_agree(&p, 0x401_000);
    assert!(
        text.contains("(uint64_t)") && text.contains("< 2"),
        "the unsigned wrap: {text}"
    );
}

/// `D` becomes a `switch (a1)` (the `movsxd` on the index must not leak)
/// with all cases, their bodies, and the default bound check.
#[test]
fn switch_function_cases() {
    let out = dc(0x1060);
    assert!(
        out.contains("switch (a1)"),
        "no switch construct (movsxd on the index must not leak):
{out}"
    );
    assert!(
        out.contains("case 0:"),
        "no case 0:
{out}"
    );
    assert!(
        out.contains("case 3:"),
        "no case 3:
{out}"
    );
    assert!(
        out.contains("return 1;") && out.contains("return 4;"),
        "case bodies missing:
{out}"
    );
    assert!(
        out.contains("default: {"),
        "default bound-check lost:
{out}"
    );
}

/// A compare ladder renders as a run of early returns, not nested levels.
///
/// `DEEP`'s seventy-two levels each test a byte and return a constant when
/// it is set; every level's body ends in a return, so each `if` inverts to
/// `if (*(uint8_t*)(a1 + k) != 0) { return k; }` and the next level follows
/// at the same indentation.
#[test]
fn compare_ladders_render_as_early_returns() {
    let out = dc(0x4300);
    assert!(out.contains("if (*(uint8_t*)a1 != 0) {"), "{out}");
    assert!(
        out.lines().all(|l| l.len() - l.trim_start().len() <= 2),
        "nested deeper than one level:\n{out}"
    );
}

/// Jump tables the jump's operand names, and tables of offsets from a base.
///
/// `JTG` jumps through `[rax * 8 + T]`, the shape GCC emits, and `JTM`
/// loads a 32-bit offset from a table a `lea` addresses and adds the base
/// back, the shape MSVC emits. Both recover as a switch over three cases.
#[test]
fn relative_and_operand_named_jump_tables_resolve() {
    let p = fixture();
    let a = Analysis::compute(&p);
    assert_eq!(
        a.jump_tables.get(&0x4cb7).map(Vec::as_slice),
        Some(&[0x4cbe, 0x4cc4, 0x4cca][..])
    );
    assert_eq!(
        a.jump_tables.get(&0x4cf6).map(Vec::as_slice),
        Some(&[0x4cf8, 0x4cfe, 0x4d04][..])
    );
}

/// A switch arm that jumps to a returning tail takes the tail in place.
///
/// A compiler's `ToString` dispatches every case to its own one-line
/// return; leaving the jumps in place would put a `goto` on every arm and
/// the answers below the switch.
#[test]
fn switch_arms_take_the_tail_they_jump_to() {
    let text = concat!(
        "switch (a1) {\n",
        "case 0: goto L_1;\n",
        "case 1: goto L_2;\n",
        "case 2: goto L_3;\n",
        "}\n",
        "L_1:\n",
        "return \"zero\";\n",
        "L_2:\n",
        "return \"one\";\n",
        "L_3:\n",
        "sub_1000(a1);\n",
        "return 0;\n",
    );
    let out = cleanup(text);
    assert!(out.contains("case 0: return \"zero\";"), "{out}");
    assert!(out.contains("case 1: return \"one\";"), "{out}");
    assert!(
        out.contains("case 2: {\n  sub_1000(a1);\n  return 0;\n}"),
        "{out}"
    );
    assert!(!out.contains("goto"), "{out}");
}

/// A dispatch through a byte index table switches on the value.
///
/// `JTX`'s byte table folds five values onto two bodies, and the case
/// labels the resolver produces are those values; writing the switch on the
/// byte load would make `case 1` mean the second slot of the jump table
/// rather than the value 1.
#[test]
fn a_switch_through_an_index_table_reads_the_value() {
    let out = dc(0x4f20);
    assert!(!out.contains("uint8_t*"), "{out}");
    assert!(out.contains("case 0: case 2: case 4:"), "{out}");
    assert!(out.contains("case 1: case 3:"), "{out}");
}

/// A switch arm whose block is already written keeps its case.
///
/// `SW` reaches its arms before the dispatch is printed, so every arm the
/// table names is already on the page by then. Skipping those arms left an
/// empty `switch` and two blocks nothing reached. Each block hands its own
/// number to 0x553f, so a missing one is plain.
#[test]
fn a_switch_arm_already_written_keeps_its_case() {
    let out = dc(0x5500);
    for n in 1..=4 {
        assert!(
            out.contains(&format!("({n})")),
            "block {n} is missing: {out}"
        );
    }
    assert!(out.contains("case "), "the switch has no arms: {out}");
}

/// A switch on a parameter decompiled under a value of it reads as that
/// one case: `D`'s table sends 2 to the case returning 3.
#[test]
fn a_scenario_takes_one_case_of_a_switch() {
    let p = fixture();
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let all = decompile(&p, &a, &o, 0x1060).unwrap_or_default();
    assert!(all.contains("switch"), "{all}");
    let two = decompile_scenario(&p, &a, &o, 0x1060, &[(0, 2)]).unwrap_or_default();
    assert!(two.starts_with("// scenario: a1 = 2; "), "{two}");
    assert!(!two.contains("switch"), "{two}");
    assert!(two.contains("return 3;"), "{two}");
    assert!(!two.contains("return 4;"), "{two}");
}

/// A compare ladder on one value with three or more bodies is a `switch`,
/// whether the compiler compared the value each time or counted it down.
#[test]
fn a_compare_ladder_is_a_switch() {
    let cmp: &[u8] = &[
        0x83, 0xf9, 0x01, 0x74, 0x0d, 0x83, 0xf9, 0x02, 0x74, 0x0e, 0x83, 0xf9, 0x03, 0x74, 0x0f,
        0x31, 0xc0, 0xc3, 0xb8, 0x0a, 0x00, 0x00, 0x00, 0xc3, 0xb8, 0x14, 0x00, 0x00, 0x00, 0xc3,
        0xb8, 0x1e, 0x00, 0x00, 0x00, 0xc3,
    ];
    let sub: &[u8] = &[
        0x83, 0xe9, 0x01, 0x74, 0x0d, 0x83, 0xe9, 0x01, 0x74, 0x0e, 0x83, 0xe9, 0x01, 0x74, 0x0f,
        0x31, 0xc0, 0xc3, 0xb8, 0x0a, 0x00, 0x00, 0x00, 0xc3, 0xb8, 0x14, 0x00, 0x00, 0x00, 0xc3,
        0xb8, 0x1e, 0x00, 0x00, 0x00, 0xc3,
    ];
    for code in [cmp, sub] {
        let p = program64(code);
        let text = decompiled(&p, 0x1_4000_1000);
        assert!(!text.contains("goto"), "{text}");
        assert!(text.contains("switch (a1)"), "{text}");
        for label in ["case 1:", "case 2:", "case 3:", "default:"] {
            assert!(text.contains(label), "{label}\n{text}");
        }
        assert!(text.contains("return 20;"), "{text}");
    }
}

/// A compare tree whose misses land in two different blocks (a range
/// split to one, the last compare's miss to another) is no `switch`, which
/// has one default: it stays an `if` chain.
#[test]
fn a_tree_with_two_residual_leaves_stays_an_if_chain() {
    let code: &[u8] = &[
        0x83, 0xf9, 0x01, 0x74, 0x12, 0x83, 0xf9, 0x0a, 0x7f, 0x13, 0x83, 0xf9, 0x02, 0x74, 0x14,
        0x83, 0xf9, 0x03, 0x74, 0x15, 0x31, 0xc0, 0xc3, 0xb8, 0x0a, 0x00, 0x00, 0x00, 0xc3, 0xb8,
        0x63, 0x00, 0x00, 0x00, 0xc3, 0xb8, 0x14, 0x00, 0x00, 0x00, 0xc3, 0xb8, 0x1e, 0x00, 0x00,
        0x00, 0xc3,
    ];
    let p = program64(code);
    let text = decompiled(&p, 0x1_4000_1000);
    assert!(!text.contains("switch ("), "{text}");
    assert!(text.contains("return 99;"), "{text}");
    assert!(text.contains("return 30;"), "{text}");
}

/// Inside a `do` loop, a switch arm that jumps to the loop's condition
/// `continue`s.
///
/// The jump passes through the switch, which only a `break` binds to, and
/// the condition is where a do-while's `continue` goes.
#[test]
fn a_switch_arm_jumping_to_the_latch_continues() {
    let code: &[u8] = &[
        0x31, 0xc0, 0x8b, 0x0a, 0x83, 0xf9, 0x01, 0x74, 0x0e, 0x83, 0xf9, 0x02, 0x74, 0x0e, 0x83,
        0xf9, 0x03, 0x74, 0x0e, 0x01, 0xc8, 0xeb, 0x0d, 0x83, 0xc0, 0x0a, 0xeb, 0x08, 0x83, 0xc0,
        0x14, 0xeb, 0x0c, 0x83, 0xc0, 0x1e, 0xff, 0xc0, 0x48, 0x83, 0xc2, 0x04, 0x41, 0xff, 0xc0,
        0x45, 0x39, 0xc8, 0x75, 0xd0, 0xc3,
    ];
    let p = program64(code);
    let text = decompiled(&p, 0x1_4000_1000);
    assert!(!text.contains("goto"), "{text}");
    assert!(text.contains("switch ("), "{text}");
    assert!(text.contains("continue;"), "{text}");
    assert!(text.contains("} while ("), "{text}");
}

/// A call into a dispatch thunk is the call through its register.
///
/// A thunk that only jumps through `rax` (the CFG dispatcher) is called
/// as the call through `rax`, with the arguments set for it, and a call
/// through a read-only pointer to a function that only returns (the CFG
/// check's default) is no statement.
///
/// `sub rsp,0x28; lea rax,[target]; mov ecx,9; call [check]; call
/// dispatch; add rsp,0x28; ret` with `dispatch` `jmp rax`, `target` `mov
/// eax,ecx; ret`, and `check` holding the address of a bare `ret`.
#[test]
fn a_dispatch_thunk_call_is_the_call_through_its_register() {
    let mut code = vec![
        0x48, 0x83, 0xec, 0x28, 0x48, 0x8d, 0x05, 0x55, 0x00, 0x00, 0x00, 0xb9, 0x09, 0x00, 0x00,
        0x00, 0xff, 0x15, 0xea, 0x0f, 0x00, 0x00, 0xe8, 0x25, 0x00, 0x00, 0x00, 0x48, 0x83, 0xc4,
        0x28, 0xc3,
    ];
    code.resize(0x40, 0xcc);
    code.extend_from_slice(&[0xff, 0xe0]);
    code.resize(0x60, 0xcc);
    code.extend_from_slice(&[0x89, 0xc8, 0xc3]);
    code.resize(0x70, 0xcc);
    code.push(0xc3);
    let p = program64_with_data(&code, &0x1_4000_1070u64.to_le_bytes());
    let text = decompiled(&p, 0x1_4000_1000);
    assert!(text.contains("(9);"), "{text}");
    assert!(!text.contains("sub_140001040()"), "{text}");
    assert!(text.contains("only jumps through rax"), "{text}");
    assert!(text.contains("are left out"), "{text}");
}

/// A `SwitchToFiber` call is an ordinary call: one argument, no result,
/// and the text after the swap stays.
///
/// The swap suspends the current fiber and resumes another, and when
/// control comes back it comes back at the call itself, so the block's
/// tail may still run on resume and belongs in the text. Unlike
/// `longjmp` the callee is not noreturn, and the prototype's single
/// parameter keeps the call from padding to the register slots: `mov rcx,
/// rax; call [SwitchToFiber]; mov eax,7; ret` renders one argument and
/// keeps the `return`.
#[test]
fn a_switchtofiber_call_keeps_its_tail_under_one_argument() {
    let mut code = vec![
        0x48, 0x83, 0xec, 0x28, // ASM: sub rsp, 28h
        0x31, 0xc9, // ASM: xor ecx, ecx
        0x48, 0x8d, 0x15, 0x1c, 0x00, 0x00, 0x00, // ASM: lea rdx, [0x140001029]
        0x45, 0x31, 0xc0, // ASM: xor r8d, r8d
        0xff, 0x15, 0xea, 0x0f, 0x00, 0x00, // ASM: call [0x140002000]
        0x48, 0x89, 0xc1, // ASM: mov rcx, rax
        0xff, 0x15, 0xe9, 0x0f, 0x00, 0x00, // ASM: call [0x140002008]
        0xb8, 0x07, 0x00, 0x00, 0x00, // ASM: mov eax, 7
        0x48, 0x83, 0xc4, 0x28, // ASM: add rsp, 28h
        0xc3, // ASM: ret
    ];
    assert_eq!(code.len(), 0x29);
    code.extend_from_slice(&[0xb8, 0x2a, 0x00, 0x00, 0x00, 0xc3]); // ASM: mov eax, 42; ret
    let p = program64_with_imports(
        &code,
        &[0; 0x20],
        &[
            (0x1_4000_2000, "kernel32.dll!CreateFiber"),
            (0x1_4000_2008, "kernel32.dll!SwitchToFiber"),
        ],
    );
    let text = decompiled(&p, 0x1_4000_1000);
    let swap = text
        .lines()
        .find(|l| l.contains("SwitchToFiber("))
        .unwrap_or_default();
    let args = swap
        .split_once("SwitchToFiber(")
        .map_or("", |(_, rest)| rest);
    let mut depth = 0usize;
    let mut padded = false;
    for c in args.chars() {
        match c {
            '(' => depth += 1,
            ')' if depth == 0 => break,
            ')' => depth -= 1,
            ',' if depth == 0 => padded = true,
            _ => {}
        }
    }
    assert!(!swap.is_empty(), "{text}");
    assert!(!padded, "padded arguments: {swap}");
    assert!(
        text.contains("return 7;"),
        "the tail after the swap was dropped:\n{text}"
    );
}

/// A bounded table of offsets from the function's start, not from the
/// table, resolves through the register the jump adds back.
///
/// `cmp ecx,3; ja D; lea r8,[F]; lea rdx,[T]; movsxd rax,[rdx+rcx*4]; add
/// rax,r8; jmp rax`: the base is another label than the table, so reading
/// the entries as offsets from the table lands every case in data.
#[test]
fn a_rel32_table_relative_to_another_label_resolves() {
    const F: u64 = 0x1_4000_1000;
    let code: &[u8] = &[
        0x83, 0xf9, 0x03, // ASM: cmp ecx,3
        0x77, 0x2f, // ASM: ja 0x34
        0x4c, 0x8d, 0x05, 0xf4, 0xff, 0xff, 0xff, // ASM: lea r8,[rip-0xc]
        0x48, 0x8d, 0x15, 0xed, 0x0f, 0x00, 0x00, // ASM: lea rdx,[rip+0xfed]
        0x48, 0x63, 0x04, 0x8a, // ASM: movsxd rax,dword [rdx+rcx*4]
        0x4c, 0x01, 0xc0, // ASM: add rax,r8
        0xff, 0xe0, // ASM: jmp rax
        0xb8, 0x0a, 0x00, 0x00, 0x00, // ASM: mov eax,10
        0xc3, // ASM: ret
        0xb8, 0x14, 0x00, 0x00, 0x00, // ASM: mov eax,20
        0xc3, // ASM: ret
        0xb8, 0x1e, 0x00, 0x00, 0x00, // ASM: mov eax,30
        0xc3, // ASM: ret
        0xb8, 0x28, 0x00, 0x00, 0x00, // ASM: mov eax,40
        0xc3, // ASM: ret
        0x31, 0xc0, // ASM: xor eax,eax
        0xc3, // ASM: ret
    ];
    let cases = [F + 0x1c, F + 0x22, F + 0x28, F + 0x2e];
    let p = program64_with_data(code, &rel32_entries(F, &cases));
    let a = Analysis::compute(&p);
    assert_eq!(
        a.jump_tables.get(&(F + 0x1a)).map(Vec::as_slice),
        Some(&cases[..])
    );
    let text = decompiled(&p, F);
    assert!(!text.contains("goto *"), "{text}");
    assert!(text.contains("switch (a1)"), "{text}");
    assert!(text.contains("return 40;"), "{text}");
    replays_clean(&p, &a, &[F]);
}

/// A table no compare bounds is read while its entries land on code of the
/// function, and ends at the first that does not.
///
/// `movzx eax,byte [rcx]; lea rdx,[T]; movsxd rax,[rdx+rax*4]; add rax,rdx;
/// jmp rax` indexes four rel32 entries with a byte read from memory, and
/// the zero after them reads as the table itself, which is data.
#[test]
fn an_unbounded_rel32_table_ends_at_its_first_invalid_entry() {
    const F: u64 = 0x1_4000_1000;
    const T: u64 = 0x1_4000_2000;
    let code: &[u8] = &[
        0x0f, 0xb6, 0x01, // ASM: movzx eax,byte [rcx]
        0x48, 0x8d, 0x15, 0xf6, 0x0f, 0x00, 0x00, // ASM: lea rdx,[rip+0xff6]
        0x48, 0x63, 0x04, 0x82, // ASM: movsxd rax,dword [rdx+rax*4]
        0x48, 0x01, 0xd0, // ASM: add rax,rdx
        0xff, 0xe0, // ASM: jmp rax
        0xb8, 0x0a, 0x00, 0x00, 0x00, // ASM: mov eax,10
        0xc3, // ASM: ret
        0xb8, 0x14, 0x00, 0x00, 0x00, // ASM: mov eax,20
        0xc3, // ASM: ret
        0xb8, 0x1e, 0x00, 0x00, 0x00, // ASM: mov eax,30
        0xc3, // ASM: ret
        0xb8, 0x28, 0x00, 0x00, 0x00, // ASM: mov eax,40
        0xc3, // ASM: ret
    ];
    let cases = [F + 0x13, F + 0x19, F + 0x1f, F + 0x25];
    let p = program64_with_data(code, &rel32_entries(T, &cases));
    let a = Analysis::compute(&p);
    assert_eq!(
        a.jump_tables.get(&(F + 0x11)).map(Vec::as_slice),
        Some(&cases[..])
    );
    let text = decompiled(&p, F);
    assert!(!text.contains("goto *"), "{text}");
    assert!(text.contains("switch ("), "{text}");
    assert!(text.contains("return 40;"), "{text}");
    replays_clean(&p, &a, &[F]);
}

/// A bytecode interpreter whose loop fetches an opcode, jumps through an
/// unbounded rel32 table and has its handlers jump back is one function
/// and one dispatch loop.
///
/// `xor eax,eax; lea r8,[T]; L: movzx edx,byte [rcx]; inc rcx; movsxd
/// rdx,[r8+rdx*4]; add rdx,r8; jmp rdx`, then a `ret` handler for opcode 0
/// and four that change `eax` and `jmp L`.
#[test]
fn an_interpreter_over_an_unbounded_rel32_table_is_a_dispatch_loop() {
    const F: u64 = 0x1_4000_1000;
    const T: u64 = 0x1_4000_2000;
    let code: &[u8] = &[
        0x31, 0xc0, // ASM: xor eax,eax
        0x4c, 0x8d, 0x05, 0xf7, 0x0f, 0x00, 0x00, // ASM: lea r8,[rip+0xff7]
        0x0f, 0xb6, 0x11, // ASM: movzx edx,byte [rcx]
        0x48, 0xff, 0xc1, // ASM: inc rcx
        0x49, 0x63, 0x14, 0x90, // ASM: movsxd rdx,dword [r8+rdx*4]
        0x4c, 0x01, 0xc2, // ASM: add rdx,r8
        0xff, 0xe2, // ASM: jmp rdx
        0xc3, // ASM: ret
        0xff, 0xc0, // ASM: inc eax
        0xeb, 0xec, // ASM: jmp 0x09
        0x83, 0xc0, 0x02, // ASM: add eax,2
        0xeb, 0xe7, // ASM: jmp 0x09
        0x01, 0xc0, // ASM: add eax,eax
        0xeb, 0xe3, // ASM: jmp 0x09
        0xff, 0xc8, // ASM: dec eax
        0xeb, 0xdf, // ASM: jmp 0x09
    ];
    let handlers = [F + 0x18, F + 0x19, F + 0x1d, F + 0x22, F + 0x26];
    let p = program64_with_data(code, &rel32_entries(T, &handlers));
    let a = Analysis::compute(&p);
    assert_eq!(
        a.jump_tables.get(&(F + 0x16)).map(Vec::as_slice),
        Some(&handlers[..])
    );
    let f = a.function(F);
    assert!(
        f.is_some_and(|f| handlers
            .iter()
            .all(|h| f.blocks.iter().any(|b| b.start == *h))),
        "a handler is outside the interpreter"
    );
    let o = Overlay::default();
    let list = borer_engine::analysis::render::vm_dispatch_tsv(&p, &a, &o, "").unwrap();
    assert!(list.starts_with("# 1 dispatch loop found"), "{list}");
    let text = decompiled(&p, F);
    assert!(!text.contains("goto *"), "{text}");
    assert!(text.contains("switch ("), "{text}");
    replays_clean(&p, &a, &[F]);
}

/// A table no compare bounds ends where the next table begins, even when
/// the next table's entries, read from the first one's base, land on code.
///
/// Two dispatches each `movzx eax,byte [...]; lea rdx,[T]; movsxd
/// rax,[rdx+rax*4]; add rax,rdx; jmp rax`, over tables of two entries laid
/// end to end. Read from the first base, the second table's entries name
/// the second `jmp rax` and the last byte of a `mov`, and the first table
/// once took both as cases.
#[test]
fn an_unbounded_rel32_table_ends_where_the_next_table_begins() {
    const F: u64 = 0x1_4000_1000;
    const T: u64 = 0x1_4000_2000;
    let code: &[u8] = &[
        0x0f, 0xb6, 0x01, // ASM: movzx eax,byte [rcx]
        0x48, 0x8d, 0x15, 0xf6, 0x0f, 0x00, 0x00, // ASM: lea rdx,[rip+0xff6]
        0x48, 0x63, 0x04, 0x82, // ASM: movsxd rax,dword [rdx+rax*4]
        0x48, 0x01, 0xd0, // ASM: add rax,rdx
        0xff, 0xe0, // ASM: jmp rax
        0x0f, 0xb6, 0x41, 0x01, // ASM: movzx eax,byte [rcx+1]
        0x48, 0x8d, 0x15, 0xea, 0x0f, 0x00, 0x00, // ASM: lea rdx,[rip+0xfea]
        0x48, 0x63, 0x04, 0x82, // ASM: movsxd rax,dword [rdx+rax*4]
        0x48, 0x01, 0xd0, // ASM: add rax,rdx
        0xff, 0xe0, // ASM: jmp rax
        0xb8, 0x01, 0x00, 0x00, 0x00, // ASM: mov eax,1
        0xc3, // ASM: ret
        0xb8, 0x02, 0x00, 0x00, 0x00, // ASM: mov eax,2
        0xc3, // ASM: ret
        0xb8, 0x03, 0x00, 0x00, 0x00, // ASM: mov eax,3
        0xc3, // ASM: ret
    ];
    let first = [F + 0x13, F + 0x27];
    let second = [F + 0x2d, F + 0x33];
    let mut data = rel32_entries(T, &first);
    data.extend(rel32_entries(T + 8, &second));
    let p = program64_with_data(code, &data);
    let a = Analysis::compute(&p);
    assert_eq!(
        a.jump_tables.get(&(F + 0x11)).map(Vec::as_slice),
        Some(&first[..])
    );
    assert_eq!(
        a.jump_tables.get(&(F + 0x25)).map(Vec::as_slice),
        Some(&second[..])
    );
    replays_clean(&p, &a, &[F]);
}
