//! Guard clauses and returns: the arm that fails or returns early stays
//! the `if` body, and the `return` statements a compiler merged into one
//! exit are written in each arm again.

#![expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]

use borer_engine::analysis::decompile::polish;
use borer_engine::analysis::decompile::traces::{Structure, check_structure};
use borer_engine::analysis::{Analysis, Overlay};
use borer_engine::program::Program;

use crate::decompiled::{decompiled, program64, replays_clean, runs_agree};

/// Where the hand-assembled functions start.
const F: u64 = 0x1_4000_1000;

/// A guard clause whose arm only fails writes that arm as the `if` body,
/// the code after it as what follows, whichever side the branch jumps to.
///
/// `f` tests `a1` and falls into a call to `abort`, which never returns,
/// else calls `x`: the text is `if (a1 == 0) { abort(); }` and then `x();`,
/// the shape of the source's guard, not the returning arm nested in the
/// `if` and the failure after it. `g` jumps to the failure and falls into
/// a lone `ret`, and its one caller reads no result: there the `return`
/// is the guard, `if (a1 != 0) return;`, before the failing call.
#[test]
fn a_guard_clause_keeps_its_failing_arm_in_the_if() {
    use borer_engine::program::{Symbol, SymbolKind};
    let mut code = vec![
        0x85, 0xc9, // ASM: test ecx, ecx
        0x75, 0x05, // ASM: jne ok
        0xe8, 0x37, 0x00, 0x00, 0x00, // ASM: call abort
        0xe8, 0x42, 0x00, 0x00, 0x00, // ASM: ok: call x
        0xc3, // ASM: ret
    ];
    code.resize(0x20, 0xcc);
    code.extend([
        0x85, 0xc9, // ASM: test ecx, ecx
        0x74, 0x01, // ASM: je fail
        0xc3, // ASM: ret
        0xe8, 0x16, 0x00, 0x00, 0x00, // ASM: fail: call abort
    ]);
    code.resize(0x40, 0xcc);
    code.push(0xc3); // ASM: ret
    code.resize(0x50, 0xcc);
    code.push(0xc3); // ASM: ret
    code.resize(0x60, 0xcc);
    code.extend([
        0xe8, 0xbb, 0xff, 0xff, 0xff, // ASM: call g
        0x31, 0xc0, // ASM: xor eax, eax
        0xc3, // ASM: ret
    ]);
    let mut p = program64(&code);
    for (name, addr) in [("abort", 0x1_4000_1040), ("x", 0x1_4000_1050)] {
        p.symbols.push(Symbol {
            name: name.to_owned(),
            addr,
            kind: SymbolKind::Local,
        });
    }
    let f = decompiled(&p, 0x1_4000_1000);
    let body = f.split_once("if (").map_or("", |(_, b)| b);
    assert!(
        body.starts_with("a1 == 0) {\n  abort();\n}\nreturn x();"),
        "{f}"
    );
    let g = decompiled(&p, 0x1_4000_1020);
    let body = g.split_once("if (").map_or("", |(_, b)| b);
    assert!(
        body.starts_with("a1 != 0) {\n  return;\n}\nabort();"),
        "{g}"
    );
    let a = Analysis::compute(&p);
    replays_clean(&p, &a, &[0x1_4000_1000, 0x1_4000_1020]);
}

/// A `return` the arms of an `if` chain share, each arm setting the value
/// it hands back, is split into each arm.
///
/// The compiler merged the source's `return` statements into one exit;
/// the split text runs the same statements on every path. A returned
/// frame slot keeps the shared `return`, since a source variable lives
/// there, and so does a tail that calls, whose call would be copied.
#[test]
fn merged_returns_split_into_the_arms() {
    let packs = borer_engine::pack::Packs::default();
    let text = concat!(
        "// signature: uint32_t f(uint32_t a1, uint32_t a2)\n",
        "if (a1 == 0) {\n",
        "  g(1);\n",
        "  var1 = 0;\n",
        "} else {\n",
        "  g(2);\n",
        "  var1 = 1;\n",
        "}\n",
        "return var1;\n",
    );
    let out = polish(text, 64, &packs);
    assert!(
        out.contains("if (a1 == 0) {\n  g(1);\n  return 0;\n}\ng(2);\nreturn 1;\n"),
        "{out}"
    );
    assert_eq!(out.matches("return").count(), 2, "{out}");
    let guard = concat!(
        "// signature: uint32_t f(uint32_t a1, uint32_t a2)\n",
        "var1 = 0;\n",
        "if (a1 == 0) {\n",
        "  var1 = g(a2);\n",
        "}\n",
        "return var1;\n",
    );
    let out = polish(guard, 64, &packs);
    assert!(
        out.contains("if (a1 == 0) {\n  return g(a2);\n}\nreturn var1;"),
        "{out}"
    );
    let slot = concat!(
        "// signature: uint32_t f(uint32_t a1, uint32_t a2)\n",
        "if (a1 == 0) {\n",
        "  local_14 = 3;\n",
        "}\n",
        "return local_14;\n",
    );
    let out = polish(slot, 64, &packs);
    assert_eq!(out.matches("return").count(), 1, "{out}");
    let call = concat!(
        "// signature: uint32_t f(uint32_t a1, uint32_t a2)
",
        "if (a1 == 0) {
",
        "  var1 = 3;
",
        "}
",
        "h(a2);
",
        "return var1;
",
    );
    let out = polish(call, 64, &packs);
    assert_eq!(out.matches("h(a2);").count(), 1, "{out}");
}

/// A code the result zero-extends from its low word is that word where
/// the function returns 64 bits, and the name alone where it returns 32.
///
/// `f` returns `E_OUTOFMEMORY` through `mov eax`, which clears the bits
/// above, or jumps on to `a2`, whose result is all of `rax`: C would
/// sign-extend the `int32_t` HRESULT, so the text returns
/// `(uint32_t)E_OUTOFMEMORY` and runs as the binary does. `g` returns
/// `E_NOTIMPL` the same way and nothing wider, so the name stands. `h`
/// picks one of two such codes with a 64-bit `cmov`, and the choice is
/// the word.
#[test]
fn a_code_a_64_bit_result_zero_extends_is_its_word() {
    let mut code = vec![
        0x85, 0xc9, // ASM: test ecx,ecx
        0x74, 0x02, // ASM: je 0x140001006
        0xff, 0xe2, // ASM: jmp rdx
        0xb8, 0x0e, 0x00, 0x07, 0x80, // ASM: mov eax,0x8007000e
        0xc3, // ASM: ret
    ];
    code.resize(0x20, 0xcc);
    code.extend([
        0xb8, 0x01, 0x40, 0x00, 0x80, // ASM: mov eax,0x80004001
        0xc3, // ASM: ret
    ]);
    code.resize(0x40, 0xcc);
    code.extend([
        0xb8, 0x0e, 0x00, 0x07, 0x80, // ASM: mov eax,0x8007000e
        0xba, 0x01, 0x40, 0x00, 0x80, // ASM: mov edx,0x80004001
        0x85, 0xc9, // ASM: test ecx,ecx
        0x48, 0x0f, 0x45, 0xc2, // ASM: cmovne rax,rdx
        0xc3, // ASM: ret
    ]);
    let p = program64(&code);
    let text = runs_agree(&p, 0x1_4000_1000);
    assert!(text.contains("return (uint32_t)E_OUTOFMEMORY;"), "{text}");
    let narrow = decompiled(&p, 0x1_4000_1020);
    assert!(narrow.contains("return E_NOTIMPL;"), "{narrow}");
    assert!(narrow.contains("uint32_t sub_140001020("), "{narrow}");
    let chosen = runs_agree(&p, 0x1_4000_1040);
    assert!(
        chosen.contains("return (uint32_t)(") && chosen.contains("E_NOTIMPL"),
        "{chosen}"
    );
}

/// The bytes of a function whose three returns share one exit behind a
/// stack canary's check.
///
/// It returns `1` when `a1 & 8`, else `2` when `a1 & 4`, else `3`, each
/// path setting `eax`. The prologue stores `fs:[0x28]` in a slot and passes
/// a frame address to the helper at `+0x80`, so the slot escapes and the
/// check at the exit survives the dataflow; the exit compares the slot with
/// `fs:[0x28]` and calls `+0x90` on a mismatch.
fn canary_exit() -> Vec<u8> {
    let mut code = vec![
        0x53, // ASM: push rbx
        0x48, 0x83, 0xec, 0x28, // ASM: sub rsp,0x28
        0x48, 0x89, 0xcb, // ASM: mov rbx,rcx
        0x64, 0x48, 0x8b, 0x04, 0x25, 0x28, 0x00, 0x00, 0x00, // ASM: mov rax,fs:[0x28]
        0x48, 0x89, 0x44, 0x24, 0x18, // ASM: mov [rsp+0x18],rax
        0x48, 0x8d, 0x7c, 0x24, 0x08, // ASM: lea rdi,[rsp+8]
        0xe8, 0x60, 0x00, 0x00, 0x00, // ASM: call 0x80
        0xf6, 0xc3, 0x08, // ASM: test bl,8
        0x0f, 0x85, 0x28, 0x00, 0x00, 0x00, // ASM: jne 0x51
        0xf6, 0xc3, 0x04, // ASM: test bl,4
        0x0f, 0x85, 0x29, 0x00, 0x00, 0x00, // ASM: jne 0x5b
        0xb8, 0x03, 0x00, 0x00, 0x00, // ASM: mov eax,3
        0x48, 0x8b, 0x54, 0x24, 0x18, // ASM: exit: mov rdx,[rsp+0x18]
        0x64, 0x48, 0x2b, 0x14, 0x25, 0x28, 0x00, 0x00, 0x00, // ASM: sub rdx,fs:[0x28]
        0x0f, 0x85, 0x1a, 0x00, 0x00, 0x00, // ASM: jne 0x65
        0x48, 0x83, 0xc4, 0x28, // ASM: add rsp,0x28
        0x5b, // ASM: pop rbx
        0xc3, // ASM: ret
        0xb8, 0x01, 0x00, 0x00, 0x00, // ASM: arm1: mov eax,1
        0xe9, 0xdc, 0xff, 0xff, 0xff, // ASM: jmp exit
        0xb8, 0x02, 0x00, 0x00, 0x00, // ASM: arm2: mov eax,2
        0xe9, 0xd2, 0xff, 0xff, 0xff, // ASM: jmp exit
        0xe8, 0x26, 0x00, 0x00, 0x00, // ASM: fail: call 0x90
    ];
    code.resize(0x80, 0xcc);
    code.extend([0x31, 0xc0, 0xc3]); // ASM: helper: xor eax,eax; ret
    code.resize(0x90, 0xcc);
    code.extend([0x0f, 0x0b]); // ASM: fail: ud2
    code
}

/// Builds a program of [`canary_exit`]-shaped `code` at [`F`] whose helper
/// at `+0x80` is a plain function and whose failing call at `+0x90` is
/// named `fail`.
///
/// # Arguments
///
/// * `code` - The bytes ([`canary_exit`] or a variant).
/// * `fail` - The name of the function the check calls.
fn named_fail(code: &[u8], fail: &str) -> Program {
    use borer_engine::program::{Symbol, SymbolKind};
    let mut p = program64(code);
    p.symbols.push(Symbol {
        name: fail.to_owned(),
        addr: F + 0x90,
        kind: SymbolKind::Local,
    });
    p
}

/// Each arm of a function whose returns share one exit behind a stack
/// canary's check returns its own value.
///
/// The check makes the exit a fork, so it was the join and the text read
/// `var1 = 1; ... return var1;`. Each arm now takes a copy of the check
/// with the return, and the canary's fold takes all three checks out; the
/// copies are the exit's own code, so the text runs as the binary on every
/// path. The exit stays the join when its failing call is no
/// `__stack_chk_fail` (named `abort`), and when every path returns the same
/// value ([`canary_same`], `7` throughout): the check stays, one `return`.
#[test]
fn a_return_behind_a_canary_check_is_written_in_each_arm() {
    let code = canary_exit();
    let p = named_fail(&code, "__stack_chk_fail");
    let text = decompiled(&p, F);
    assert!(
        text.contains("\n// folded: stack canary in local_10, 3 checks;"),
        "{text}"
    );
    assert!(
        text.contains(
            "\nif ((a1 & 8) != 0) {\n  return 1;\n}\nif ((a1 & 4) != 0) {\n  return 2;\n}\nreturn 3;\n"
        ),
        "{text}"
    );
    let a = Analysis::compute(&p);
    assert_eq!(
        check_structure(&p, &a, &Overlay::default(), F, &text),
        Structure::Agrees,
        "{text}"
    );
    replays_clean(&p, &a, &[F]);
    let joined = |code: &[u8]| {
        let text = decompiled(&named_fail(code, "__stack_chk_fail"), F);
        let returns = text
            .lines()
            .filter(|l| l.trim_start().starts_with("return "))
            .count();
        (returns, text)
    };
    let (n, text) = joined(&canary_same());
    assert_eq!(n, 1, "{text}");
    let abort = decompiled(&named_fail(&code, "abort"), F);
    let returns = abort
        .lines()
        .filter(|l| l.trim_start().starts_with("return "))
        .count();
    assert_eq!(returns, 1, "{abort}");
}

/// The bytes of [`canary_exit`]'s shape where every path returns the same
/// value.
///
/// The result slot at `[rsp+0x10]` is set to `7` once, after the escaping
/// call, and the arms only store distinct dead values to `[rsp+0x20]`, so
/// the exit returns `7` on every path and stays the shared join.
fn canary_same() -> Vec<u8> {
    let mut code = vec![
        0x53, // ASM: push rbx
        0x48, 0x83, 0xec, 0x28, // ASM: sub rsp,0x28
        0x48, 0x89, 0xcb, // ASM: mov rbx,rcx
        0x64, 0x48, 0x8b, 0x04, 0x25, 0x28, 0x00, 0x00, 0x00, // ASM: mov rax,fs:[0x28]
        0x48, 0x89, 0x44, 0x24, 0x18, // ASM: mov [rsp+0x18],rax
        0x48, 0x8d, 0x7c, 0x24, 0x08, // ASM: lea rdi,[rsp+8]
        0xe8, 0x60, 0x00, 0x00, 0x00, // ASM: call 0x80
        0xc7, 0x44, 0x24, 0x10, 0x07, 0x00, 0x00, 0x00, // ASM: mov [rsp+0x10],7
        0xf6, 0xc3, 0x08, // ASM: test bl,8
        0x0f, 0x85, 0x2f, 0x00, 0x00, 0x00, // ASM: jne arm1
        0xf6, 0xc3, 0x04, // ASM: test bl,4
        0x0f, 0x85, 0x33, 0x00, 0x00, 0x00, // ASM: jne arm2
        0xc7, 0x44, 0x24, 0x20, 0x03, 0x00, 0x00, 0x00, // ASM: mov [rsp+0x20],3
        0x8b, 0x44, 0x24, 0x10, // ASM: exit: mov eax,[rsp+0x10]
        0x48, 0x8b, 0x54, 0x24, 0x18, // ASM: mov rdx,[rsp+0x18]
        0x64, 0x48, 0x2b, 0x14, 0x25, 0x28, 0x00, 0x00, 0x00, // ASM: sub rdx,fs:[0x28]
        0x0f, 0x85, 0x20, 0x00, 0x00, 0x00, // ASM: jne fail
        0x48, 0x83, 0xc4, 0x28, // ASM: add rsp,0x28
        0x5b, // ASM: pop rbx
        0xc3, // ASM: ret
        0xc7, 0x44, 0x24, 0x20, 0x01, 0x00, 0x00, 0x00, // ASM: arm1: mov [rsp+0x20],1
        0xe9, 0xd5, 0xff, 0xff, 0xff, // ASM: jmp exit
        0xc7, 0x44, 0x24, 0x20, 0x02, 0x00, 0x00, 0x00, // ASM: arm2: mov [rsp+0x20],2
        0xe9, 0xc8, 0xff, 0xff, 0xff, // ASM: jmp exit
        0xe8, 0x11, 0x00, 0x00, 0x00, // ASM: fail: call 0x90
    ];
    code.resize(0x80, 0xcc);
    code.extend([0x31, 0xc0, 0xc3]); // ASM: helper: xor eax,eax; ret
    code.resize(0x90, 0xcc);
    code.extend([0x0f, 0x0b]); // ASM: fail: ud2
    code
}

/// Each arm of a function whose returns share one epilogue that clears
/// the registers it leaves, as `-fzero-call-used-regs` builds do, returns
/// its own value.
///
/// `f` returns `-3` when `a1 == 0`, `-6` when `a2 > 5`, else `0`, through
/// one exit that clears eight registers no result comes back in, and
/// empties an x87 one, before its `ret`. Those render as nothing, so the exit is as small as a plain
/// `return` and each arm takes a copy; `edx` may carry a second result,
/// and its clearing still counts.
#[test]
fn a_return_behind_cleared_registers_is_written_in_each_arm() {
    let code = [
        0x53, // ASM: push rbx
        0x85, 0xc9, // ASM: test ecx,ecx
        0x74, 0x29, // ASM: je 0x2e
        0x83, 0xfa, 0x05, // ASM: cmp edx,5
        0x77, 0x2b, // ASM: ja 0x35
        0x31, 0xc0, // ASM: xor eax,eax
        0x5b, // ASM: pop rbx
        0x31, 0xc9, // ASM: xor ecx,ecx
        0x45, 0x31, 0xc0, // ASM: xor r8d,r8d
        0x45, 0x31, 0xc9, // ASM: xor r9d,r9d
        0x45, 0x31, 0xd2, // ASM: xor r10d,r10d
        0x45, 0x31, 0xdb, // ASM: xor r11d,r11d
        0x66, 0x0f, 0xef, 0xc9, // ASM: pxor xmm1,xmm1
        0x66, 0x0f, 0xef, 0xd2, // ASM: pxor xmm2,xmm2
        0x66, 0x0f, 0xef, 0xdb, // ASM: pxor xmm3,xmm3
        0xd9, 0xee, // ASM: fldz
        0xdd, 0xd8, // ASM: fstp st(0)
        0x31, 0xd2, // ASM: xor edx,edx
        0xc3, // ASM: ret
        0xb8, 0xfd, 0xff, 0xff, 0xff, // ASM: mov eax,-3
        0xeb, 0xd7, // ASM: jmp 0xc
        0xb8, 0xfa, 0xff, 0xff, 0xff, // ASM: mov eax,-6
        0xeb, 0xd0, // ASM: jmp 0xc
    ];
    let p = program64(&code);
    let text = runs_agree(&p, F);
    assert!(text.contains("\nif (a1 == 0) {\n  return "), "{text}");
    assert_eq!(text.matches("return ").count(), 3, "{text}");
    assert!(!text.contains("else"), "{text}");
    replays_clean(&p, &Analysis::compute(&p), &[F]);
}
