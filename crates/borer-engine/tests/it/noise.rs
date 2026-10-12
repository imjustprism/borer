//! Lines the pseudo-C prints that say nothing about the program: phantom
//! second results, float results nobody reads, imports declared as
//! variables, dead stores and the spills of a variadic prologue.

#![expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]

use crate::decompiled::decompiled;
use crate::raw::image;

use borer_engine::analysis::Analysis;
use borer_engine::analysis::decompile::cleanup;
use borer_engine::program::Arch;

/// Pads `code` with `int3` up to `len` bytes, where the next function
/// starts.
///
/// # Arguments
///
/// * `code` - The bytes so far.
/// * `len` - The offset the next function starts at.
fn pad(code: &mut Vec<u8>, len: usize) {
    code.resize(len, 0xcc);
}

/// A call site whose scan runs out before anything reads or writes `rdx`
/// is no evidence of a second result.
///
/// `call PAIR` followed by thirteen `nop`s and `ret`, where `PAIR` is `mov
/// eax,1; mov edx,2; ret`: the twelve-instruction scan after the call
/// loses the site, and a lost site made `PAIR` hand back `rdx`, which put
/// a phantom `rdx = PAIR__rdx()` beside every call to it.
#[test]
fn a_call_site_the_scan_loses_is_no_second_result() {
    let mut code = vec![
        0xe8, 0x1b, 0x00, 0x00, 0x00, // ASM: call 0x401020
    ];
    code.extend_from_slice(&[0x90; 13]); // ASM: nop (thirteen times)
    code.push(0xc3); // ASM: ret
    pad(&mut code, 0x20);
    code.extend_from_slice(&[
        0xb8, 0x01, 0x00, 0x00, 0x00, // ASM: mov eax, 1
        0xba, 0x02, 0x00, 0x00, 0x00, // ASM: mov edx, 2
        0xc3, // ASM: ret
    ]);
    let p = image(Arch::X86_64, &code, &[]);
    let a = Analysis::compute(&p);
    let pair = a.function(0x401020).expect("the callee");
    assert!(!pair.hands_back_rdx, "a lost site made a second result");
}

/// A caller that reads only `rax` after a call shows no second result,
/// though another caller of the same function reads `rdx`.
///
/// `PAIR` is `lea rax,[rcx+1]; mov edx,7; ret`; the first caller ends
/// `call PAIR; mov rax,rdx; ret`, the second `call PAIR; add rax,1; ret`,
/// whose `ret` hands back `rax` alone: the text wrote `rdx =
/// PAIR__rdx();` there too.
#[test]
fn a_caller_reading_only_rax_shows_no_second_result() {
    let mut code = vec![
        0xe8, 0x1b, 0x00, 0x00, 0x00, // ASM: call 0x401020
        0x48, 0x89, 0xd0, // ASM: mov rax, rdx
        0xc3, // ASM: ret
    ];
    pad(&mut code, 0x20);
    code.extend_from_slice(&[
        0x48, 0x8d, 0x41, 0x01, // ASM: lea rax, [rcx+1]
        0xba, 0x07, 0x00, 0x00, 0x00, // ASM: mov edx, 7
        0xc3, // ASM: ret
    ]);
    pad(&mut code, 0x40);
    code.extend_from_slice(&[
        0xe8, 0xdb, 0xff, 0xff, 0xff, // ASM: call 0x401020
        0x48, 0x83, 0xc0, 0x01, // ASM: add rax, 1
        0xc3, // ASM: ret
    ]);
    let p = image(Arch::X86_64, &code, &[]);
    let reader = decompiled(&p, 0x401000);
    assert!(reader.contains("sub_401020__rdx("), "{reader}");
    let other = decompiled(&p, 0x401040);
    assert!(!other.contains("__rdx"), "{other}");
}

/// A second result nothing reads goes like any other dead assignment: it
/// only names what the call on the line before left in `rdx`.
#[test]
fn a_dead_second_result_is_dropped() {
    let body = "f(rsi, a1);\nrdx = f__rdx(rsi, rdx);\nreturn rax;\n";
    let text = cleanup(body);
    assert!(!text.contains("__rdx"), "{text}");
    assert!(text.contains("f(rsi, a1);"), "{text}");
}

/// The caller of the float tests, whose first call ends its block.
///
/// `sub rsp,0x28; test ecx,ecx; je L; call 0x401020; L: call 0x401040; add
/// rsp,0x28; ret`: only the liveness after the first call says what reads
/// its result.
const FLOAT_CALLER: [u8; 23] = [
    0x48, 0x83, 0xec, 0x28, // ASM: sub rsp, 0x28
    0x85, 0xc9, // ASM: test ecx, ecx
    0x74, 0x05, // ASM: je 0x40100d
    0xe8, 0x13, 0x00, 0x00, 0x00, // ASM: call 0x401020
    0xe8, 0x2e, 0x00, 0x00, 0x00, // ASM: call 0x401040
    0x48, 0x83, 0xc4, 0x28, // ASM: add rsp, 0x28
    0xc3, // ASM: ret
];

/// The second callee of [`FLOAT_CALLER`] at 0x401040: `mov eax,ecx; ret`.
const FLOAT_NEXT: [u8; 3] = [
    0x89, 0xc8, // ASM: mov eax, ecx
    0xc3, // ASM: ret
];

/// A call that returns no float binds no `xmm0` because a later call may
/// take a float argument there.
///
/// [`FLOAT_CALLER`] calls `xor eax,eax; ret` and then a function reading
/// `ecx`: every call reads `xmm0`..`xmm3` in case its callee takes a
/// float, which made the first call's result `xmm0 = sub_401020();` with
/// a `double xmm0;` declared for it.
#[test]
fn a_call_before_another_binds_no_float_result() {
    let mut code = FLOAT_CALLER.to_vec();
    pad(&mut code, 0x20);
    code.extend_from_slice(&[
        0x31, 0xc0, // ASM: xor eax, eax
        0xc3, // ASM: ret
    ]);
    pad(&mut code, 0x40);
    code.extend_from_slice(&FLOAT_NEXT);
    let p = image(Arch::X86_64, &code, &[]);
    let text = decompiled(&p, 0x401000);
    assert!(text.contains("sub_401020();"), "{text}");
    assert!(!text.contains("xmm0"), "{text}");
}

/// A callee known to return a float still binds its result where a later
/// call takes it.
///
/// `sub rsp,0x28; test ecx,ecx; je E; call F; jmp J; E: call F; J: call
/// G; add rsp,0x28; ret`, where `F` is `movsd xmm0,[2.5]; ret`, whose other
/// caller converts the `xmm0` it leaves (`call F; cvttsd2si eax,xmm0;
/// ret`), so it returns a `double`, and `G` is that conversion: both arms
/// bind the result, the first though only the jump after its call is left
/// in its block.
#[test]
fn a_float_callee_still_binds_its_result() {
    let mut code = vec![
        0x48, 0x83, 0xec, 0x28, // ASM: sub rsp, 0x28
        0x85, 0xc9, // ASM: test ecx, ecx
        0x74, 0x07, // ASM: je 0x40100f
        0xe8, 0x13, 0x00, 0x00, 0x00, // ASM: call 0x401020
        0xeb, 0x05, // ASM: jmp 0x401014
        0xe8, 0x0c, 0x00, 0x00, 0x00, // ASM: call 0x401020
        0xe8, 0x27, 0x00, 0x00, 0x00, // ASM: call 0x401040
        0x48, 0x83, 0xc4, 0x28, // ASM: add rsp, 0x28
        0xc3, // ASM: ret
    ];
    pad(&mut code, 0x20);
    code.extend_from_slice(&[
        0xf2, 0x0f, 0x10, 0x05, 0xd8, 0x0f, 0x00, 0x00, // ASM: movsd xmm0, [rip+0xfd8]
        0xc3, // ASM: ret
    ]);
    pad(&mut code, 0x40);
    code.extend_from_slice(&[
        0xf2, 0x0f, 0x2c, 0xc0, // ASM: cvttsd2si eax, xmm0
        0xc3, // ASM: ret
    ]);
    pad(&mut code, 0x60);
    code.extend_from_slice(&[
        0xe8, 0xbb, 0xff, 0xff, 0xff, // ASM: call 0x401020
        0xf2, 0x0f, 0x2c, 0xc0, // ASM: cvttsd2si eax, xmm0
        0xc3, // ASM: ret
    ]);
    let p = image(Arch::X86_64, &code, &2.5f64.to_bits().to_le_bytes());
    let text = decompiled(&p, 0x401000);
    assert_eq!(text.matches("xmm0 = sub_401020();").count(), 2, "{text}");
}

/// An import slot the code reads as a value is named for its import and
/// declared as no variable.
///
/// `mov rax,[frob]; mov [rcx],rax; ret`, where 0x402000 is the import
/// slot of `Foo.dll!frob`: the text stores `frob` and listed `uint64_t
/// frob; // @ 0x402000` among its locals, as if the import were one.
#[test]
fn an_import_slot_is_declared_as_no_variable() {
    use borer_engine::program::{Symbol, SymbolKind};
    let code = [
        0x48, 0x8b, 0x05, 0xf9, 0x0f, 0x00, 0x00, // ASM: mov rax, [rip+0xff9]
        0x48, 0x89, 0x01, // ASM: mov [rcx], rax
        0xc3, // ASM: ret
    ];
    let mut p = image(Arch::X86_64, &code, &[0u8; 8]);
    p.symbols = vec![Symbol {
        name: "Foo.dll!frob".to_owned(),
        addr: 0x402000,
        kind: SymbolKind::Import,
    }];
    let text = decompiled(&p, 0x401000);
    assert!(text.contains("= frob;"), "{text}");
    assert!(!text.contains("// @ 0x402000"), "{text}");
}

/// A value the next lines replace before anything reads it goes, also on
/// x86 and arm64, whose register names the cleanup did not know.
#[test]
fn a_store_replaced_before_any_read_goes() {
    for (reg, ret) in [("rax", "rax"), ("eax", "eax"), ("x10", "x0")] {
        let body = format!(
            "{reg} = a1 + 8;\n*a2 = 1;\nL_401010:\n{reg} = 5;\n{ret} = {reg};\nreturn {ret};\n"
        );
        let text = cleanup(&body);
        assert!(!text.contains("a1 + 8"), "{reg}: {text}");
    }
    let text = cleanup("x8 = a1;\nreturn 0;\n");
    assert!(!text.contains("x8"), "{text}");
}

/// A value a branch may read, or a later line reads, stays.
#[test]
fn a_store_read_on_some_path_stays() {
    let text = cleanup("rax = 1;\nif (a1 != 0) {\n  rax = 2;\n}\nreturn rax;\n");
    assert!(text.contains("rax = 1;"), "{text}");
    let text = cleanup("eax = 1;\n*a2 = eax;\neax = 2;\nreturn eax;\n");
    assert!(
        text.contains("*a2 = eax;") || text.contains("*a2 = 1;"),
        "{text}"
    );
}

/// A call whose result nothing reads stays as a statement of its own; a
/// right side that does more than call keeps its line.
#[test]
fn a_dead_call_result_leaves_the_call() {
    let text = cleanup("eax = f(a1);\neax = 0;\nreturn eax;\n");
    assert!(text.contains("f(a1);"), "{text}");
    assert!(!text.contains("eax = f(a1);"), "{text}");
    let text = cleanup("x0 = a1->vtable[2](a1);\nreturn;\n");
    assert!(text.contains("a1->vtable[2](a1);"), "{text}");
    assert!(!text.contains("x0 ="), "{text}");
    let text = cleanup("rax = f(a1) + 1;\nrax = 0;\nreturn rax;\n");
    assert!(text.contains("rax = f(a1) + 1;"), "{text}");
}

/// A System V variadic function at 0x401000 with two fixed arguments.
///
/// As clang builds one, it stores `rdx` to `r9` into its register save
/// area, then `xmm0` behind `test al, al`, and returns `a1 + a2`.
const SYSV_VARIADIC: [u8; 47] = [
    0x48, 0x81, 0xec, 0xd8, 0x00, 0x00, 0x00, // ASM: sub rsp, 0xd8
    0x48, 0x89, 0x54, 0x24, 0x30, // ASM: mov [rsp+0x30], rdx
    0x48, 0x89, 0x4c, 0x24, 0x38, // ASM: mov [rsp+0x38], rcx
    0x4c, 0x89, 0x44, 0x24, 0x40, // ASM: mov [rsp+0x40], r8
    0x4c, 0x89, 0x4c, 0x24, 0x48, // ASM: mov [rsp+0x48], r9
    0x84, 0xc0, // ASM: test al, al
    0x74, 0x05, // ASM: je 0x401024
    0x0f, 0x29, 0x44, 0x24, 0x50, // ASM: movaps [rsp+0x50], xmm0
    0x8d, 0x04, 0x37, // ASM: lea eax, [rdi+rsi]
    0x48, 0x81, 0xc4, 0xd8, 0x00, 0x00, 0x00, // ASM: add rsp, 0xd8
    0xc3, // ASM: ret
];

/// Builds an ELF-convention image of [`SYSV_VARIADIC`] followed, at
/// 0x401040, by `tail`.
///
/// # Arguments
///
/// * `tail` - The code of the functions after the variadic one.
fn sysv_image(tail: &[u8]) -> borer_engine::program::Program {
    let mut code = SYSV_VARIADIC.to_vec();
    pad(&mut code, 0x40);
    code.extend_from_slice(tail);
    let mut p = image(Arch::X86_64, &code, &[]);
    p.format = borer_engine::program::BinaryFormat::Elf;
    p
}

/// A System V variadic function takes its fixed arguments and `...`, and a
/// caller passes what it set: the save area's stores are no reads of
/// parameters.
///
/// The caller at 0x401040 is `sub rsp,8; mov edi,1; mov esi,2; mov edx,3;
/// xor eax,eax; call 0x401000; add rsp,8; ret`. Every store read as a
/// parameter gave the function fourteen, eight of them `float`, and every
/// caller as many arguments.
#[test]
fn a_sysv_variadic_function_takes_its_fixed_arguments() {
    let p = sysv_image(&[
        0x48, 0x83, 0xec, 0x08, // ASM: sub rsp, 8
        0xbf, 0x01, 0x00, 0x00, 0x00, // ASM: mov edi, 1
        0xbe, 0x02, 0x00, 0x00, 0x00, // ASM: mov esi, 2
        0xba, 0x03, 0x00, 0x00, 0x00, // ASM: mov edx, 3
        0x31, 0xc0, // ASM: xor eax, eax
        0xe8, 0xa6, 0xff, 0xff, 0xff, // ASM: call 0x401000
        0x48, 0x83, 0xc4, 0x08, // ASM: add rsp, 8
        0xc3, // ASM: ret
    ]);
    let callee = decompiled(&p, 0x401000);
    let signature = callee
        .lines()
        .find(|l| l.starts_with("// signature:"))
        .unwrap_or_default();
    assert!(signature.contains(" a2, ...)"), "{callee}");
    assert!(
        !signature.contains("a3") && !signature.contains("float"),
        "{callee}"
    );
    let caller = decompiled(&p, 0x401040);
    assert!(caller.contains("sub_401000(1, 2, 3)"), "{caller}");
}

/// A call to a System V variadic function that does not set `rdx` is no
/// read of a second result an earlier call left there.
///
/// `call PAIR; mov edi,1; mov esi,2; xor eax,eax; call 0x401000; ret`,
/// where `PAIR` is `mov eax,1; mov edx,2; ret`: the save area's store of
/// `rdx` read as the variadic function's own parameter made `PAIR` hand
/// back `rdx`.
#[test]
fn a_variadic_save_area_reads_no_second_result() {
    let mut tail = vec![
        0xe8, 0x1b, 0x00, 0x00, 0x00, // ASM: call 0x401060
        0xbf, 0x01, 0x00, 0x00, 0x00, // ASM: mov edi, 1
        0xbe, 0x02, 0x00, 0x00, 0x00, // ASM: mov esi, 2
        0x31, 0xc0, // ASM: xor eax, eax
        0xe8, 0xaa, 0xff, 0xff, 0xff, // ASM: call 0x401000
        0xc3, // ASM: ret
    ];
    tail.resize(0x20, 0xcc);
    tail.extend_from_slice(&[
        0xb8, 0x01, 0x00, 0x00, 0x00, // ASM: mov eax, 1
        0xba, 0x02, 0x00, 0x00, 0x00, // ASM: mov edx, 2
        0xc3, // ASM: ret
    ]);
    let p = sysv_image(&tail);
    let a = Analysis::compute(&p);
    let pair = a.function(0x401060).expect("the callee");
    assert!(!pair.hands_back_rdx, "the save area read rdx");
}
