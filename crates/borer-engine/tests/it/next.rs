//! The `# next:` steps a function's facts point at.
//!
//! A switch on an argument hints `scenarios`, a decoder loop `emulate`, a
//! serial check `solve`, fields read through a pointer `layout`, each with
//! the address filled in, at most two, the same every time.

#![expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]

use borer_engine::analysis::render::{
    NEXT_MAX, function_summary, next_steps, partial_tsv, solve_tsv,
};
use borer_engine::analysis::{Analysis, Overlay};
use borer_engine::program::{Arch, BinaryFormat};

use crate::common::fixture;
use crate::raw::image;

/// The steps of the function at the image's entry, 0x401000.
///
/// # Arguments
///
/// * `code` - The function's bytes.
fn steps(code: &[u8]) -> Vec<String> {
    let p = image(Arch::X86_64, code, &[]);
    let a = Analysis::compute(&p);
    next_steps(&p, &a, &Overlay::default(), 0x40_1000).to_vec()
}

/// A switch on its first argument points at one scenario per value, the
/// default included, and nothing else fires.
#[test]
fn a_switch_on_an_argument_hints_its_scenarios() {
    let p = fixture();
    let a = Analysis::compute(&p);
    let got = next_steps(&p, &a, &Overlay::default(), 0x1060);
    assert_eq!(
        got.as_slice(),
        ["borer://scenarios/0x1060/a1=0..5 (a switch on a1: what each value runs)"]
    );
}

/// A loop that xors a buffer in place points at a run of it, and is not a
/// partial product check.
#[test]
fn a_decoder_loop_hints_an_emulation() {
    let code = [
        0x31, 0xc0, // ASM: xor eax, eax
        0x80, 0x34, 0x01, 0x5a, // ASM: xor byte [rcx+rax], 0x5a
        0x48, 0xff, 0xc0, // ASM: inc rax
        0x48, 0x83, 0xf8, 0x10, // ASM: cmp rax, 0x10
        0x72, 0xf3, // ASM: jb 0x401002
        0xc3, // ASM: ret
    ];
    let hinted = steps(&code);
    assert_eq!(
        hinted,
        [
            "borer://emulate/0x401000 (a loop that mixes bytes by xor or rotate and stores them: run it)"
        ]
    );
    let p = image(Arch::X86_64, &code, &[]);
    let a = Analysis::compute(&p);
    let err = partial_tsv(&p, &a, &Overlay::default(), "0x401000")
        .expect_err("a decoder is not this shape");
    assert!(err.contains("no partial product check"), "{err}");
    assert!(!err.contains('#'), "{err}");
}

/// A counted loop comparing the top bits of `secret * k[i]` with a byte
/// table is a hidden-number problem: lattice reduction, not more samples.
#[test]
fn a_partial_product_loop_is_a_hidden_number_problem() {
    let code = [
        0x45, 0x31, 0xff, // ASM: xor r15d, r15d
        0x4c, 0x8d, 0x0d, 0xd6, 0x11, 0x00, 0x00, // ASM: lea r9, [rip+0x11d6] -> 0x4021e0
        0x4c, 0x8d, 0x05, 0xef, 0x0f, 0x00, 0x00, // ASM: lea r8, [rip+0xfef] -> 0x402000
        0xeb, 0x00, // ASM: jmp 0x401013
        0x48, 0x8b, 0xc1, // ASM: mov rax, rcx
        0x4b, 0xf7, 0x24, 0xf8, // ASM: mul qword [r8+r15*8]
        0x48, 0xc1, 0xea, 0x3d, // ASM: shr rdx, 61
        0x43, 0x3a, 0x14, 0x39, // ASM: cmp dl, [r9+r15]
        0x49, 0xff, 0xc7, // ASM: inc r15
        0x49, 0x83, 0xff, 0x3c, // ASM: cmp r15, 0x3c
        0x7d, 0x02, // ASM: jge 0x40102d
        0xeb, 0xe6, // ASM: jmp 0x401013
        0x31, 0xc0, // ASM: xor eax, eax
        0xc3, // ASM: ret
    ];
    let hinted = steps(&code);
    assert!(
        hinted
            .first()
            .is_some_and(|s| s.starts_with("borer://partial/0x401000")),
        "{hinted:?}"
    );
    let partial_at = hinted
        .iter()
        .position(|s| s.contains("borer://partial/"))
        .expect("a partial step");
    for other in ["borer://solve/", "borer://emulate/"] {
        if let Some(at) = hinted.iter().position(|s| s.contains(other)) {
            assert!(partial_at < at, "{hinted:?}");
        }
    }
    let p = image(Arch::X86_64, &code, &[]);
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let report = partial_tsv(&p, &a, &o, "0x401000").expect("the loop is this shape");
    for needle in [
        "60 iterations",
        "by 61",
        "0x4021e0",
        "rcx",
        "hidden number problem",
        "not more samples",
    ] {
        assert!(report.contains(needle), "{needle} missing:\n{report}");
    }
    let solved = solve_tsv(&p, &a, &o, "0x401000").expect("solves");
    assert!(solved.contains("borer://partial/0x401000"), "{solved}");
}

/// A `sub` whose flags a following `xor` overwrites is a mixer, not the
/// constant `solve` should try. The later `cmp` of the argument is.
#[test]
fn arithmetic_that_feeds_a_xor_is_not_the_solved_constant() {
    let code = [
        0x81, 0xea, 0xa2, 0xc8, 0x56, 0x07, // ASM: sub edx, 0x0756c8a2
        0x33, 0xf2, // ASM: xor esi, edx
        0x81, 0xf9, 0xcd, 0xab, 0x37, 0x13, // ASM: cmp ecx, 0x1337abcd
        0x0f, 0x94, 0xc0, // ASM: sete al
        0xc3, // ASM: ret
    ];
    assert_eq!(
        steps(&code),
        ["borer://solve/0x401000,a1 (compares against 0x1337abcd: solve tries it as a1)"]
    );
}

/// A call between a `sub` and the flag read leaves the flags undefined.
/// The immediate is not the check.
#[test]
fn a_call_between_a_sub_and_its_flag_read_hides_the_compare() {
    let code = [
        0x81, 0xe9, 0xcd, 0xab, 0x37, 0x13, // ASM: sub ecx, 0x1337abcd
        0xe8, 0x04, 0x00, 0x00, 0x00, // ASM: call 0x40100f
        0x0f, 0x94, 0xc0, // ASM: sete al
        0xc3, // ASM: ret
        0xc3, // ASM: ret
    ];
    let got = steps(&code);
    assert!(
        got.iter().all(|step| !step.contains("0x1337abcd")),
        "{got:?}"
    );
}

/// A `sub` that nothing reads, followed by a branch on its flags, is the
/// compare. The argument register was not written before it.
#[test]
fn a_sub_whose_flags_a_branch_reads_is_still_a_compare() {
    let code = [
        0x81, 0xe9, 0xcd, 0xab, 0x37, 0x13, // ASM: sub ecx, 0x1337abcd
        0x0f, 0x84, 0x03, 0x00, 0x00, 0x00, // ASM: jz 0x40100f
        0x31, 0xc0, // ASM: xor eax, eax
        0xc3, // ASM: ret
        0xb8, 0x01, 0x00, 0x00, 0x00, // ASM: mov eax, 1
        0xc3, // ASM: ret
    ];
    assert_eq!(
        steps(&code),
        ["borer://solve/0x401000,a1 (compares against 0x1337abcd: solve tries it as a1)"]
    );
}

/// `adc` reads the carry to continue a sum. That is not a check of the
/// subtracted constant.
#[test]
fn an_adc_is_not_a_check_of_the_subtracted_constant() {
    let code = [
        0x81, 0xe9, 0xcd, 0xab, 0x37, 0x13, // ASM: sub ecx, 0x1337abcd
        0x83, 0xd2, 0x00, // ASM: adc edx, 0
        0xc3, // ASM: ret
    ];
    let got = steps(&code);
    assert!(
        got.iter().all(|step| !step.contains("0x1337abcd")),
        "{got:?}"
    );
}

/// A branch on a flag a later instruction replaced is not that compare.
///
/// `inc` writes the zero flag and leaves carry. `jz` reads the zero flag
/// `inc` wrote, so the immediate is not the check.
#[test]
fn a_branch_on_a_replaced_flag_is_not_the_compare() {
    let code = [
        0x81, 0xe9, 0xcd, 0xab, 0x37, 0x13, // ASM: sub ecx, 0x1337abcd
        0xff, 0xc2, // ASM: inc edx
        0x74, 0x01, // ASM: jz 0x40100b
        0xc3, // ASM: ret
        0xc3, // ASM: ret
    ];
    let got = steps(&code);
    assert!(
        got.iter().all(|step| !step.contains("0x1337abcd")),
        "{got:?}"
    );
}

/// Flags still decide the compare after a run of flag-preserving moves,
/// and after an instruction that writes a different flag.
#[test]
fn a_late_flag_read_and_a_carry_clear_keep_the_compare() {
    let mut late = vec![
        0x81, 0xe9, 0xcd, 0xab, 0x37, 0x13, // ASM: sub ecx, 0x1337abcd
    ];
    late.extend(
        std::iter::repeat_n(
            [0x89, 0xc2], // ASM: mov edx, eax
            8,
        )
        .flatten(),
    );
    late.extend_from_slice(&[
        0x0f, 0x94, 0xc0, // ASM: sete al
        0xc3, // ASM: ret
    ]);
    assert_eq!(
        steps(&late),
        ["borer://solve/0x401000,a1 (compares against 0x1337abcd: solve tries it as a1)"]
    );
    let cleared = [
        0x81, 0xe9, 0xcd, 0xab, 0x37, 0x13, // ASM: sub ecx, 0x1337abcd
        0xf8, // ASM: clc
        0x0f, 0x94, 0xc0, // ASM: sete al
        0xc3, // ASM: ret
    ];
    assert_eq!(
        steps(&cleared),
        ["borer://solve/0x401000,a1 (compares against 0x1337abcd: solve tries it as a1)"]
    );
}

/// A compare of a register copied from a call's return value is not `a1`.
#[test]
fn a_compare_of_a_call_result_does_not_name_a1() {
    let code = [
        0x89, 0xc8, // ASM: mov eax, ecx
        0xe8, 0x0c, 0x00, 0x00, 0x00, // ASM: call 0x401013
        0x89, 0xc2, // ASM: mov edx, eax
        0x81, 0xfa, 0x0a, 0x10, 0x00, 0x00, // ASM: cmp edx, 0x100a
        0x74, 0x01, // ASM: je 0x401012
        0xc3, // ASM: ret
        0xc3, // ASM: ret
        0x31, 0xc0, // ASM: xor eax, eax
        0xc3, // ASM: ret
    ];
    assert_eq!(
        steps(&code),
        ["borer://solve/0x401000 (compares against 0x100a: a call result, not an argument)"]
    );
}

/// A `test` of an `xor` result is the compare the `xor` flags no longer are.
///
/// `test ecx, ecx` replaces those flags, and `sete` reads the test. A copy
/// of the result is still that compare. Overwriting the register first, or
/// leaving the test's flags unread, is not.
#[test]
fn a_tested_xor_result_is_still_a_compare() {
    let code = [
        0x81, 0xf1, 0xcd, 0xab, 0x37, 0x13, // ASM: xor ecx, 0x1337abcd
        0x85, 0xc9, // ASM: test ecx, ecx
        0x0f, 0x94, 0xc0, // ASM: sete al
        0xc3, // ASM: ret
    ];
    assert_eq!(
        steps(&code),
        ["borer://solve/0x401000,a1 (compares against 0x1337abcd: solve tries it as a1)"]
    );
    let copied = [
        0x81, 0xf1, 0xcd, 0xab, 0x37, 0x13, // ASM: xor ecx, 0x1337abcd
        0x89, 0xca, // ASM: mov edx, ecx
        0x85, 0xd2, // ASM: test edx, edx
        0x0f, 0x94, 0xc0, // ASM: sete al
        0xc3, // ASM: ret
    ];
    assert_eq!(
        steps(&copied),
        ["borer://solve/0x401000,a1 (compares against 0x1337abcd: solve tries it as a1)"]
    );
    let replaced = [
        0x81, 0xf1, 0xcd, 0xab, 0x37, 0x13, // ASM: xor ecx, 0x1337abcd
        0x89, 0xc1, // ASM: mov ecx, eax
        0x85, 0xc9, // ASM: test ecx, ecx
        0x0f, 0x94, 0xc0, // ASM: sete al
        0xc3, // ASM: ret
    ];
    let got = steps(&replaced);
    assert!(
        got.iter().all(|step| !step.contains("0x1337abcd")),
        "{got:?}"
    );
    let unread = [
        0x81, 0xf1, 0xcd, 0xab, 0x37, 0x13, // ASM: xor ecx, 0x1337abcd
        0x85, 0xc9, // ASM: test ecx, ecx
        0xc3, // ASM: ret
    ];
    let got = steps(&unread);
    assert!(
        got.iter().all(|step| !step.contains("0x1337abcd")),
        "{got:?}"
    );
}

/// Copying the difference does not hide a `sub` whose flags a later
/// instruction still reads.
#[test]
fn a_copied_sub_result_is_still_a_compare() {
    let code = [
        0x81, 0xe9, 0xcd, 0xab, 0x37, 0x13, // ASM: sub ecx, 0x1337abcd
        0x89, 0xca, // ASM: mov edx, ecx
        0x0f, 0x94, 0xc0, // ASM: sete al
        0x0f, 0xb6, 0xc0, // ASM: movzx eax, al
        0xc3, // ASM: ret
    ];
    assert_eq!(
        steps(&code),
        ["borer://solve/0x401000,a1 (compares against 0x1337abcd: solve tries it as a1)"]
    );
}

/// A direct jump to the flag read is the path that runs. A flag write that
/// only sits between the two in address order is another block.
#[test]
fn a_jump_to_the_flag_read_keeps_the_compare() {
    let code = [
        0x81, 0xe9, 0xcd, 0xab, 0x37, 0x13, // ASM: sub ecx, 0x1337abcd
        0xe9, 0x04, 0x00, 0x00, 0x00, // ASM: jmp 0x40100f
        0x83, 0xc0, 0x01, // ASM: add eax, 1
        0xc3, // ASM: ret
        0x74, 0x05, // ASM: jz 0x401016
        0xe9, 0xf5, 0xff, 0xff, 0xff, // ASM: jmp 0x40100b
        0xb8, 0x01, 0x00, 0x00, 0x00, // ASM: mov eax, 1
        0xc3, // ASM: ret
    ];
    assert_eq!(
        steps(&code),
        ["borer://solve/0x401000,a1 (compares against 0x1337abcd: solve tries it as a1)"]
    );
}

/// A call may change `rcx`, so a compare of `ecx` after the call is not
/// shown to be `a1`.
#[test]
fn a_call_hides_the_argument_register() {
    let code = [
        0x89, 0xc8, // ASM: mov eax, ecx
        0xe8, 0x0a, 0x00, 0x00, 0x00, // ASM: call 0x401011
        0x81, 0xf9, 0xcd, 0xab, 0x37, 0x13, // ASM: cmp ecx, 0x1337abcd
        0x0f, 0x94, 0xc0, // ASM: sete al
        0xc3, // ASM: ret
        0xc3, // ASM: ret
    ];
    assert_eq!(
        steps(&code),
        ["borer://solve/0x401000 (compares against 0x1337abcd: not shown to be a1)"]
    );
}

/// A copy the fallthrough always runs names that argument.
#[test]
fn a_copied_argument_keeps_its_number() {
    let code = [
        0x89, 0xd1, // ASM: mov ecx, edx
        0x81, 0xf9, 0xcd, 0xab, 0x37, 0x13, // ASM: cmp ecx, 0x1337abcd
        0x0f, 0x94, 0xc0, // ASM: sete al
        0xc3, // ASM: ret
    ];
    assert_eq!(
        steps(&code),
        ["borer://solve/0x401000,a2 (compares against 0x1337abcd: solve tries it as a2)"]
    );
}

/// A branch that jumps over the copy still reaches the compare, so the
/// hint does not name the register only one path holds.
#[test]
fn a_branch_over_a_copy_does_not_name_that_argument() {
    let code = [
        0x45, 0x85, 0xc0, // ASM: test r8d, r8d
        0x74, 0x02, // ASM: jz 0x401007
        0x89, 0xd1, // ASM: mov ecx, edx
        0x81, 0xf9, 0xcd, 0xab, 0x37, 0x13, // ASM: cmp ecx, 0x1337abcd
        0x0f, 0x94, 0xc0, // ASM: sete al
        0xc3, // ASM: ret
    ];
    assert_eq!(
        steps(&code),
        ["borer://solve/0x401000 (compares against 0x1337abcd: not shown to be a1)"]
    );
}

/// A copy at a later address that jumps back to the compare is not in the
/// address-order trace, so the hint does not name `a1`.
#[test]
fn a_later_copy_that_jumps_back_does_not_name_the_argument() {
    let code = [
        0xeb, 0x0a, // ASM: jmp 0x40100c
        0x81, 0xf9, 0xcd, 0xab, 0x37, 0x13, // ASM: cmp ecx, 0x1337abcd
        0x0f, 0x94, 0xc0, // ASM: sete al
        0xc3, // ASM: ret
        0x89, 0xd1, // ASM: mov ecx, edx
        0xeb, 0xf2, // ASM: jmp 0x401002
    ];
    assert_eq!(
        steps(&code),
        ["borer://solve/0x401000 (compares against 0x1337abcd: not shown to be a1)"]
    );
}

/// A byte copy does not make the whole compared register the argument.
#[test]
fn a_partial_copy_is_not_the_argument() {
    let code = [
        0x31, 0xd2, // ASM: xor edx, edx
        0x88, 0xca, // ASM: mov dl, cl
        0x81, 0xfa, 0xcd, 0xab, 0x37, 0x13, // ASM: cmp edx, 0x1337abcd
        0x0f, 0x94, 0xc0, // ASM: sete al
        0xc3, // ASM: ret
    ];
    assert_eq!(
        steps(&code),
        ["borer://solve/0x401000 (compares against 0x1337abcd: not shown to be a1)"]
    );
}

/// On System V the first argument arrives in `rdi`. `rcx` is the fourth.
#[test]
fn an_elf_argument_is_named_from_its_register() {
    let rdi = [
        0x81, 0xff, 0xcd, 0xab, 0x37, 0x13, // ASM: cmp edi, 0x1337abcd
        0x0f, 0x94, 0xc0, // ASM: sete al
        0xc3, // ASM: ret
    ];
    let mut p = image(Arch::X86_64, &rdi, &[]);
    p.format = BinaryFormat::Elf;
    let a = Analysis::compute(&p);
    let got = next_steps(&p, &a, &Overlay::default(), 0x40_1000);
    assert_eq!(
        got.as_slice(),
        ["borer://solve/0x401000,a1 (compares against 0x1337abcd: solve tries it as a1)"]
    );

    let rcx = [
        0x89, 0xf8, // ASM: mov eax, edi
        0x81, 0xf9, 0xcd, 0xab, 0x37, 0x13, // ASM: cmp ecx, 0x1337abcd
        0x0f, 0x94, 0xc0, // ASM: sete al
        0xc3, // ASM: ret
    ];
    let mut p = image(Arch::X86_64, &rcx, &[]);
    p.format = BinaryFormat::Elf;
    let a = Analysis::compute(&p);
    let got = next_steps(&p, &a, &Overlay::default(), 0x40_1000);
    assert_eq!(
        got.as_slice(),
        ["borer://solve/0x401000,a4 (compares against 0x1337abcd: solve tries it as a4)"]
    );
}

/// A `!= 0` test of a named global does not parse the address digits in
/// the name as a decimal constant.
#[test]
fn a_global_name_is_not_the_compared_constant() {
    let code = [
        0x85, 0xc9, // ASM: test ecx, ecx
        0x83, 0x3d, 0x07, 0x10, 0x00, 0x00, 0x00, // ASM: cmp dword [rip+0x1007], 0
        0x75, 0x01, // ASM: jne 0x40100c
        0xc3, // ASM: ret
        0xc3, // ASM: ret
    ];
    let hinted = steps(&code);
    assert!(
        hinted
            .iter()
            .all(|s| !s.contains("0x6225a") && !s.contains("402010")),
        "{hinted:?}"
    );
}

/// A compare of the argument against a telling constant points at the
/// value it accepts, and the summary ends with the same step.
#[test]
fn a_serial_check_hints_solve_and_the_summary_ends_with_it() {
    let code = [
        0x81, 0xf9, 0xcd, 0xab, 0x37, 0x13, // ASM: cmp ecx, 0x1337abcd
        0x0f, 0x94, 0xc0, // ASM: sete al
        0x0f, 0xb6, 0xc0, // ASM: movzx eax, al
        0xc3, // ASM: ret
    ];
    let step = "borer://solve/0x401000,a1 (compares against 0x1337abcd: solve tries it as a1)";
    assert_eq!(steps(&code), [step]);
    let p = image(Arch::X86_64, &code, &[]);
    let a = Analysis::compute(&p);
    let summary = function_summary(&p, &a, &Overlay::default(), 0x40_1000).expect("a function");
    assert!(summary.ends_with(&format!("# next: {step}\n")), "{summary}");
}

/// Three fields read through the first argument point at the structure,
/// in the register the argument arrives in.
#[test]
fn fields_through_a_pointer_hint_its_layout() {
    let code = [
        0x8b, 0x41, 0x08, // ASM: mov eax, [rcx+8]
        0x03, 0x41, 0x10, // ASM: add eax, [rcx+0x10]
        0x03, 0x41, 0x18, // ASM: add eax, [rcx+0x18]
        0xc3, // ASM: ret
    ];
    assert_eq!(
        steps(&code),
        ["borer://layout/0x401000,rcx (reads 3 fields through a1: its structure)"]
    );
}

/// A plain function gets no step, no function gets more than
/// [`NEXT_MAX`], and two analyses give the same steps.
#[test]
fn steps_are_few_and_the_same_every_time() {
    assert!(steps(&[0x31, 0xc0, 0xc3]).is_empty());
    let p = fixture();
    let first = Analysis::compute(&p);
    let second = Analysis::compute(&p);
    for f in &first.functions {
        let one = next_steps(&p, &first, &Overlay::default(), f.entry);
        let two = next_steps(&p, &second, &Overlay::default(), f.entry);
        assert!(one.len() <= NEXT_MAX, "{:#x}: {one:?}", f.entry);
        assert_eq!(one, two, "{:#x}", f.entry);
    }
}

/// An arm64 program gets no step: the rules read x86 code.
#[test]
fn an_arm64_function_gets_no_step() {
    let ret = [0xc0, 0x03, 0x5f, 0xd6]; // ASM: ret
    let p = image(Arch::Arm64, &ret, &[]);
    let a = Analysis::compute(&p);
    assert!(next_steps(&p, &a, &Overlay::default(), 0x40_1000).is_empty());
}

/// A 32-bit copy does not carry a 64-bit value into a compare.
///
/// `mov ebx, eax` after `sub rax, imm` keeps the low half. `test rbx, rbx`
/// is not that subtraction. `mov eax, ecx` then `cmp rax, imm` is a compare,
/// and it is not a compare of `a1`. The full-width copies are.
#[test]
fn a_narrow_copy_is_not_a_wide_compare() {
    let low = [
        0x48, 0x81, 0xe8, 0xcd, 0xab, 0x37, 0x13, // ASM: sub rax, 0x1337abcd
        0x89, 0xc3, // ASM: mov ebx, eax
        0x48, 0x85, 0xdb, // ASM: test rbx, rbx
        0x74, 0x03, // ASM: jz 0x401011
        0x89, 0xc8, // ASM: mov eax, ecx
        0xc3, // ASM: ret
        0xc3, // ASM: ret
    ];
    let got = steps(&low);
    assert!(
        got.iter().all(|step| !step.contains("0x1337abcd")),
        "{got:?}"
    );
    let wide = [
        0x48, 0x81, 0xe8, 0xcd, 0xab, 0x37, 0x13, // ASM: sub rax, 0x1337abcd
        0x48, 0x89, 0xc3, // ASM: mov rbx, rax
        0x48, 0x85, 0xdb, // ASM: test rbx, rbx
        0x74, 0x03, // ASM: jz 0x401012
        0x89, 0xc8, // ASM: mov eax, ecx
        0xc3, // ASM: ret
        0xc3, // ASM: ret
    ];
    assert_eq!(
        steps(&wide),
        ["borer://solve/0x401000 (compares against 0x1337abcd: not shown to be a1)"]
    );
    let half = [
        0x89, 0xc8, // ASM: mov eax, ecx
        0x48, 0x81, 0xf8, 0xcd, 0xab, 0x37, 0x13, // ASM: cmp rax, 0x1337abcd
        0x0f, 0x94, 0xc0, // ASM: sete al
        0xc3, // ASM: ret
    ];
    assert_eq!(
        steps(&half),
        ["borer://solve/0x401000 (compares against 0x1337abcd: not shown to be a1)"]
    );
    let full = [
        0x48, 0x89, 0xc8, // ASM: mov rax, rcx
        0x48, 0x81, 0xf8, 0xcd, 0xab, 0x37, 0x13, // ASM: cmp rax, 0x1337abcd
        0x0f, 0x94, 0xc0, // ASM: sete al
        0xc3, // ASM: ret
    ];
    assert_eq!(
        steps(&full),
        ["borer://solve/0x401000,a1 (compares against 0x1337abcd: solve tries it as a1)"]
    );
}
