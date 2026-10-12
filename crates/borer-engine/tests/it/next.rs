//! The `# next:` steps a function's facts point at.
//!
//! A switch on an argument hints `scenarios`, a decoder loop `emulate`, a
//! serial check `solve`, fields read through a pointer `layout`, each with
//! the address filled in, at most two, the same every time.

#![expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]

use borer_engine::analysis::render::{NEXT_MAX, function_summary, next_steps};
use borer_engine::analysis::{Analysis, Overlay};
use borer_engine::program::{Arch, Program};

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

/// A loop that xors a buffer in place points at a run of it.
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
    assert_eq!(
        steps(&code),
        [
            "borer://emulate/0x401000 (a loop that mixes bytes by xor or rotate and stores them: run it)"
        ]
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
    let step = "borer://solve/0x401000 (compares against 0x1337abcd: the a1 it accepts)";
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
    let p: Program = image(Arch::Arm64, &ret, &[]);
    let a = Analysis::compute(&p);
    assert!(next_steps(&p, &a, &Overlay::default(), 0x40_1000).is_empty());
}
