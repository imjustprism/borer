//! Chains of arithmetic inverted to the input that reaches a target.

use super::*;

/// `solve` names a value no constant in the function spells, by inverting
/// the chain between the argument and its comparison.
///
/// `((a1 ^ 0x5bd1e995) + 0x1234) == 0xdeadbeef` holds for one input the
/// code never carries: the prober's constants all answer the same, and
/// the chain's inverse states it, proven by the run.
///
/// # Panics
///
/// When the solved value or its run is missing from the report.
#[test]
fn solve_inverts_a_chain_the_constants_do_not_name() {
    use borer_engine::analysis::render::solve_tsv;
    let code = [
        0x8b, 0xc1, // ASM: mov eax,ecx
        0x35, 0x95, 0xe9, 0xd1, 0x5b, // ASM: xor eax,0x5bd1e995
        0x05, 0x34, 0x12, 0x00, 0x00, // ASM: add eax,0x1234
        0x3d, 0xef, 0xbe, 0xad, 0xde, // ASM: cmp eax,0xdeadbeef
        0x75, 0x06, // ASM: jne +6
        0xb8, 0x01, 0x00, 0x00, 0x00, // ASM: mov eax,1
        0xc3, // ASM: ret
        0x31, 0xc0, // ASM: xor eax,eax
        0xc3, // ASM: ret
    ];
    let p = program64(&code);
    let a = Analysis::compute(&p);
    let out = solve_tsv(&p, &a, &Overlay::default(), "0x140001000").expect("solves");
    let want = 0x00deadbeefu64.wrapping_sub(0x1234) ^ 0x5bd1e995;
    assert!(out.contains(&format!("a1 = {want:#x}")), "{out}");
    assert!(out.contains("returns 0x1"), "{out}");
}

/// `solve`'s inversion only answers what a run proves: a chain that
/// loses bits - a mask, a shift right - says nothing rather than a value
/// it cannot know to be right.
///
/// # Panics
///
/// When the report claims a chain it cannot invert.
#[test]
fn solve_says_nothing_for_a_chain_it_cannot_invert() {
    use borer_engine::analysis::render::solve_tsv;
    let code = [
        0x8b, 0xc1, // ASM: mov eax,ecx
        0x25, 0xf0, 0x00, 0x00, 0x00, // ASM: and eax,0xf0
        0x3d, 0x30, 0x00, 0x00, 0x00, // ASM: cmp eax,0x30
        0x75, 0x06, // ASM: jne +6
        0xb8, 0x01, 0x00, 0x00, 0x00, // ASM: mov eax,1
        0xc3, // ASM: ret
        0x31, 0xc0, // ASM: xor eax,eax
        0xc3, // ASM: ret
    ];
    let p = program64(&code);
    let a = Analysis::compute(&p);
    let out = solve_tsv(&p, &a, &Overlay::default(), "0x140001000").expect("solves");
    assert!(!out.contains("chain:"), "{out}");
}

/// `solve` inverts a switch subject to the case it selects.
///
/// `switch (a1 ^ 0x5bd1e995) { case 42: ... }` holds its answer in the
/// arithmetic between the parameter and the case labels; inverting the
/// subject for the first case states the input that selects it, proven by
/// the run (case 42 returns 1, every other input returns 0).
///
/// # Panics
///
/// When the switch subject is not solved to the value that selects its
/// first case.
#[test]
fn solve_inverts_a_switch_subject_to_its_case() {
    use borer_engine::analysis::render::solve_tsv;
    let code = [
        0x8b, 0xc1, // ASM: mov eax,ecx
        0x35, 0x95, 0xe9, 0xd1, 0x5b, // ASM: xor eax,0x5bd1e995
        0x3d, 0x2a, 0x00, 0x00, 0x00, // ASM: cmp eax,0x2a
        0x74, 0x11, // ASM: je case_42
        0x3d, 0x2b, 0x00, 0x00, 0x00, // ASM: cmp eax,0x2b
        0x74, 0x10, // ASM: je case_43
        0x3d, 0x2c, 0x00, 0x00, 0x00, // ASM: cmp eax,0x2c
        0x74, 0x0f, // ASM: je case_44
        0x31, 0xc0, // ASM: xor eax,eax
        0xc3, // ASM: ret
        0xb8, 0x01, 0x00, 0x00, 0x00, // ASM: mov eax,1
        0xc3, // ASM: ret
        0xb8, 0x02, 0x00, 0x00, 0x00, // ASM: mov eax,2
        0xc3, // ASM: ret
        0xb8, 0x03, 0x00, 0x00, 0x00, // ASM: mov eax,3
        0xc3, // ASM: ret
    ];
    let p = program64(&code);
    let a = Analysis::compute(&p);
    let out = solve_tsv(&p, &a, &Overlay::default(), "0x140001000").expect("solves");
    let want = 0x2a ^ 0x5bd1_e995u64;
    assert!(out.contains(&format!("chain: a1 = {want:#x}")), "{out}");
    assert!(out.contains("returns 0x1"), "{out}");
}

/// `solve` states a 32-bit chain's answer inside 32 bits.
///
/// `((a1 ^ 0x5bd1e995) + 0x2000) == 0x100` wraps at 32 bits: the inverse
/// of `0x100 - 0x2000` is `0xffffe100`, and the answer the report states
/// xor's the key onto that, still inside the word the compare runs at.
///
/// # Panics
///
/// When the answer is missing or wider than the comparison.
#[test]
fn solve_fits_the_word_at_32_bits() {
    use borer_engine::analysis::render::solve_tsv;
    let code = [
        0x8b, 0xc1, // ASM: mov eax,ecx
        0x35, 0x95, 0xe9, 0xd1, 0x5b, // ASM: xor eax,0x5bd1e995
        0x05, 0x00, 0x20, 0x00, 0x00, // ASM: add eax,0x2000
        0x3d, 0x00, 0x01, 0x00, 0x00, // ASM: cmp eax,0x100
        0x75, 0x06, // ASM: jne no
        0xb8, 0x01, 0x00, 0x00, 0x00, // ASM: mov eax,1
        0xc3, // ASM: ret
        0x31, 0xc0, // ASM: xor eax,eax
        0xc3, // ASM: ret
    ];
    let p = program64(&code);
    let a = Analysis::compute(&p);
    let out = solve_tsv(&p, &a, &Overlay::default(), "0x140001000").expect("solves");
    let want = 0x100u32.wrapping_sub(0x2000) ^ 0x5bd1_e995u32;
    assert!(out.contains(&format!("chain: a1 = {want:#x}")), "{out}");
    assert!(out.contains("returns 0x1"), "{out}");
}

/// `solve` stays silent when a mid-chain step loses bits.
///
/// `xor; and eax,0xf0; add; cmp`: the mask in the middle of the chain
/// keeps its input's high nibble, so no inverse exists and the report
/// says nothing rather than a value it cannot know to be right.
///
/// # Panics
///
/// When the report claims a chain the mask breaks.
#[test]
fn solve_says_nothing_when_a_midway_step_loses_bits() {
    use borer_engine::analysis::render::solve_tsv;
    let code = [
        0x8b, 0xc1, // ASM: mov eax,ecx
        0x35, 0x95, 0xe9, 0xd1, 0x5b, // ASM: xor eax,0x5bd1e995
        0x25, 0xf0, 0x00, 0x00, 0x00, // ASM: and eax,0xf0
        0x05, 0x10, 0x00, 0x00, 0x00, // ASM: add eax,0x10
        0x3d, 0x40, 0x00, 0x00, 0x00, // ASM: cmp eax,0x40
        0x75, 0x06, // ASM: jne no
        0xb8, 0x01, 0x00, 0x00, 0x00, // ASM: mov eax,1
        0xc3, // ASM: ret
        0x31, 0xc0, // ASM: xor eax,eax
        0xc3, // ASM: ret
    ];
    let p = program64(&code);
    let a = Analysis::compute(&p);
    let out = solve_tsv(&p, &a, &Overlay::default(), "0x140001000").expect("solves");
    assert!(out.contains("# every candidate"), "{out}");
    assert!(!out.contains("chain:"), "{out}");
}

/// `solve` still solves when the parameter is read outside its chain.
///
/// The comparison chain runs on `eax`, but the taken arm returns `edx`,
/// which holds the parameter again: the inversion is the same, and the
/// run tells the solved value apart from zero by returning it.
///
/// # Panics
///
/// When the solved value or its run is missing from the report.
#[test]
fn solve_still_solves_when_the_parameter_is_read_elsewhere() {
    use borer_engine::analysis::render::solve_tsv;
    let code = [
        0x8b, 0xd1, // ASM: mov edx,ecx
        0x8b, 0xc1, // ASM: mov eax,ecx
        0x35, 0x95, 0xe9, 0xd1, 0x5b, // ASM: xor eax,0x5bd1e995
        0x3d, 0xef, 0xbe, 0xad, 0xde, // ASM: cmp eax,0xdeadbeef
        0x75, 0x03, // ASM: jne no
        0x8b, 0xc2, // ASM: mov eax,edx
        0xc3, // ASM: ret
        0x31, 0xc0, // ASM: xor eax,eax
        0xc3, // ASM: ret
    ];
    let p = program64(&code);
    let a = Analysis::compute(&p);
    let out = solve_tsv(&p, &a, &Overlay::default(), "0x140001000").expect("solves");
    let want = 0xdead_beefu64 ^ 0x5bd1_e995;
    assert!(out.contains(&format!("chain: a1 = {want:#x}")), "{out}");
    assert!(out.contains(&format!("returns {want:#x}")), "{out}");
}

/// `solve` inverts the chain of the parameter it was asked about.
///
/// Asked for `a2`, it reads the comparison on `edx` - even with `a1`
/// read in the arm beside it - and the answer names `a2`, never `a1`.
///
/// # Panics
///
/// When the second parameter's chain is not solved, or the report names
/// the first.
#[test]
fn solve_inverts_the_second_parameters_chain() {
    use borer_engine::analysis::render::solve_tsv;
    let code = [
        0x8b, 0xc2, // ASM: mov eax,edx
        0x35, 0x95, 0xe9, 0xd1, 0x5b, // ASM: xor eax,0x5bd1e995
        0x3d, 0xef, 0xbe, 0xad, 0xde, // ASM: cmp eax,0xdeadbeef
        0x75, 0x03, // ASM: jne no
        0x03, 0xc1, // ASM: add eax,ecx
        0xc3, // ASM: ret
        0x31, 0xc0, // ASM: xor eax,eax
        0xc3, // ASM: ret
    ];
    let p = program64(&code);
    let a = Analysis::compute(&p);
    let out = solve_tsv(&p, &a, &Overlay::default(), "0x140001000,a2").expect("solves");
    let want = 0xdead_beefu64 ^ 0x5bd1_e995;
    assert!(out.contains(&format!("chain: a2 = {want:#x}")), "{out}");
    assert!(!out.contains("chain: a1"), "{out}");
    assert!(out.contains("returns 0xdeadbeef"), "{out}");
}

/// `solve` finds the target inside a joined condition.
///
/// Only the second conjunct names `a1`; the first (`a2 == 0`) is true of
/// the zero argument the verification runs, so the second's comparison
/// decides the run and its chain is the one inverted.
///
/// # Panics
///
/// When the conjunct's target is missing from the report.
#[test]
fn solve_finds_the_target_inside_a_joined_condition() {
    use borer_engine::analysis::render::solve_tsv;
    let code = [
        0x85, 0xd2, // ASM: test edx,edx
        0x75, 0x14, // ASM: jne no
        0x8b, 0xc1, // ASM: mov eax,ecx
        0x35, 0x95, 0xe9, 0xd1, 0x5b, // ASM: xor eax,0x5bd1e995
        0x3d, 0xef, 0xbe, 0xad, 0xde, // ASM: cmp eax,0xdeadbeef
        0x75, 0x06, // ASM: jne no
        0xb8, 0x01, 0x00, 0x00, 0x00, // ASM: mov eax,1
        0xc3, // ASM: ret
        0x31, 0xc0, // ASM: xor eax,eax
        0xc3, // ASM: ret
    ];
    let p = program64(&code);
    let a = Analysis::compute(&p);
    let out = solve_tsv(&p, &a, &Overlay::default(), "0x140001000").expect("solves");
    let want = 0xdead_beefu64 ^ 0x5bd1_e995;
    assert!(out.contains(&format!("chain: a1 = {want:#x}")), "{out}");
    assert!(out.contains("returns 0x1"), "{out}");
}

/// `solve` never reports what a run cannot distinguish.
///
/// The chain inverts, but both arms return 7: the run of the candidate
/// answers what the run of zero answers, so no value is reported - the
/// verified answer is the contract, not the inversion.
///
/// # Panics
///
/// When the report claims a value the run cannot tell apart from zero.
#[test]
fn solve_stays_silent_when_the_run_cannot_distinguish() {
    use borer_engine::analysis::render::solve_tsv;
    let code = [
        0x8b, 0xc1, // ASM: mov eax,ecx
        0x35, 0x95, 0xe9, 0xd1, 0x5b, // ASM: xor eax,0x5bd1e995
        0x3d, 0xef, 0xbe, 0xad, 0xde, // ASM: cmp eax,0xdeadbeef
        0x75, 0x06, // ASM: jne no
        0xb8, 0x07, 0x00, 0x00, 0x00, // ASM: mov eax,7
        0xc3, // ASM: ret
        0xb8, 0x07, 0x00, 0x00, 0x00, // ASM: mov eax,7
        0xc3, // ASM: ret
    ];
    let p = program64(&code);
    let a = Analysis::compute(&p);
    let out = solve_tsv(&p, &a, &Overlay::default(), "0x140001000").expect("solves");
    assert!(out.contains("every candidate returns 0x7"), "{out}");
    assert!(!out.contains("chain:"), "{out}");
}
