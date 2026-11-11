//! Structured control flow: loops, shared tails, joins, labels and gotos.

use super::*;

/// A call site's scan follows a jump within the caller.
///
/// `call 0x140001040; jmp L; int3; L: xor eax,eax; ret` overwrites the
/// result unread, so the callee `call 0x140001060; ret`, which hands back
/// what `mov eax,1; ret` left, returns nothing anyone reads.
#[test]
fn a_call_site_scan_follows_a_jump() {
    let mut code = vec![
        0xe8, 0x3b, 0x00, 0x00, 0x00, 0xeb, 0x01, 0xcc, 0x33, 0xc0, 0xc3,
    ];
    code.resize(0x40, 0xcc);
    code.extend_from_slice(&[0xe8, 0x1b, 0x00, 0x00, 0x00, 0xc3]);
    code.resize(0x60, 0xcc);
    code.extend_from_slice(&[0xb8, 0x01, 0x00, 0x00, 0x00, 0xc3]);
    let p = program64(&code);
    let a = Analysis::compute(&p);
    let f = a.function(0x1_4000_1040).map(|f| f.returns_value);
    assert_eq!(f, Some(Some(false)));
}

/// A call site's scan goes down both sides of a branch.
///
/// `call 0x140001040; test ebx,ebx; je L; xor eax,eax; ret; L: mov eax,2;
/// ret` overwrites the result on each, so the callee `call 0x140001060;
/// ret` returns nothing anyone reads.
#[test]
fn a_call_site_scan_follows_both_sides_of_a_branch() {
    let mut code = vec![
        0xe8, 0x3b, 0x00, 0x00, 0x00, 0x85, 0xdb, 0x74, 0x03, 0x33, 0xc0, 0xc3, 0xb8, 0x02, 0x00,
        0x00, 0x00, 0xc3,
    ];
    code.resize(0x40, 0xcc);
    code.extend_from_slice(&[0xe8, 0x1b, 0x00, 0x00, 0x00, 0xc3]);
    code.resize(0x60, 0xcc);
    code.extend_from_slice(&[0xb8, 0x01, 0x00, 0x00, 0x00, 0xc3]);
    let p = program64(&code);
    let a = Analysis::compute(&p);
    let f = a.function(0x1_4000_1040).map(|f| f.returns_value);
    assert_eq!(f, Some(Some(false)));
}

/// A call block a switch case copies keeps the label its copy jumps to.
///
/// `case 111` and the `79` test both enter the block at 0x50 that calls
/// and falls into the test at 0x55. The case arm gets its own copy of the
/// call, which jumps to 0x55; that path is not one the block graph lists,
/// so the original call may not fold 0x55 into its own test and drop the
/// label. Every `goto` lands on a label, and every block agrees with the
/// machine.
#[test]
fn a_copied_call_block_keeps_the_label_it_jumps_to() {
    let code = [
        0x83, 0xf9, 0x4f, // ASM: cmp ecx,0x4f
        0x74, 0x4b, // ASM: je 0x50
        0x83, 0xf9, 0x42, // ASM: cmp ecx,0x42
        0x74, 0x22, // ASM: je 0x2c
        0x83, 0xf9, 0x5a, // ASM: cmp ecx,0x5a
        0x7f, 0x03, // ASM: jg 0x12
        0x31, 0xc0, // ASM: xor eax,eax
        0xc3, // ASM: ret
        0x83, 0xf9, 0x62, // ASM: cmp ecx,0x62
        0x74, 0x27, // ASM: je 0x3e
        0x83, 0xf9, 0x65, // ASM: cmp ecx,0x65
        0x74, 0x28, // ASM: je 0x44
        0x83, 0xf9, 0x6f, // ASM: cmp ecx,0x6f
        0x74, 0x2f, // ASM: je 0x50
        0x83, 0xf9, 0x70, // ASM: cmp ecx,0x70
        0x74, 0x24, // ASM: je 0x4a
        0xb8, 0x63, 0x00, 0x00, 0x00, // ASM: mov eax,0x63
        0xc3, // ASM: ret
        0xb8, 0x0a, 0x00, 0x00, 0x00, // ASM: mov eax,0xa
        0xc3, // ASM: ret
        0xb8, 0x0b, 0x00, 0x00, 0x00, // ASM: mov eax,0xb
        0xc3, // ASM: ret
        0xb8, 0x0c, 0x00, 0x00, 0x00, // ASM: mov eax,0xc
        0xc3, // ASM: ret
        0xb8, 0x0d, 0x00, 0x00, 0x00, // ASM: mov eax,0xd
        0xc3, // ASM: ret
        0xb8, 0x0e, 0x00, 0x00, 0x00, // ASM: mov eax,0xe
        0xc3, // ASM: ret
        0xb8, 0x0f, 0x00, 0x00, 0x00, // ASM: mov eax,0xf
        0xc3, // ASM: ret
        0xe8, 0x10, 0x00, 0x00, 0x00, // ASM: call 0x65
        0x85, 0xc0, // ASM: test eax,eax
        0x75, 0x06, // ASM: jne 0x5f
        0xb8, 0x01, 0x00, 0x00, 0x00, // ASM: mov eax,1
        0xc3, // ASM: ret
        0xb8, 0x02, 0x00, 0x00, 0x00, // ASM: mov eax,2
        0xc3, // ASM: ret
        0x31, 0xc0, // ASM: xor eax,eax
        0xc3, // ASM: ret
    ];
    let p = program64(&code);
    let a = Analysis::compute(&p);
    let text = decompile(&p, &a, &Overlay::default(), 0x1_4000_1000).unwrap_or_default();
    assert!(text.contains("case 111:"), "{text}");
    let labels: std::collections::BTreeSet<&str> = text
        .lines()
        .filter_map(|l| l.trim().strip_suffix(':'))
        .collect();
    for line in text.lines() {
        if let Some((_, target)) = line.trim().rsplit_once("goto ") {
            let target = target.trim_end_matches(';');
            assert!(labels.contains(target), "{target} has no label: {text}");
        }
    }
    replays_clean(&p, &a, &[0x1_4000_1000]);
}

/// A tail jump hands the callee's result on.
///
/// `call 0x140001060; call 0x140001040; mov [rcx],eax; ret` reads what
/// `jmp 0x140001060` hands back, which is the `mov eax,7; ret` of the
/// function jumped to, so that one returns a value though its one call
/// drops the result.
#[test]
fn a_tail_jump_hands_the_result_on() {
    let mut code = vec![
        0xe8, 0x5b, 0x00, 0x00, 0x00, 0xe8, 0x36, 0x00, 0x00, 0x00, 0x89, 0x01, 0xc3,
    ];
    code.resize(0x40, 0xcc);
    code.extend_from_slice(&[0xe9, 0x1b, 0x00, 0x00, 0x00]);
    code.resize(0x60, 0xcc);
    code.extend_from_slice(&[0xb8, 0x07, 0x00, 0x00, 0x00, 0xc3]);
    let p = program64(&code);
    let a = Analysis::compute(&p);
    let f = a.function(0x1_4000_1060).map(|f| f.returns_value);
    assert_eq!(f, Some(Some(true)));
}

/// `G`: `eax` is untouched on both paths of the branch, so the join keeps the
/// constant and the function returns 7.
#[test]
fn const_survives_join() {
    let out = dc(0x1130);
    assert!(
        out.contains("return 7;"),
        "join dropped the constant:\n{out}"
    );
}

/// A counted loop whose step is a constant other than one is a `for`.
///
/// `xor ecx,ecx; L: cmp ecx,10; jge X; add ecx,2; jmp L; X: mov eax,ecx;
/// ret`. A step that names another value is not a compound update:
/// `cmp ecx,edx; jge X; add ecx,edx; jmp` back.
#[test]
fn a_constant_step_other_than_one_is_a_for() {
    let code = [
        0x31, 0xc9, // ASM: xor ecx, ecx
        0x83, 0xf9, 0x0a, // ASM: cmp ecx, 10
        0x7d, 0x05, // ASM: jge +5
        0x83, 0xc1, 0x02, // ASM: add ecx, 2
        0xeb, 0xf6, // ASM: jmp -10
        0x89, 0xc8, // ASM: mov eax, ecx
        0xc3, // ASM: ret
    ];
    let text = decompiled(&program64(&code), 0x1_4000_1000);
    assert!(text.contains("for (") && text.contains("+= 2"), "{text}");
    let varied = [
        0x39, 0xd1, // ASM: cmp ecx, edx
        0x7d, 0x04, // ASM: jge +4
        0x01, 0xd1, // ASM: add ecx, edx
        0xeb, 0xf8, // ASM: jmp -8
        0x89, 0xc8, // ASM: mov eax, ecx
        0xc3, // ASM: ret
    ];
    let text = decompiled(&program64(&varied), 0x1_4000_1000);
    assert!(text.contains("+ a2"), "{text}");
    assert!(!text.contains("+="), "{text}");
}

/// `K` is a loop; the inner `if (rbx != 0) return rax;` may fold into the
/// loop guard (`while (rax < 5 && rbx == 0)`), which is the same program. The
/// latch goto never survives.
///
/// The counter may be declared `int32_t`, which its compare then reads
/// without a cast.
#[test]
fn nested_if_inside_while() {
    let out = dc(0x1180);
    assert!(
        out.contains("for (var1 = 0; (int32_t)var1 < 5")
            || out.contains("for (var1 = 0; var1 < 5")
            || out.contains("while ("),
        "no loop:
{out}"
    );
    assert!(
        out.contains("if (") || out.contains(" && "),
        "neither nested if nor merged guard:
{out}"
    );
    assert!(
        !out.contains("goto L_1185;"),
        "latch goto survived:
{out}"
    );
    assert!(
        out.contains("return var1;"),
        "no return:
{out}"
    );
}

/// `H`: `if (ecx == 0) goto ret; *a2 = ecx; ret:`.
///
/// The `ret` block has two predecessors, so it is the join, not the
/// if-body: an inverted `if` with the store, and no `return` in it: the
/// function ends after it, so the one shared exit needs no statement.
#[test]
fn if_body_with_shared_join_is_not_swallowed() {
    let out = dc(0x1150);
    assert!(
        out.contains("if (a1 != 0) {"),
        "inverted if expected:\n{out}"
    );
    assert!(
        out.contains("*(uint32_t*)a2 = a1;"),
        "store body missing:\n{out}"
    );
    assert_eq!(
        out.matches("return").count(),
        0,
        "the if must end the function, no return in it:\n{out}"
    );
}

/// `G`: the branch's only effect is `inc ecx`, dead at the return, so no empty
/// `if` survives and the constant still flows to the return.
#[test]
fn dead_if_body_is_dropped() {
    let out = dc(0x1130);
    assert!(!out.contains("if ("), "empty if survived:\n{out}");
    assert!(out.contains("return 7;"), "constant lost:\n{out}");
}

/// `W`: `mov ecx, 1; jmp A` renders as a tail call, `return sub_1020(...)`.
#[test]
fn tail_call_renders_as_return_call() {
    let out = dc(0x1240);
    assert!(out.contains("return sub_1020("), "{out}");
    assert!(
        !out.lines()
            .any(|l| !l.starts_with("static inline ") && l.contains("return 1;")),
        "A's body leaked into W:\n{out}"
    );
}

/// `E1`: on the edge where `rcx` is known to be zero, `rcx + 25` folds to `25`.
#[test]
fn equality_branch_makes_the_variable_a_constant_inside() {
    let out = dc(0x13c0);
    assert!(out.contains("return 25;"), "{out}");
    assert!(!out.contains("rcx + 25"), "{out}");
    assert!(out.contains("return 1;"), "{out}");
}

/// `CC`: a chain block whose condition is constant is not merged into the
/// guard as `a1 != 0 || 0 == 0`; its dead edge is pruned, so the merged form
/// left a `goto` to a block that was never emitted.
#[test]
fn constant_condition_block_is_not_merged_into_a_guard() {
    let out = dc(0x1430);
    for label in out.lines().filter_map(|l| l.trim().strip_prefix("goto L_")) {
        let label = label.trim_end_matches(';');
        assert!(
            out.contains(&format!("L_{label}:")),
            "dangling goto L_{label}:\n{out}"
        );
    }
    assert!(!out.contains("0 == 0"), "{out}");
    assert!(out.contains("return 0;"), "{out}");
}

/// `FJ`: `test eax, eax` on both edges into the join that reads the flags
/// is re-expressed over `rax`, so the flags agree at the join and the `sete`
/// lifts instead of staying an `/* asm */` comment.
#[test]
fn same_comparison_on_both_edges_survives_the_join() {
    let out = dc(0x1450);
    assert!(!out.contains("/* sete"), "{out}");
    assert!(out.contains("var1 == 0"), "{out}");
}

/// `FJ8`: the byte form of `FJ`; the compared operand is `rax` on both
/// edges once `rax` is written out (its value is a masked byte, so the byte
/// test needs no mask), so the `sete` lifts.
#[test]
fn byte_comparison_on_both_edges_survives_the_join() {
    let out = dc(0x1490);
    assert!(!out.contains("/* sete"), "{out}");
    assert!(out.contains("return var1 == 0;"), "{out}");
    assert!(!out.contains("(var1 & 0xff) == 0"), "{out}");
}

/// `FM`: the edges compare memory at different addresses, so no register can
/// carry the agreement.
///
/// Each edge computes the join's condition, the `setl` lifts, and with the
/// joined `setl; ret` copied into each arm every arm returns its own
/// comparison with no temporary left.
#[test]
fn differing_comparisons_reach_the_join_as_a_truth_temporary() {
    let out = dc(0x14d0);
    assert!(!out.contains("/* setl"), "{out}");
    assert!(
        out.contains("return (int32_t)*(uint32_t*)(a2 + 4) < 5;"),
        "{out}"
    );
    assert!(out.contains("return (int32_t)*(uint32_t*)a2 < 5;"), "{out}");
    assert!(!out.contains("tmp_"), "{out}");
}

/// `ADC3`: a multiword add chains its carry through two `adc` into memory
/// and `setb` reads the carry out of the second; the carry out of an `adc`
/// is `uaddo(l, r) | uaddo(l + r, cf)`.
#[test]
fn adc_chain_carries_out_of_each_add() {
    let out = dc(0x1520);
    assert!(!out.contains("/* adc"), "{out}");
    assert!(!out.contains("/* setb"), "{out}");
    assert!(out.matches("uaddo32(").count() >= 2, "{out}");
}

/// `DC`: `sub ecx, 1; cmp ecx, 1` tests `a1 - 1 == 1`, which renders as
/// `a1 == 2` (and the edge assumption folds the taken arm's return to `2`).
#[test]
fn dec_chain_comparison_folds_onto_the_variable() {
    let out = dc(0x1530);
    assert!(out.contains("a1 == 2") || out.contains("a1 != 2"), "{out}");
    assert!(!out.contains("a1 - 1"), "{out}");
}

/// `LD2`: a shared block that is both a branch target and a fall-through.
///
/// `D` must not be split across a copy that loses its jump: each arm returns
/// its own constant (`rdx = 60; return rdx;` folds to `return 60;`), the
/// `ecx == 6` arm returns 60 inside its branch, comparing the low half of
/// `a1`, the fall-through returns 0 once, and nothing is a goto.
#[test]
fn shared_block_heads_an_arm_and_its_copy_keeps_its_jump() {
    let out = dc(0x1590);
    assert!(!out.contains("goto"), "{out}");
    assert!(out.contains("*(uint32_t*)a2 = 1;"), "{out}");
    assert!(
        out.contains("if ((uint32_t)a1 == 6) {\n    return 60;\n  }"),
        "{out}"
    );
    assert_eq!(out.matches("return 0;").count(), 1, "{out}");
    assert!(out.trim_end().ends_with("return 0;"), "{out}");
}

/// `LX`: the scan loop leaves through its condition, written as a
/// `do { ... } while (c);`.
///
/// The loop's exit block is shared with the other arm and ends in a call;
/// it is the loop's continuation, the body ends `if (c) continue; break;`,
/// and the block is written once after the `if`.
#[test]
fn loop_exit_shared_with_the_other_arm_is_a_break() {
    let out = dc(0x15b0);
    assert!(
        out.contains("} while (*(uint8_t*)(a1 + var1) != 32);"),
        "{out}"
    );
    assert!(
        !out.contains("break;") && !out.contains("continue;"),
        "{out}"
    );
    assert!(!out.contains("goto"), "{out}");
    assert_eq!(out.matches("Base::vfunc_1(").count(), 1, "{out}");
}

/// `VT`: `call VD2; ret` hands `VD2`'s result to its own caller, which
/// discards it, so `VT` is `void` and the call is not bound to `rax`.
#[test]
fn tail_return_after_a_call_is_void_when_the_callers_result_is_unused() {
    let out = dc(0x1620);
    assert!(out.contains("// signature: void exported_vt("), "{out}");
    assert!(!out.contains("rax = exported_vd2"), "{out}");
    assert!(!out.contains("return rax"), "{out}");
}

/// A shared one-way block that falls into a shared return is copied whole
/// into each guard's arm.
///
/// `TC`'s two guards jump to `L: rax |= -1;`, which falls into `R: return
/// rax;`; the guard gets a copy of both, so no `goto` remains and the two
/// guards merge into one condition.
#[test]
fn one_way_chains_into_a_return_are_copied_into_arms() {
    let out = dc(0x1c60);
    assert!(!out.contains("goto "), "{out}");
    assert!(out.contains("if (a1 == 0 || a2 == 0) {"), "{out}");
    assert!(out.contains("return a1;"), "{out}");
}

/// A loop whose break arms and fall-through share one return keeps every
/// label it jumps to.
///
/// `LP`'s arms `rax = 1;` and `rax = 2;` and its fall-through `rax = -1;`
/// all reach `R: return rax;` (its first arm now serves as the loop's
/// condition), and `LP2` puts the arms inside an if/else whose copies of
/// the return once left the loop's `goto` dangling; whatever the
/// structurer copies, no `goto` may be left without its label.
#[test]
fn loop_arms_sharing_a_return_keep_their_labels() {
    for entry in [0x1c80, 0x1cb0] {
        let out = dc(entry);
        for line in out.lines() {
            let t = line.trim();
            if let Some(target) = t.strip_prefix("goto ").and_then(|g| g.strip_suffix(';')) {
                assert!(
                    out.contains(&format!("{target}:")),
                    "dangling {target}: {out}"
                );
            }
        }
        assert!(out.contains("while ("), "{out}");
    }
}

/// A tail with a call is copied when nothing else structures.
///
/// `TL`'s loop exit `E` reaches `return Base::vfunc_1(1, ...)` through a tail
/// whose call keeps it out of the first attempt, and the loop's exits meet
/// nowhere, so only a copy of the calling tail writes the exit inline; the
/// second attempt copies it and no `goto` remains, while `LD`'s ladder,
/// which structures at the first attempt, still writes its call once.
#[test]
fn tails_with_a_call_are_copied_as_a_last_resort() {
    let out = dc(0x1d90);
    assert!(!out.contains("goto "), "{out}");
    assert!(out.contains("while (1) {"), "{out}");
    assert!(out.matches("Base::vfunc_1(").count() >= 2, "{out}");
    let ladder = dc(0x1550);
    assert_eq!(ladder.matches("Base::vfunc_1(").count(), 1, "{ladder}");
}

/// A shared return jumped to from two sites of one arm is copied to both,
/// so the arms still meet at their tail.
///
/// `JT`'s second arm returns early from two places; with the return copied
/// into each, both arms leave only into the two-call tail, which is written
/// once after the if/else instead of being copied into an arm.
#[test]
fn shared_return_from_two_sites_still_joins() {
    let out = dc(0x1e70);
    assert!(!out.contains("goto "), "{out}");
    assert!(out.contains("} else {"), "{out}");
    assert_eq!(out.matches("Base::vfunc_1(").count(), 4, "{out}");
}

/// Two guards that share a small one-way block are one guard when the
/// second tests a call's result alone.
///
/// `GX`'s guards both jump to `X: rdi = 0;`, which leads into the join the
/// main path falls into; the second guard tests what a call returned, so
/// it is the first one's second term, `X` is the one arm the pair guards,
/// written once, and no `goto` remains.
#[test]
fn shared_one_way_block_is_copied_into_the_other_arm() {
    let out = dc(0x1f00);
    assert!(!out.contains("goto "), "{out}");
    assert!(
        out.contains("if (a1 == 0 || Base::vfunc_1() != 0) {"),
        "{out}"
    );
    assert_eq!(out.matches("var1 = 0;").count(), 1, "{out}");
    assert!(out.contains("return var1"), "{out}");
}

/// A `goto` whose label follows across the closing brace of its `if` is
/// dropped.
///
/// `GJ`'s outer arm holds an inner branch and ends in a jump to the block
/// the other path takes, so the arm's text ends `goto L;` right before `}`
/// and `L:`; falling out of the `if` reaches the label anyway.
#[test]
fn a_goto_into_the_label_after_its_branch_is_dropped() {
    let out = dc(0x4000);
    assert!(out.contains("if (a1 == 0) {"), "{out}");
    assert!(!out.contains("goto "), "{out}");
    assert!(!out.contains("L_"), "{out}");
}

/// A guard whose arm has two exits structures once its call is a term.
///
/// `GC`'s guarded arm calls and leaves both to the join `J` and to `F`, the
/// join falling into `F`. The call's result decides alone, so it is the
/// guard's second term and the two tests guard the stores together, with
/// no jump over a run left. The callee is a bare `ret`, which leaves `rcx`
/// and `rdx` as it found them, so the stores still read the parameters.
#[test]
fn conditional_gotos_over_a_short_run_become_an_if() {
    let out = dc(0x4180);
    assert!(
        out.contains("if (a1 == 0 || Base::vfunc_1() != 0) {"),
        "{out}"
    );
    assert_eq!(out.matches("goto ").count(), 0, "{out}");
    assert_eq!(out.matches("return 13;").count(), 1, "{out}");
    assert!(out.contains("*(uint32_t*)a2 = a1;"), "{out}");
}

/// An `xadd` leaves the flags of the addition it performed, so the branch
/// after it reads the sum and not an opaque condition.
///
/// `XA` stores the addend's partner on the stack, adds `0x10` through the
/// exchange, and branches on the sum reaching zero.
#[test]
fn an_xadd_branch_reads_the_additions_flags() {
    let out = dc(0x5910);
    assert!(out.contains("xadd32(home_10, 16);"), "{out}");
    assert!(out.contains("a2 == 0xfffffff0"), "{out}");
}

/// A `cmpxchg` leaves the flags of the compare that decided the exchange,
/// so the branch after it reads whether the old value matched the
/// accumulator.
///
/// `CX` compares the accumulator with `5` and exchanges `a2` in; the
/// branch reads the match through `rax`, which the exchange leaves
/// holding the old value either way.
#[test]
fn a_cmpxchg_branch_reads_the_compares_zero_flag() {
    let out = dc(0x5930);
    assert!(out.contains("cmpxchg32(*(uint32_t*)a1, 5, a2);"), "{out}");
    assert!(out.contains("var1 == 5"), "{out}");
}

/// A loop whose head is the entry block structures and carries its
/// parameter correctly.
///
/// `LP` walks a list and jumps back to its first instruction. The entry
/// block's environment joins with the back edge like any other join, so
/// the register the loop advances is written from the parameter once at
/// the top (`rcx = a1;`) and the body reads and advances that register,
/// never the parameter's original value; and the loop structures instead
/// of jumping to a label the emitter used to omit.
#[test]
fn loops_headed_by_the_entry_block_carry_their_parameter() {
    let out = dc(0x47a0);
    assert!(!out.contains("goto"), "{out}");
    assert!(out.contains("var1 = a1;"), "{out}");
    assert!(out.contains("do {"), "{out}");
    assert!(out.contains("} while (var1 != 0);"), "{out}");
    assert!(out.contains("var1 = *(uint64_t*)var1;"), "{out}");
    assert!(out.contains("*(uint8_t*)(var1 + 0x34) ^= 1;"), "{out}");
}

/// A block nothing reaches inside a loop's address range does not keep the
/// loop from structuring.
///
/// `xor ecx,ecx; L: mov eax,0x41; cmp al,0x43; jl S; mov eax,0x43; S: mov
/// [rdx+rcx],al; inc ecx; cmp ecx,r8d; jb L; ret`: the compare folds, so
/// the `mov eax,0x43` between the loop's blocks is dead, and the loop is
/// one `do`/`while` rather than a rotated `while` that writes its first
/// block twice, once in front of the loop and once inside it.
#[test]
fn a_dead_block_inside_a_loop_does_not_veto_it() {
    let code = [
        0x31, 0xc9, 0xb8, 0x41, 0x00, 0x00, 0x00, 0x3c, 0x43, 0x7c, 0x05, 0xb8, 0x43, 0x00, 0x00,
        0x00, 0x88, 0x04, 0x0a, 0xff, 0xc1, 0x44, 0x39, 0xc1, 0x72, 0xe8, 0xc3,
    ];
    let p = program64(&code);
    let text = decompiled(&p, 0x1_4000_1000);
    assert!(text.contains("unreachable"), "{text}");
    assert!(!text.contains("goto"), "{text}");
    assert!(text.contains("do {"), "{text}");
    assert_eq!(text.matches("var1 += 1;").count(), 1, "{text}");
}

/// Conditions a text pass negates, and `setcc` results joined before one
/// test, read as `&&` and `||` chains.
///
/// `test ecx,ecx; sete al; test edx,edx; setle dl; or al,dl; jne Z; ...`
/// is one test of `a1 == 0 | a2 <= 0`, which reads `a1 == 0 || a2 <= 0`
/// in the guard and `a1 != 0 && a2 > 0` in its negation, never as a `|`
/// of truth values or under a `!`.
#[test]
fn joined_truth_values_read_as_a_chain() {
    let code = [
        0x85, 0xc9, 0x0f, 0x94, 0xc0, 0x85, 0xd2, 0x0f, 0x9e, 0xc2, 0x08, 0xd0, 0x75, 0x06, 0xb8,
        0x07, 0x00, 0x00, 0x00, 0xc3, 0x31, 0xc0, 0xc3,
    ];
    let p = program64(&code);
    let text = decompiled(&p, 0x1_4000_1000);
    assert!(!text.contains(" | "), "{text}");
    assert!(!text.contains("!("), "{text}");
    assert!(
        text.contains("if (a1 == 0 || a2 <= 0) {") || text.contains("if (a1 != 0 && a2 > 0) {"),
        "{text}"
    );
}

/// Two copies of one test on two paths are one test, where the paths meet.
///
/// `test cl,1; je A; call F1; test bl,2; je E; T: call F2; jmp E; A: test
/// bl,2; jne T; E: ret` (`F1` and `F2` each `mov eax,1; ret`) tests `bl &
/// 2` after each arm of the first `if`, the copies sending each outcome to
/// the same blocks; read as one block, the two `if`s follow one another and
/// the test is written once.
#[test]
fn copies_of_one_test_are_one_test() {
    let mut code = vec![
        0xf6, 0xc1, 0x01, 0x74, 0x11, 0xe8, 0x36, 0x00, 0x00, 0x00, 0xf6, 0xc3, 0x02, 0x74, 0x0c,
        0xe8, 0x3c, 0x00, 0x00, 0x00, 0xeb, 0x05, 0xf6, 0xc3, 0x02, 0x75, 0xf4, 0xc3,
    ];
    code.resize(0x40, 0xcc);
    code.extend_from_slice(&[0xb8, 0x01, 0x00, 0x00, 0x00, 0xc3]);
    code.resize(0x50, 0xcc);
    code.extend_from_slice(&[0xb8, 0x01, 0x00, 0x00, 0x00, 0xc3]);
    let p = program64(&code);
    let text = decompiled(&p, 0x1_4000_1000);
    assert!(!text.contains("goto"), "{text}");
    let calls = text
        .lines()
        .filter(|l| !l.starts_with("static inline ") && l.contains("sub_140001050("))
        .count();
    assert_eq!(calls, 1, "{text}");
    assert_eq!(text.matches("& 2").count(), 1, "{text}");
}

/// A loop whose body ends `if (c) break;` is a `do`/`while` on `!c`.
///
/// `xor eax,eax; xor ecx,ecx; test r8d,r8d; je X; L: cmp byte [rdx+rcx],0;
/// je S; inc eax; S: inc ecx; cmp ecx,r8d; jae X; jmp L; X: add eax,ecx;
/// ret`: the latch leaves on its taken side and goes round through a jump,
/// so the body's last line breaks out, and the loop reads as the bottom
/// test it is. Every use of `r8d` is 32 bits, so `a3` is `uint32_t` and
/// the condition does not cast it.
#[test]
fn a_loop_ending_in_a_conditional_break_is_a_do_while() {
    let code = [
        0x31, 0xc0, 0x31, 0xc9, 0x45, 0x85, 0xc0, 0x74, 0x11, 0x80, 0x3c, 0x0a, 0x00, 0x74, 0x02,
        0xff, 0xc0, 0xff, 0xc1, 0x44, 0x39, 0xc1, 0x73, 0x02, 0xeb, 0xef, 0x01, 0xc8, 0xc3,
    ];
    let p = program64(&code);
    let text = decompiled(&p, 0x1_4000_1000);
    assert!(!text.contains("while (1)"), "{text}");
    assert!(!text.contains("break;"), "{text}");
    assert!(
        text.lines()
            .any(|l| l.contains("signature:") && l.contains("uint32_t a3")),
        "{text}"
    );
    assert!(
        text.lines()
            .any(|l| l.contains("} while (") && l.contains("a3") && !l.contains("(uint32_t)a3")),
        "{text}"
    );
}

/// A loop's escapes to one returning tail carry the tail.
///
/// `ET3`'s loop escapes twice to one error tail holding a call, each escape
/// a test of a call's result; with the calls in the tests the two escapes
/// are one guard, `Base::vfunc_1() == 0 || Base::vfunc_1() == 0`, the
/// second call made only when the first returned nonzero, and the tail is
/// written once inside it with no jump left.
#[test]
fn loop_escapes_to_a_returning_tail_carry_it() {
    let out = dc(0x4900);
    assert!(!out.contains("goto"), "{out}");
    assert!(
        out.contains("for (var1 = a1; *(uint32_t*)var1 != 0; var1 += 8) {"),
        "{out}"
    );
    assert!(
        out.contains("if (Base::vfunc_1() == 0 || Base::vfunc_1() == 0) {"),
        "{out}"
    );
    assert_eq!(out.matches("return 7;").count(), 1, "{out}");
}

/// A conditional `goto` over a run holding a nested block becomes an `if`
/// around the run.
///
/// `FC`'s guarded arm holds its own `if`; the arm's run is label-free, so
/// the guard inverts around it and the nested block sits one level deeper.
/// The call before it is to a bare `ret`, which leaves `rcx` and `rdx` the
/// parameters they were.
#[test]
fn conditional_gotos_over_nested_blocks_become_an_if() {
    let out = dc(0x4930);
    assert!(!out.contains("goto"), "{out}");
    assert!(out.contains("if (a1 != 0) {"), "{out}");
    assert!(out.contains("  if (Base::vfunc_1() != 0) {"), "{out}");
    assert!(out.contains("    *(uint32_t*)a2 = a1;"), "{out}");
}

/// A conditional `goto` over a run with internal jumps still folds when
/// the run's labels are targeted only from inside it.
///
/// The text is the shape of the client's `sub_140d36f00`: a ladder whose
/// first arm jumps past the other arms to a label, while one of those arms
/// jumps to a label inside the skipped run. The guard inverts around the
/// run, the returning tails the inner jumps reach are copied to them, and
/// the first arm's short tail becomes the early return, so no jump is
/// left.
#[test]
fn conditional_gotos_over_self_contained_runs_become_an_if() {
    let body = "if (a1 == 1) goto L_7f;
if (a1 == 2) {
  r9 = 1;
} else {
  r9 = 2;
  if (a1 == 3) goto L_86;
  r9 = 2;
  if (a1 == 4) goto L_76;
  return Base::vfunc_1(a1);
}
L_76:
rax = 3;
goto L_8d;
L_7f:
r9 = 1;
L_86:
rax = 4;
L_8d:
return rax + r9;
";
    let out = cleanup(body);
    assert!(out.contains("if (a1 == 1) {"), "{out}");
    assert!(!out.contains("goto"), "{out}");
    assert_eq!(out.matches("return Base::vfunc_1(a1);").count(), 1, "{out}");
}

/// A return beside the fall-through is the arm, and the rest is not an `else`.
///
/// `jz` to `mov eax, ecx; add eax, 2; ret`, with `mov eax, 1; ret` as the
/// other side: the zero arm is `return 2` and the other return follows it.
/// Two `ret`s, `mov eax, 1` and `mov eax, 2`, print the same way. Neither
/// wraps the second return in `else`.
#[test]
fn a_return_beside_a_fall_through_is_not_an_else() {
    let fall = &[
        0x85, 0xc9, // ASM: test ecx,ecx
        0x74, 0x06, // ASM: jz rest
        0xb8, 0x01, 0x00, 0x00, 0x00, // ASM: mov eax,1
        0xc3, // ASM: ret
        0x89, 0xc8, // ASM: mov eax,ecx
        0x83, 0xc0, 0x02, // ASM: add eax,2
        0xc3, // ASM: ret
    ];
    let text = decompiled(&program64(fall), 0x1_4000_1000);
    assert!(
        text.contains("if (a1 == 0) {\n  return 2;\n}\nreturn 1;"),
        "{text}"
    );
    assert!(!text.contains("else"), "{text}");
    let both = &[
        0x85, 0xc9, // ASM: test ecx,ecx
        0x74, 0x06, // ASM: jz other
        0xb8, 0x01, 0x00, 0x00, 0x00, // ASM: mov eax,1
        0xc3, // ASM: ret
        0xb8, 0x02, 0x00, 0x00, 0x00, // ASM: mov eax,2
        0xc3, // ASM: ret
    ];
    let text = decompiled(&program64(both), 0x1_4000_1000);
    assert!(
        text.contains("if (a1 == 0) {\n  return 2;\n}\nreturn 1;"),
        "{text}"
    );
    assert!(!text.contains("else"), "{text}");
}

/// The `else` of an `else if (v != K)` arm names `K`.
///
/// `EN3`'s chain ends `else if (a1 != 4) { rdx = "Normal"; } else { rdx =
/// "Down"; }`, so `Down = 4` joins the table and the default does not.
#[test]
fn else_defaults_name_their_constant() {
    let out = dc(0x4a50);
    assert!(
        out.contains("// enum values of a1: 4 values, Normal = 0, Pressed = 1, Over = 2, Down = 4"),
        "{out}"
    );
}

/// A byte-counting loop is the `strlen` it compiles from.
///
/// `SL` seeds `rax` with all ones, then bumps it until the byte at
/// `a1 + rax` is zero: `return strlen(a1);`. The text form pins the rule
/// itself: a base loaded between the seed and the loop, and a loop over
/// 16-bit elements for `wcslen`.
#[test]
fn strlen_loops_render_as_calls() {
    let out = dc(0x4b00);
    assert!(out.contains("return strlen(a1);"), "{out}");
    assert!(!out.contains("do {"), "{out}");
    let text = "r8 |= -1;\nrdx = *(uint64_t*)rcx;\ndo {\n    r8 += 1;\n} while (*(uint8_t*)(rdx + r8) != 0);\nr9 = 0xffffffff;\ndo {\n    r9 += 1;\n} while (((uint16_t*)a2)[r9] != 0);\nreturn r8 + r9;\n";
    let out = cleanup(text);
    assert!(
        out.contains(
            "rdx = *(uint64_t*)rcx;\nr8 = strlen(rdx);\nr9 = wcslen(a2);\nreturn r8 + r9;"
        ),
        "{out}"
    );
}

/// A carry-guarded multiply or add is the saturating operation.
///
/// `SA` multiplies `a1` by 16 and adds 8, each time moving all ones in on
/// the carry: `add_sat(mul_sat(0x10, a1), 8)`, the allocation-size guard a
/// standard library compiles to.
#[test]
fn carry_guarded_arithmetic_saturates() {
    let out = dc(0x4b60);
    assert!(
        out.contains("return add_sat(mul_sat(0x10, a1), 8);"),
        "{out}"
    );
}

/// The trailing jump of an `if` arm becomes the `else` around what it skips.
///
/// The arm ends `goto L_1;` and `L_1:` follows the run at the `if`'s own
/// indentation, so the run is what runs when the condition is false. A run
/// a later jump goes back into is that jump's loop, kept whole.
#[test]
fn trailing_jumps_of_an_arm_become_an_else() {
    let text = "if (a1 == 1) {\n  rax = sub_1000(a1);\n  goto L_1;\n}\nrax = 20;\nsub_1010(rax);\nL_1:\nreturn rax;\n";
    let out = cleanup(text);
    assert!(
        out.contains("} else {\n  rax = 20;\n  sub_1010(rax);\n}\nreturn rax;"),
        "{out}"
    );
    assert!(!out.contains("goto"), "{out}");
    let entered = "if (a1 == 1) {\n  goto L_1;\n}\nL_2:\nrax = 20;\nif (rax != 0) goto L_2;\nL_1:\nreturn rax;\n";
    let out = cleanup(entered);
    assert!(
        out.contains("if (a1 != 1) {\n  do {\n    rax = 20;\n  } while (rax != 0);\n}"),
        "a run entered from outside was not kept whole as its loop:\n{out}"
    );
}

/// A block one jump reaches moves to where the jump is.
///
/// The label is not a shared exit, so the jump and the label both go and
/// nothing is duplicated. A one-line returning tail is copied by the tail
/// rule instead; this one moves the block the tail rule is too small for.
/// A block that can be fallen into from above stays where it is, since
/// moving it would change what runs; the one here is also too long for the
/// tail rule to copy, so nothing else touches it either.
#[test]
fn blocks_one_jump_reaches_move_to_it() {
    let text = concat!(
        "switch (a1) {\n",
        "case 0: goto L_1;\n",
        "case 1: goto L_2;\n",
        "}\n",
        "return 9;\n",
        "L_1:\n",
        "sub_1000(a1);\n",
        "sub_1001(a1);\n",
        "sub_1002(a1);\n",
        "sub_1003(a1);\n",
        "sub_1004(a1);\n",
        "return 1;\n",
        "L_2:\n",
        "return 2;\n",
    );
    let out = cleanup(text);
    assert!(!out.contains("goto"), "{out}");
    assert!(!out.contains("L_1:") && !out.contains("L_2:"), "{out}");
    assert!(out.contains("case 0: {"), "{out}");
    assert!(out.contains("  sub_1004(a1);"), "{out}");
    assert!(out.contains("case 1: return 2;"), "{out}");
    let falls = concat!(
        "switch (a1) {\n",
        "case 0: goto L_3;\n",
        "}\n",
        "sub_1000(a1);\n",
        "L_3:\n",
        "sub_1001(a1);\n",
        "sub_1002(a1);\n",
        "sub_1003(a1);\n",
        "sub_1004(a1);\n",
        "sub_1005(a1);\n",
        "sub_1006(a1);\n",
        "sub_1007(a1);\n",
        "sub_1008(a1);\n",
        "sub_1009(a1);\n",
        "return 1;\n",
    );
    let out = cleanup(falls);
    assert!(
        out.contains("L_3:") && out.contains("goto L_3;"),
        "a block reachable from above moved: {out}"
    );
}

/// A shared tail that nests still leaves no jump to it.
///
/// The exit tests a flag before returning, so the run holds a block. Both
/// jumps skip the same return, so the guards nest around that return and
/// the tail follows once, or the tail is copied to each jump; either way
/// no `goto` is left and the block keeps its braces.
#[test]
fn shared_tails_may_nest() {
    let text = concat!(
        "if (a1 == 0) goto L_1;\n",
        "if (a1 == 1) goto L_1;\n",
        "rax = sub_2000(a1);\n",
        "return rax;\n",
        "L_1:\n",
        "if (a2 != 0) {\n",
        "  sub_1000(a2);\n",
        "}\n",
        "return 0;\n",
    );
    let out = cleanup(text);
    assert!(!out.contains("goto"), "{out}");
    assert!(out.contains("return sub_2000(a1);"), "{out}");
    assert!(out.contains("sub_1000(a2);"), "{out}");
    assert!(out.contains("if (a2 != 0) {"), "{out}");
}

/// A jump whose label follows another label falls to it all the same.
///
/// `goto L_2;` closes an `if` and `L_1:` stands between the brace and
/// `L_2:`. A label runs nothing, so the jump goes.
#[test]
fn a_jump_falls_to_its_label_past_another_label() {
    let text = concat!(
        "if (a1 != 0) {\n",
        "  sub_1(a1);\n",
        "  goto L_2;\n",
        "}\n",
        "L_1:\n",
        "L_2:\n",
        "sub_3(a1);\n",
        "if (a2 != 0) goto L_1;\n",
        "return 0;\n",
    );
    let out = cleanup(text);
    assert!(!out.contains("goto L_2"), "{out}");
}

/// A jump that ends an arm and skips a run that leaves its block is the
/// `else` of that run.
///
/// `goto L_1;` skips `sub_2(a1);`, and the brace after that run falls to
/// `L_1:`, so the run is the `else` and no jump is left.
#[test]
fn an_arm_jump_over_a_run_that_leaves_its_block_is_an_else() {
    let text = concat!(
        "if (a1 != 0) {\n",
        "  if (a2 != 0) {\n",
        "    sub_1(a1);\n",
        "    goto L_1;\n",
        "  }\n",
        "  sub_2(a1);\n",
        "}\n",
        "L_1:\n",
        "return sub_3(a1);\n",
    );
    let out = cleanup(text);
    assert!(!out.contains("goto"), "{out}");
    assert!(out.contains("} else {"), "{out}");
}

/// A test both arms of an `if`/`else` end with is made once after it.
///
/// Each arm ends in `if (a2 != 0) goto L_1;`. Moved after the `if`, the
/// one test guards `sub_3(a1);` and no jump is left.
#[test]
fn a_test_both_arms_end_with_is_made_once() {
    let text = concat!(
        "if (a1 != 0) {\n",
        "  sub_1(a1);\n",
        "  if (a2 != 0) goto L_1;\n",
        "} else {\n",
        "  sub_2(a1);\n",
        "  if (a2 != 0) goto L_1;\n",
        "}\n",
        "sub_3(a1);\n",
        "L_1:\n",
        "return 0;\n",
    );
    let out = cleanup(text);
    assert!(!out.contains("goto"), "{out}");
    assert_eq!(out.matches("a2").count(), 1, "{out}");
}

/// A guard jump over a run that leaves its block folds into an `if`.
///
/// `if (a2 == 0) goto L_1;` skips `sub_1(a1);` and the closing brace
/// after it falls to `L_1:`, so the run is guarded by `a2 != 0`.
#[test]
fn a_guard_over_a_run_that_leaves_its_block_folds() {
    let text = concat!(
        "if (a1 != 0) {\n",
        "  if (a2 == 0) goto L_1;\n",
        "  sub_1(a1);\n",
        "}\n",
        "L_1:\n",
        "return 0;\n",
    );
    let out = cleanup(text);
    assert!(!out.contains("goto"), "{out}");
    assert!(out.contains("if (a2 != 0) {"), "{out}");
}

/// A call through a one-instruction thunk takes the arguments it reads.
///
/// `TJ` is a bare `jmp`, so it reads no argument register itself; counting
/// only what it reads left the call open-ended and it printed `edx` too,
/// which `FW3` at the end of the jump never reads.
#[test]
fn a_call_through_a_jump_thunk_stops_at_what_it_reads() {
    let out = dc(0x4f70);
    assert!(out.contains("sub_4f60(85)"), "{out}");
    assert!(!out.contains("102"), "{out}");
}

/// Every goto lands on a label, and a cross-loop jump stays a goto.
///
/// `LB` is three `while (1)` loops. The outer entry is 0x5273, the inner
/// entry is 0x525f, and 0x5287 jumps to itself. `goto L_5251` falls out of
/// the inner loop. `goto L_5287` is that self-loop. Either one written as
/// `break` or `continue` leaves the wrong loop. The inner loop still
/// restarts 0x525f, by a `continue` or by falling off its body.
#[test]
fn a_loop_entered_below_its_first_block_keeps_its_label() {
    let out = dc(0x5240);
    let labels: std::collections::BTreeSet<&str> = out
        .lines()
        .filter_map(|l| l.trim().strip_suffix(':'))
        .filter(|l| l.starts_with("L_"))
        .collect();
    for line in out.lines() {
        let t = line.trim();
        let Some(target) = t
            .strip_prefix("goto ")
            .or_else(|| t.rsplit_once(") goto ").map(|(_, g)| g))
            .and_then(|g| g.strip_suffix(';'))
            .filter(|g| g.starts_with("L_"))
        else {
            continue;
        };
        assert!(labels.contains(target), "{target} has no label: {out}");
    }
    for edge in [
        "goto L_525f;",
        "goto L_527d;",
        "goto L_5251;",
        "goto L_5287;",
    ] {
        assert!(
            out.contains(edge),
            "{edge} reads as break or continue: {out}"
        );
    }
    assert_eq!(
        out.matches("while (1)").count(),
        3,
        "expected three while (1) loops: {out}"
    );
}

/// A branch that leaves the function is a computed goto, not a label.
///
/// `JO` branches to 0x3000, which is `.data`: no block of the function
/// starts there, so a `goto L_3000;` would name a label the text never
/// writes.
#[test]
fn a_branch_that_leaves_is_a_computed_goto() {
    let out = dc(0x52a0);
    assert!(out.contains("goto *0x3000;"), "{out}");
    assert!(!out.contains("L_3000"), "{out}");
}

/// The code a loop breaks to is still there.
///
/// `BC`'s loops are left only by a `break` under a condition. Reading that
/// as no break at all made the loop endless, and everything after it was
/// dropped as text nothing reaches: the call to `E` disappeared.
#[test]
fn a_loop_left_by_a_conditional_break_keeps_what_follows() {
    let out = dc(0x52c0);
    assert!(
        out.contains("sub_5312"),
        "the call after the loops is gone: {out}"
    );
    for callee in ["sub_5300", "sub_5306", "sub_530c"] {
        assert!(out.contains(callee), "{callee} is missing: {out}");
    }
}

/// A loop two levels deep does not swallow the outer loop's break.
///
/// `NL` nests three loops, so the outer one's `break` stands below a brace
/// that closes two levels in. Counting nested loops without minding the
/// indent each closes at left that break unseen, the outer loop endless,
/// and the last call dropped as text nothing reaches.
#[test]
fn a_break_below_a_nested_loop_still_leaves_the_outer_one() {
    let out = dc(0x5320);
    assert!(
        out.contains("sub_5378"),
        "the call after the loops is gone: {out}"
    );
}

/// A break belongs to the loop it stands in.
///
/// `NB` runs a loop inside a loop, and the inner body jumps both back to
/// the outer loop's header and out past it. Written as the inner loop's
/// `continue` and `break` those jumps left the wrong loop, and the block
/// after the outer loop, which nothing else reaches, went with them. Each
/// block hands its own number to 0x5445, so a missing one is plain.
/// `goto L_5390` and `goto L_5407` both stay gotos. One leftover goto is
/// not enough.
#[test]
fn a_break_leaves_the_loop_it_stands_in() {
    let out = dc(0x5390);
    for n in 1..=11 {
        assert!(
            out.contains(&format!("({n})")),
            "block {n} is missing: {out}"
        );
    }
    assert!(
        out.contains("goto L_5390;"),
        "the jump back to the outer loop reads as the inner one's continue: {out}"
    );
    assert!(
        out.contains("goto L_5407;"),
        "the jump to 0x5407 reads as the inner loop's break or continue: {out}"
    );
}

/// A block that continues its own loop is not moved into another one.
///
/// `SL` runs two loops side by side inside a third, and one jumps into the
/// middle of the other. The block it lands on ends by continuing its own
/// loop; moved to the jump it continued the loop there instead, and the
/// rest of its loop was left reachable by nothing. Each block hands its own
/// number to 0x54cd, so a missing one is plain, and the text's paths must
/// be the binary's, so the jump back to the outer header read as the inner
/// loop's `break` or `continue` is plain too.
#[test]
fn a_block_that_continues_its_loop_stays_in_it() {
    use borer_engine::analysis::decompile::traces::{Structure, check_structure};
    let out = dc(0x5450);
    for n in 1..=8 {
        assert!(
            out.contains(&format!("({n})")),
            "block {n} is missing: {out}"
        );
    }
    let (p, o) = (fixture(), Overlay::default());
    let agrees = check_structure(&p, &Analysis::compute(&p), &o, 0x5450, &out);
    assert_eq!(agrees, Structure::Agrees, "{out}");
}

/// `FA`: one edge compares `eax` while `edx` holds the same value, the other
/// compares `edx`; both are re-expressed over `edx` and the `setl` lifts.
#[test]
fn aliased_comparison_on_both_edges_survives_the_join() {
    let out = dc(0x1470);
    assert!(!out.contains("/* setl"), "{out}");
    assert!(out.contains("var1 < 5"), "{out}");
}

/// `Y` and `W3` end at their noreturn calls: nothing after the call is rendered.
#[test]
fn noreturn_calls_end_the_text() {
    let y = dc(0x1270);
    assert!(y.contains("ExitProcess(1);"), "{y}");
    assert!(!y.contains("return 3;"), "Z's body leaked into Y:\n{y}");
    let w3 = dc(0x12d0);
    assert!(w3.contains("sub_12b0(3);"), "{w3}");
    assert!(!w3.contains("return 5;"), "dead tail survived:\n{w3}");
}

/// Inside a loop, a branch whose one side leaves the loop (here to a
/// return) and whose other side stays is `if (leaves) { return 1; }`,
/// with the staying side following, not a goto to the staying side.
#[test]
fn a_loop_exit_is_the_arm_and_the_staying_side_follows() {
    let code: &[u8] = &[
        0xbb, 0x03, 0x00, 0x00, 0x00, 0xe8, 0x36, 0x00, 0x00, 0x00, 0x85, 0xc0, 0x74, 0x09, 0xe8,
        0x3d, 0x00, 0x00, 0x00, 0x85, 0xc0, 0x75, 0x19, 0xff, 0xcb, 0x75, 0xea, 0x31, 0xc0, 0xc3,
        0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc,
        0xcc, 0xcc, 0xcc, 0xb8, 0x01, 0x00, 0x00, 0x00, 0xc3, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc,
        0xcc, 0xcc, 0xcc, 0xcc, 0x8b, 0x01, 0xc3, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc,
        0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0x8b, 0x41, 0x04, 0xc3,
    ];
    let p = program64(code);
    let text = decompiled(&p, 0x1_4000_1000);
    assert!(!text.contains("goto"), "{text}");
    assert!(text.contains("return 1;"), "{text}");
}

/// A branch at the end of an `if` arm whose jump side is the arm's join
/// falls into the join.
///
/// The other side is the guarded statement (`if (ecx == 7) break;`), not
/// `if (ecx != 7) goto L_join; break;`.
#[test]
fn a_branch_ending_an_arm_falls_into_the_join() {
    let code: &[u8] = &[
        0x31, 0xc0, 0x8b, 0x0a, 0x85, 0xc9, 0x75, 0x0b, 0x48, 0x83, 0xc2, 0x04, 0x41, 0xff, 0xc8,
        0x75, 0xf1, 0xeb, 0x07, 0x01, 0xc8, 0x83, 0xf9, 0x07, 0x75, 0xee, 0x83, 0xf9, 0x01, 0x74,
        0x2a, 0x83, 0xf9, 0x02, 0x74, 0x25, 0x83, 0xf9, 0x03, 0x74, 0x20, 0x83, 0xf9, 0x04, 0x74,
        0x1b, 0x83, 0xf9, 0x05, 0x74, 0x16, 0x83, 0xf9, 0x06, 0x74, 0x11, 0x83, 0xf9, 0x07, 0x74,
        0x0c, 0x83, 0xf9, 0x08, 0x74, 0x07, 0x83, 0xf9, 0x09, 0x74, 0x02, 0x31, 0xc0, 0xc3,
    ];
    let p = program64(code);
    let text = decompiled(&p, 0x1_4000_1000);
    assert!(!text.contains("goto"), "{text}");
    assert!(text.contains("== 7) break;"), "{text}");
}

/// A loop whose address range holds a block that is not the loop's is still
/// a loop.
///
/// Here a return the function's head jumps to lies between the loop's
/// blocks; it is left to the head, not folded into the body and not a
/// reason to give the loop up.
#[test]
fn a_loop_skips_the_block_in_its_range_that_is_not_its_own() {
    let code: &[u8] = &[
        0x31, 0xc0, 0x85, 0xc9, 0x7e, 0x0c, 0x03, 0x02, 0x48, 0x83, 0xc2, 0x04, 0x85, 0xc0, 0x78,
        0x02, 0xeb, 0x01, 0xc3, 0xff, 0xc9, 0x75, 0xef, 0xc3,
    ];
    let p = program64(code);
    let text = decompiled(&p, 0x1_4000_1000);
    assert!(!text.contains("goto"), "{text}");
    assert!(text.contains("while"), "{text}");
}

/// A byte result stays a byte beside a tail jump to a function whose width
/// nothing states.
///
/// `test ecx,ecx; jne L; call g; xor al,al; ret; L: jmp g`, with `g` at
/// 0x1040 loading `rax` whole: the exit the function writes itself hands
/// back `al`, and the jump hands on whatever `g` leaves, which no lane
/// bounds. Only a 32-bit lane needs the jump's width to hold; a byte one
/// is the function's own, as it was before the 32-bit lane existed, and
/// without it the exit printed `return rax & ~0xff;`.
#[test]
fn a_byte_result_beside_a_tail_jump_of_unknown_width_stays_a_byte() {
    let mut code = vec![
        0x85, 0xc9, 0x75, 0x08, 0xe8, 0x37, 0x00, 0x00, 0x00, 0x30, 0xc0, 0xc3, 0xe9, 0x2f, 0x00,
        0x00, 0x00,
    ];
    code.resize(0x40, 0xcc);
    code.extend_from_slice(&[0x48, 0x8b, 0x01, 0xc3]);
    let text = decompiled(&program64(&code), 0x1_4000_1000);
    assert!(
        text.contains("// signature: uint8_t sub_140001000("),
        "{text}"
    );
    assert!(!text.contains("& ~0xff"), "{text}");
}

/// A call the header says the text leaves out, written where its check
/// did not fold, ends the text's path when it never returns.
///
/// `f` calls `y`, then on `a1 == 0` calls `panic_const_add_overflow`,
/// which never returns, and else calls `x` and `z`. A text that writes
/// the panic at the end of its arm and lets C fall past it claims nothing
/// after it, so the steps it writes there are no path of its own; read as
/// a step it may skip, the panic would let the text go on to `x` and `y`,
/// which no path of the binary does.
#[test]
fn a_left_out_call_the_text_writes_ends_the_path_when_it_never_returns() {
    use borer_engine::analysis::decompile::traces::{Structure, check_structure};
    use borer_engine::program::{Symbol, SymbolKind};
    let mut code = vec![
        0x48, 0x83, 0xec, 0x28, // ASM: sub rsp, 0x28
        0xe8, 0x37, 0x00, 0x00, 0x00, // ASM: call y
        0x85, 0xc9, // ASM: test ecx, ecx
        0x74, 0x13, // ASM: je panics
        0xe8, 0x3e, 0x00, 0x00, 0x00, // ASM: call x
        0xe8, 0x49, 0x00, 0x00, 0x00, // ASM: call z
        0x48, 0x83, 0xc4, 0x28, // ASM: add rsp, 0x28
        0xc3, // ASM: ret
    ];
    code.resize(0x20, 0xcc);
    code.extend([0xe8, 0x4b, 0x00, 0x00, 0x00]); // ASM: call panic_const_add_overflow
    code.resize(0x40, 0xcc);
    code.push(0xc3); // ASM: ret
    code.resize(0x50, 0xcc);
    code.push(0xc3); // ASM: ret
    code.resize(0x60, 0xcc);
    code.push(0xc3); // ASM: ret
    code.resize(0x70, 0xcc);
    code.extend([0x0f, 0x0b]); // ASM: ud2
    let mut p = program64(&code);
    for (name, addr) in [
        ("y", 0x1_4000_1040),
        ("x", 0x1_4000_1050),
        ("z", 0x1_4000_1060),
        ("panic_const_add_overflow", 0x1_4000_1070),
    ] {
        p.symbols.push(Symbol {
            name: name.to_owned(),
            addr,
            kind: SymbolKind::Local,
        });
    }
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let text = "// f @ 0x140001000\n\
                // note: calls to panic_const_add_overflow are left out: rust overflow and bounds checks folded\n\
                \n\
                y();\n\
                if (a1 == 0) {\n\
                \x20 panic_const_add_overflow(0);\n\
                \x20 x();\n\
                \x20 y();\n\
                \x20 return;\n\
                }\n\
                x();\n\
                z();\n\
                return;\n";
    assert_eq!(
        check_structure(&p, &a, &o, 0x1_4000_1000, text),
        Structure::Agrees,
        "{text}"
    );
}

/// A jump that writes out a store the branch skipped over keeps it.
///
/// The entry stores `[rbp-48h]` (`local_60`) and compares; one side calls,
/// which writes the store out before it, and the other only jumps to the
/// join that reads it. That jump was taken for a detour and dropped with
/// the store it wrote out, so on that side the join read a `local_60`
/// nothing set (a Rust `Vec::push`).
#[test]
fn a_jump_that_writes_out_a_store_is_kept() {
    let mut code = vec![
        0x55, // ASM: push rbp
        0x48, 0x81, 0xec, 0x90, 0x00, 0x00, 0x00, // ASM: sub rsp, 0x90
        0x48, 0x8d, 0xac, 0x24, 0x80, 0x00, 0x00, 0x00, // ASM: lea rbp, [rsp+0x80]
        0x48, 0xc7, 0x45, 0x08, 0xfe, 0xff, 0xff, 0xff, // ASM: mov qword [rbp+8], -2
        0x89, 0x55, 0xac, // ASM: mov [rbp-0x54], edx
        0x48, 0x89, 0x4d, 0xb0, // ASM: mov [rbp-0x50], rcx
        0x48, 0x89, 0x4d, 0xc8, // ASM: mov [rbp-0x38], rcx
        0x89, 0x55, 0xd4, // ASM: mov [rbp-0x2c], edx
        0x48, 0xc7, 0x45, 0xd8, 0x04, 0x00, 0x00, 0x00, // ASM: mov qword [rbp-0x28], 4
        0x48, 0x8b, 0x41, 0x10, // ASM: mov rax, [rcx+0x10]
        0x48, 0x89, 0x45, 0xb8, // ASM: mov [rbp-0x48], rax
        0x48, 0x89, 0x45, 0xe0, // ASM: mov [rbp-0x20], rax
        0x48, 0x8b, 0x09, // ASM: mov rcx, [rcx]
        0x48, 0x89, 0x4d, 0xe8, // ASM: mov [rbp-0x18], rcx
        0x48, 0x89, 0x4d, 0xc0, // ASM: mov [rbp-0x40], rcx
        0x48, 0x3b, 0x45, 0xc0, // ASM: cmp rax, [rbp-0x40]
        0x74, 0x02, // ASM: je 0x14000104d
        0xeb, 0x0c, // ASM: jmp 0x140001059
        0x48, 0x8b, 0x4d, 0xb0, // ASM: mov rcx, [rbp-0x50]
        0xe8, 0xaa, 0x00, 0x00, 0x00, // ASM: call 0x140001100
        0x90, // ASM: nop
        0xeb, 0x00, // ASM: jmp 0x140001059
        0x48, 0x8b, 0x4d, 0xb0, // ASM: mov rcx, [rbp-0x50]
        0x48, 0x8b, 0x55, 0xb8, // ASM: mov rdx, [rbp-0x48]
        0x44, 0x8b, 0x4d, 0xac, // ASM: mov r9d, [rbp-0x54]
        0x4c, 0x8b, 0x41, 0x08, // ASM: mov r8, [rcx+8]
        0x4c, 0x89, 0x45, 0xf0, // ASM: mov [rbp-0x10], r8
        0x49, 0x89, 0xd2, // ASM: mov r10, rdx
        0x49, 0xc1, 0xe2, 0x02, // ASM: shl r10, 2
        0x4c, 0x89, 0xc0, // ASM: mov rax, r8
        0x4c, 0x01, 0xd0, // ASM: add rax, r10
        0x48, 0x89, 0x45, 0xf8, // ASM: mov [rbp-8], rax
        0x44, 0x89, 0x4d, 0x04, // ASM: mov [rbp+4], r9d
        0x48, 0x83, 0xc2, 0x01, // ASM: add rdx, 1
        0x48, 0x89, 0x51, 0x10, // ASM: mov [rcx+0x10], rdx
        0x48, 0x81, 0xc4, 0x90, 0x00, 0x00, 0x00, // ASM: add rsp, 0x90
        0x5d, // ASM: pop rbp
        0xc3, // ASM: ret
    ];
    code.resize(0x100, 0xcc);
    code.extend_from_slice(&[
        0x48, 0x8b, 0x01, // ASM: mov rax, [rcx]
        0x48, 0x83, 0xc0, 0x04, // ASM: add rax, 4
        0x48, 0x89, 0x01, // ASM: mov [rcx], rax
        0x48, 0x89, 0x49, 0x08, // ASM: mov [rcx+8], rcx
        0xc3, // ASM: ret
    ]);
    let text = runs_agree(&program64(&code), 0x1_4000_1000);
    assert!(text.contains("} else {"), "{text}");
}

/// A `_longjmp` import ends the text like any noreturn call, taking its
/// two declared arguments.
///
/// `mov ecx,buf; mov edx,1; call [_longjmp]; mov eax,7; ret` never runs
/// past the call, so the MSVC spelling of `longjmp` is among the names the
/// analysis knows never return and the walk ends the block at it: the dead
/// tail is not rendered, and the call renders the two arguments its
/// prototype declares, not four padded register slots.
#[test]
fn a_longjmp_import_ends_the_text_like_a_noreturn_call() {
    let code = [
        0xb9, 0x10, 0x20, 0x00, 0x14, // ASM: mov ecx,0x14002010
        0xba, 0x01, 0x00, 0x00, 0x00, // ASM: mov edx,1
        0xff, 0x15, 0xf0, 0x0f, 0x00, 0x00, // ASM: call [0x14002000]
        0xb8, 0x07, 0x00, 0x00, 0x00, // ASM: mov eax,7
        0xc3, // ASM: ret
    ];
    let p = program64_with_imports(
        &code,
        &[0; 0x20],
        &[(0x1_4000_2000, "api-ms-win-crt-runtime-l1-1-0.dll!_longjmp")],
    );
    let text = decompiled(&p, 0x1_4000_1000);
    assert!(
        text.lines()
            .any(|l| l.contains("_longjmp(") && l.contains(", 1);")),
        "{text}"
    );
    assert!(!text.contains("return"), "dead tail survived:\n{text}");
}

/// A call to a no-return import through a CET stub ends the path in the
/// text.
///
/// The stub opens with `endbr64` before its jump through the slot, and
/// GCC at `-O0` lays the return right after `call __stack_chk_fail`, so
/// a walk past the call read its result as the function's.
#[test]
fn a_noreturn_import_behind_an_endbr64_stub_ends_the_text() {
    use borer_engine::program::{Arch, BinaryFormat, Program, Section, Symbol, SymbolKind};
    let mut bytes = vec![0xccu8; 0x2000];
    let code: &[(usize, &[u8])] = &[
        (0x0, &[0xf3, 0x0f, 0x1e, 0xfa]),                   // ASM: endbr64
        (0x4, &[0xf2, 0xff, 0x25, 0xf5, 0x0f, 0x00, 0x00]), // ASM: bnd jmp [rip+0xff5]
        (0x40, &[0xb8, 0x07, 0x00, 0x00, 0x00]),            // ASM: mov eax,7
        (0x45, &[0x85, 0xff]),                              // ASM: test edi,edi
        (0x47, &[0x74, 0x05]),                              // ASM: je 0x104e
        (0x49, &[0xe8, 0xb2, 0xff, 0xff, 0xff]),            // ASM: call 0x1000
        (0x4e, &[0xc3]),                                    // ASM: ret
    ];
    for (at, b) in code {
        bytes[*at..*at + b.len()].copy_from_slice(b);
    }
    bytes[0x1000..0x1008].fill(0);
    let mut p = Program::raw(
        bytes,
        Arch::X86_64,
        0,
        Some(0x1040),
        vec![
            Section::mapped(".text", 0x1000, 0, 0x1000, false, true),
            Section::mapped(".got", 0x2000, 0x1000, 0x1000, false, false),
        ],
    );
    p.format = BinaryFormat::Elf;
    p.symbols.push(Symbol {
        name: "__stack_chk_fail".to_owned(),
        addr: 0x2000,
        kind: SymbolKind::Import,
    });
    let text = decompiled(&p, 0x1040);
    assert!(!text.contains("= __stack_chk_fail("), "{text}");
    assert!(text.contains("return 7;"), "{text}");
}

/// The code a catch the text could not wrap runs stays in the text.
///
/// The structurer writes it after the body under the label of the block
/// the runtime enters, which no `goto` names; the region's comment names
/// that block, and the label and its code are kept rather than read as
/// dead text after the `return`, while a label nothing names still goes
/// with the code after it.
#[test]
fn an_unwrapped_catch_keeps_the_code_it_runs() {
    let body = "// try 0x1000..0x1008 not structured, its bounds are not exact: \
                catch (...) at 0x1010, runs f::__catch_0_0 @ 0x2000\n\
                f();\n\
                return;\n\
                L_1010:\n\
                g();\n\
                return;\n\
                L_1020:\n\
                h();\n";
    let out = cleanup(body);
    assert!(out.contains("L_1010:\ng();"), "{out}");
    assert!(!out.contains("h();"), "{out}");
}
