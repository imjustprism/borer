//! ARM32 functions decompiled under the ARM32 procedure call standard,
//! and their text replayed against the ARM32 machine.
//!
//! The routines, T32 and A32 in one image, are assembled by LLVM (`clang
//! --target=armv7a-linux-gnueabihf -mcpu=cortex-a15 -mfpu=neon-vfpv4`)
//! and checked against `llvm-objdump`; each instruction's comment is its
//! text.
#![expect(
    clippy::missing_panics_doc,
    clippy::expect_used,
    reason = "assertions are the point of a test"
)]

use borer_engine::analysis::decompile::decompile;
use borer_engine::analysis::decompile::replay::{replay_function, replay_tsv};
use borer_engine::analysis::decompile::verify_a32::{verify, verify_tsv};
use borer_engine::analysis::{Analysis, Overlay};
use borer_engine::isa::a32::{Mode, Modes};
use borer_engine::program::{Arch, Feature, Program, Section, Symbol, SymbolKind};

/// Where the routines are placed.
const BASE: u64 = 0x4_0000;

/// Where the A32 routines start; the T32 ones come before.
const ARM_FROM: u64 = BASE + 0x68;

/// Each routine's name and its offset from [`BASE`].
const NAMES: [(&str, u64); 8] = [
    ("t_switch", 0),
    ("t_pairs", 0x20),
    ("t_literal", 0x30),
    ("t_lane_move", 0x3c),
    ("t_sum_doubles", 0x48),
    ("a_divmod", 0x68),
    ("__aeabi_idivmod", 0x78),
    ("a_clamp", 0x88),
];

/// The routines, at [`BASE`], each named in its first instruction's
/// comment; A32 words are two halfwords, the low first.
const ROUTINES: [u16; 72] = [
    // ASM: cmp r0, #0x3 (t_switch)
    0x2803, // ASM: bhi 0x4001c
    0xd80b, // ASM: tbb [pc, r0]
    0xe8df, 0xf000, // ASM: .byte 2, 4, 6, 8
    0x0402, 0x0806, // ASM: movs r0, #0x7
    0x2007, // ASM: bx lr
    0x4770, // ASM: movs r0, #0x9
    0x2009, // ASM: bx lr
    0x4770, // ASM: movs r0, #0xb
    0x200b, // ASM: bx lr
    0x4770, // ASM: adds r0, r1, #0x1
    0x1c48, // ASM: bx lr
    0x4770, // ASM: movs r0, #0x0
    0x2000, // ASM: bx lr
    0x4770, // ASM: subs.w r4, r0, r2 (t_pairs)
    0xebb0, 0x0402, // ASM: sbcs.w r4, r1, r3
    0xeb71, 0x0403, // ASM: ite lt
    0xbfb4, // ASM: movlt r0, #0x1
    0x2001, // ASM: movge r0, #0x0
    0x2000, // ASM: bx lr
    0x4770, // ASM: ldr r1, [pc, #0x4] (t_literal)
    0x4901, // ASM: adds r0, r0, r1
    0x1840, // ASM: bx lr
    0x4770, // ASM: nop
    0xbf00, // ASM: .byte 120, 86, 52, 18
    0x5678, 0x1234, // ASM: mov r2, r0 (t_lane_move)
    0x4602, // ASM: vmov.32 r2, d16[1]
    0xee30, 0x2b90, // ASM: adds r0, r2, r1
    0x1850, // ASM: bx lr
    0x4770, // ASM: nop
    0xbf00, // ASM: vldr d0, [pc, #20] (t_sum_doubles)
    0xed9f, 0x0b05, // ASM: cmp r1, #0x1
    0x2901, // ASM: it lt
    0xbfb8, // ASM: bxlt lr
    0x4770, // ASM: vldmia r0!, {d1}
    0xecb0, 0x1b02, // ASM: subs r1, #0x1
    0x3901, // ASM: vadd.f64 d0, d0, d1
    0xee30, 0x0b01, // ASM: bne 0x40052
    0xd1f9, // ASM: bx lr
    0x4770, // ASM: .zero 8
    0x0000, 0x0000, 0x0000, 0x0000, // ASM: push {r11, lr} (a_divmod)
    0x4800, 0xe92d, // ASM: bl 0x40078
    0x0001, 0xeb00, // ASM: add r0, r0, r1
    0x0001, 0xe080, // ASM: pop {r11, pc}
    0x8800, 0xe8bd, // ASM: sdiv r2, r0, r1 (__aeabi_idivmod)
    0xf110, 0xe712, // ASM: mls r1, r2, r1, r0
    0x0192, 0xe061, // ASM: mov r0, r2
    0x0002, 0xe1a0, // ASM: bx lr
    0xff1e, 0xe12f, // ASM: usat r0, #0x8, r0 (a_clamp)
    0x0010, 0xe6e8, // ASM: bx lr
    0xff1e, 0xe12f,
];

/// [`ROUTINES`] as a raw ARM32 image, every routine named and its
/// instruction set marked.
fn image() -> Program {
    let code: Vec<u8> = ROUTINES.iter().flat_map(|h| h.to_le_bytes()).collect();
    let len = u64::try_from(code.len()).expect("a small image");
    let text = Section::mapped(".text", BASE, 0, len, false, true);
    let mut p = Program::raw(code, Arch::Arm, 0, Some(BASE), vec![text]);
    p.symbols = NAMES
        .iter()
        .map(|&(name, off)| Symbol {
            name: name.to_owned(),
            addr: BASE + off,
            kind: SymbolKind::Local,
        })
        .collect();
    p.modes = Modes::from_marks(vec![(BASE, Mode::Thumb), (ARM_FROM, Mode::Arm)]);
    p
}

/// The decompiled text of the routine `name`.
///
/// # Arguments
///
/// * `p` - The image.
/// * `a` - Its analysis.
/// * `name` - The routine.
fn text(p: &Program, a: &Analysis, name: &str) -> String {
    let off = NAMES
        .iter()
        .find(|(n, _)| *n == name)
        .map(|(_, off)| *off)
        .expect("a routine of the table");
    decompile(p, a, &Overlay::default(), BASE + off).expect("decompiles")
}

/// ARM32 code decompiles under the ARM32 procedure call standard.
///
/// A `tbb` dispatch is a switch over its guarded index; a compare of two
/// pairs through `subs` and `sbcs` is the 64-bit order; a literal pool's
/// word is a constant; a register a lane move writes holds nothing it held
/// before; a function that sums doubles hands back a double; the remainder
/// a division helper hands back in `r1` is the operator; a saturation is
/// its clamp.
#[test]
fn arm32_functions_decompile_with_their_arguments_and_results() {
    let p = image();
    assert!(p.refuses(Feature::Decompile).is_none());
    let a = Analysis::compute(&p);
    let switch = text(&p, &a, "t_switch");
    assert!(switch.contains("switch (a1) {"), "{switch}");
    assert!(switch.contains("return a2 + 1;"), "{switch}");
    assert!(switch.contains("return 0;"), "{switch}");
    let pairs = text(&p, &a, "t_pairs");
    assert!(
        pairs.contains("(int32_t)a2 < (int32_t)a4 || (a2 == a4 && a1 < a3)"),
        "{pairs}"
    );
    let literal = text(&p, &a, "t_literal");
    assert!(literal.contains("return a1 + 0x12345678;"), "{literal}");
    let lane = text(&p, &a, "t_lane_move");
    assert!(lane.contains("/* asm"), "{lane}");
    assert!(!lane.contains("a1 + a2"), "{lane}");
    let sum = text(&p, &a, "t_sum_doubles");
    assert!(
        sum.contains("// signature: double t_sum_doubles(uint32_t a1, uint32_t a2)"),
        "{sum}"
    );
    assert!(sum.contains("double d0;"), "{sum}");
    let divmod = text(&p, &a, "a_divmod");
    assert!(
        divmod.contains("// signature: uint32_t a_divmod(uint32_t a1, uint32_t a2)"),
        "{divmod}"
    );
    assert!(
        divmod.contains("((int32_t)(a1) / (int32_t)(a2))"),
        "{divmod}"
    );
    assert!(divmod.contains("(int32_t)a1 % (int32_t)a2"), "{divmod}");
    let clamp = text(&p, &a, "a_clamp");
    assert!(
        clamp.contains("((int32_t)a1 < 0 ? 0 : ((int32_t)a1 > 255 ? 255 : a1))"),
        "{clamp}"
    );
}

/// The text of every routine agrees with the ARM32 machine on every state
/// the check tries, and the check compares blocks of each it can run.
#[test]
fn arm32_text_agrees_with_the_machine() {
    let p = image();
    let a = Analysis::compute(&p);
    for (name, off) in NAMES {
        let r = replay_function(&p, &a, BASE + off, 1);
        assert!(r.wrong().is_empty(), "{name}: {}", replay_tsv(&r));
        if name != "t_lane_move" {
            assert!(r.checked > 0, "{name}: {}", replay_tsv(&r));
        }
    }
}

/// Every block of every routine lifts as the machine runs it.
#[test]
fn arm32_blocks_agree_with_the_machine() {
    let p = image();
    let a = Analysis::compute(&p);
    let entries: Vec<u64> = NAMES.iter().map(|(_, off)| BASE + off).collect();
    for seed in 1..=8 {
        let v = verify(&p, &a, &entries, seed);
        assert!(v.checked > 0, "seed {seed}: {}", verify_tsv(&v));
        assert!(v.mismatches.is_empty(), "seed {seed}: {}", verify_tsv(&v));
    }
}

/// A long run of flag-setting logical instructions decompiles promptly.
///
/// Each `movs` or `ands` keeps the carry and overflow the flags held
/// before it, so a run of 120 of them would nest every earlier state twice
/// over and the lift would never finish. The image is a `cmp r0, r1` that
/// gives the flags a value, the run, `movs r0, r1` then `ands r2, r0`
/// sixty times, and a jump through `r0`, which
/// leaves the flags to code the walk cannot see.
#[test]
fn a_run_of_flag_setting_moves_lifts_in_bounded_time() {
    let mut code: Vec<u16> = vec![0x4288];
    code.extend([0x0008, 0x4002].repeat(60));
    code.push(0x4700);
    let bytes: Vec<u8> = code.iter().flat_map(|h| h.to_le_bytes()).collect();
    let len = u64::try_from(bytes.len()).expect("a small image");
    let text = Section::mapped(".text", BASE, 0, len, false, true);
    let mut p = Program::raw(bytes, Arch::Arm, 0, Some(BASE), vec![text]);
    p.modes = Modes::from_marks(vec![(BASE, Mode::Thumb)]);
    let a = Analysis::compute(&p);
    let out = decompile(&p, &a, &Overlay::default(), BASE).expect("decompiles");
    assert!(out.contains("sub_40000"), "{out}");
}

/// A loop that walks a stack buffer through a pointer takes no stack
/// parameter.
///
/// The pointer starts at the buffer, 16 bytes below the entry stack
/// pointer, and steps 4 bytes a turn. Followed turn by turn, it reaches the
/// entry stack pointer and above, where incoming stack arguments live, but
/// what it reads there is the walk's own drift, not an argument any caller
/// passes. A32, hand-assembled.
#[test]
fn a_pointer_walking_a_stack_buffer_is_no_stack_parameter() {
    let words: [u32; 10] = [
        0xe24d_d010, // ASM: sub sp, sp, #16
        0xe1a0_300d, // ASM: mov r3, sp
        0xe3a0_2000, // ASM: mov r2, #0
        0xe493_1004, // ASM: ldr r1, [r3], #4
        0xe082_2001, // ASM: add r2, r2, r1
        0xe250_0001, // ASM: subs r0, r0, #1
        0x1aff_fffb, // ASM: bne 0x4000c
        0xe1a0_0002, // ASM: mov r0, r2
        0xe28d_d010, // ASM: add sp, sp, #16
        0xe12f_ff1e, // ASM: bx lr
    ];
    let bytes: Vec<u8> = words.iter().flat_map(|w| w.to_le_bytes()).collect();
    let len = u64::try_from(bytes.len()).expect("a small image");
    let text = Section::mapped(".text", BASE, 0, len, false, true);
    let mut p = Program::raw(bytes, Arch::Arm, 0, Some(BASE), vec![text]);
    p.modes = Modes::from_marks(vec![(BASE, Mode::Arm)]);
    let a = Analysis::compute(&p);
    let out = decompile(&p, &a, &Overlay::default(), BASE).expect("decompiles");
    let sig = out
        .lines()
        .find(|l| l.starts_with("// signature:"))
        .expect("a signature line");
    assert!(!sig.contains("arg_") && !sig.contains("a4"), "{out}");
}

/// A stack word one path writes and the other only reads is still an
/// incoming argument: the join keeps the stack pointer. A32, hand-assembled.
#[test]
fn a_stack_word_read_on_one_path_of_a_join_is_an_argument() {
    let words: [u32; 5] = [
        0xe350_0000, // ASM: cmp r0, #0
        0x0a00_0000, // ASM: beq 0x4000c
        0xe58d_1000, // ASM: str r1, [sp]
        0xe59d_0000, // ASM: ldr r0, [sp]
        0xe12f_ff1e, // ASM: bx lr
    ];
    let bytes: Vec<u8> = words.iter().flat_map(|w| w.to_le_bytes()).collect();
    let len = u64::try_from(bytes.len()).expect("a small image");
    let text = Section::mapped(".text", BASE, 0, len, false, true);
    let mut p = Program::raw(bytes, Arch::Arm, 0, Some(BASE), vec![text]);
    p.modes = Modes::from_marks(vec![(BASE, Mode::Arm)]);
    let a = Analysis::compute(&p);
    let out = decompile(&p, &a, &Overlay::default(), BASE).expect("decompiles");
    let sig = out
        .lines()
        .find(|l| l.starts_with("// signature:"))
        .expect("a signature line");
    assert!(sig.contains("a5"), "{out}");
}

/// A division helper's call is a step the text may write as its operator.
///
/// `a_divmod` calls `__aeabi_idivmod`, which the text writes as `/`. The
/// structure check took the call for one the text must write, so every
/// function that divides through the helper disagreed with its own text
/// (37 of u-boot's 2015 functions).
#[test]
fn the_structure_check_reads_a_division_helper_as_its_operator() {
    use borer_engine::analysis::decompile::traces::{Structure, check_structure};
    let p = image();
    let a = Analysis::compute(&p);
    let out = text(&p, &a, "a_divmod");
    assert!(!out.contains("__aeabi_idivmod("), "{out}");
    let o = Overlay::default();
    assert_eq!(
        check_structure(&p, &a, &o, BASE + 0x68, &out),
        Structure::Agrees,
        "{out}"
    );
}
