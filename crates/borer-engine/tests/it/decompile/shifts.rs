//! A32 and T32 shifts by a register: one helper call each, never a `?:`.

use super::thumb::{AT, agreed_in};
use crate::a32_emulate::{Code, image};
use borer_engine::emulate::Stop;
use borer_engine::emulate::a32::Machine;

/// The amounts every shift is checked at: the edges of the 32-bit range
/// and of the low byte the Arm ARM reads the amount from.
const AMOUNTS: [u64; 7] = [0, 1, 31, 32, 33, 255, 256];

/// The words every shift is checked on: a negative one and a positive one,
/// neither a value the text's constant tables name.
const WORDS: [u64; 2] = [0x9234_5679, 0x7234_5678];

/// `lsl r0, r1, r2`, in A32.
const A_LSL: &[u32] = &[
    // ASM: lsl r0, r1, r2
    0xe1a0_0211,
    // ASM: bx lr
    0xe12f_ff1e,
];

/// `lsr r0, r1, r2`, in A32.
const A_LSR: &[u32] = &[
    // ASM: lsr r0, r1, r2
    0xe1a0_0231,
    // ASM: bx lr
    0xe12f_ff1e,
];

/// `asr r0, r1, r2`, in A32.
const A_ASR: &[u32] = &[
    // ASM: asr r0, r1, r2
    0xe1a0_0251,
    // ASM: bx lr
    0xe12f_ff1e,
];

/// `lsl.w r0, r1, r2`, in T32.
const T_LSL: &[u16] = &[
    0xfa01, 0xf002, // ASM: lsl.w r0, r1, r2
    0x4770, // ASM: bx lr
];

/// `lsr.w r0, r1, r2`, in T32.
const T_LSR: &[u16] = &[
    0xfa21, 0xf002, // ASM: lsr.w r0, r1, r2
    0x4770, // ASM: bx lr
];

/// `asr.w r0, r1, r2`, in T32.
const T_ASR: &[u16] = &[
    0xfa41, 0xf002, // ASM: asr.w r0, r1, r2
    0x4770, // ASM: bx lr
];

/// Every routine with the helper its text calls.
const SHIFTS: [(Code<'static>, &str); 6] = [
    (Code::Arm(A_LSL), "lsl32"),
    (Code::Arm(A_LSR), "lsr32"),
    (Code::Arm(A_ASR), "asr32"),
    (Code::Thumb(T_LSL), "lsl32"),
    (Code::Thumb(T_LSR), "lsr32"),
    (Code::Thumb(T_ASR), "asr32"),
];

/// Returns an A32 routine that loads `x` into `r1` and `n` into `r2`,
/// shifts, and returns.
///
/// It is `movw r1, #lo; movt r1, #hi; mov r2, #n; <shift>; bx lr`, each
/// word encoded as the Arm ARM lays it out and checked against LLVM's
/// (`movw r1, #0x1` is `0xe3001001`, `movt r1, #0x8000` is `0xe3481000`,
/// `mov r2, #256` is `0xe3a02c01`).
///
/// # Arguments
///
/// * `x` - The word, 32 bits.
/// * `n` - The amount, at most 255 or exactly 256.
/// * `shift` - The shift's word, reading `r1` and `r2` into `r0`.
fn loaded(x: u64, n: u64, shift: u32) -> [u32; 5] {
    let half = |v: u64| u32::try_from(v & 0xffff).unwrap_or(0);
    let wide = |base: u32, v: u32| base | ((v >> 12) << 16) | (v & 0xfff);
    let amount = if n == 256 { 0xc01 } else { half(n) & 0xff };
    [
        wide(0xe300_1000, half(x)),
        wide(0xe340_1000, half(x >> 16)),
        0xe3a0_2000 | amount,
        shift,
        // ASM: bx lr
        0xe12f_ff1e,
    ]
}

/// The lines of a text past the helper definitions at its top.
///
/// # Arguments
///
/// * `text` - The text.
fn body(text: &str) -> String {
    text.lines()
        .filter(|l| !l.starts_with("static inline "))
        .collect::<Vec<_>>()
        .join("\n")
}

/// What the machine leaves in `r0` after a routine run on `r1` and `r2`.
///
/// # Arguments
///
/// * `code` - The routine.
/// * `x` - The word in `r1`.
/// * `n` - The amount register `r2`.
///
/// # Returns
///
/// The word, or `None` when the routine does not run to its return.
fn machine_r0(code: Code<'_>, x: u64, n: u64) -> Option<u64> {
    let p = image(AT, code);
    let mut m = Machine::new(&p, 64)?;
    if !(m.set_register("r1", x) && m.set_register("r2", n)) {
        return None;
    }
    (m.run(AT).stop == Stop::Returned).then(|| m.register("r0"))?
}

/// The value a text returns, read from its last `return`.
///
/// # Arguments
///
/// * `text` - The text.
///
/// # Returns
///
/// The value as a 32-bit word, a multi-character literal read as C reads
/// it, or `None` when the text returns no constant.
fn returned(text: &str) -> Option<u64> {
    let line = text
        .lines()
        .rev()
        .find_map(|l| l.trim().strip_prefix("return "))?;
    let v = line.strip_suffix(';')?;
    if let Some(chars) = v.strip_prefix('\'').and_then(|c| c.strip_suffix('\'')) {
        return Some(chars.bytes().fold(0, |acc, b| (acc << 8) | u64::from(b)) & 0xffff_ffff);
    }
    let (neg, digits) = v.strip_prefix('-').map_or((false, v), |d| (true, d));
    let n = match digits.strip_prefix("0x") {
        Some(hex) => u64::from_str_radix(hex, 16).ok()?,
        None => digits.parse().ok()?,
    };
    Some(if neg { n.wrapping_neg() } else { n } & 0xffff_ffff)
}

/// `lsl`, `lsr` and `asr` by a register print as one helper call on the
/// two registers, with no `?:`, and the lift and the statements agree with
/// the emulator, in A32 and in T32.
#[test]
fn a_shift_by_a_register_agrees_with_the_emulator_as_one_helper_call() {
    for (code, helper) in SHIFTS {
        let text = agreed_in(code);
        assert!(text.contains(&format!("{helper}(a2, a3)")), "{text}");
        assert!(!body(&text).contains('?'), "{text}");
    }
}

/// Every A32 shift by a register, with its word and amount loaded as
/// constants, folds to the constant the emulator leaves, at the amounts on
/// either side of 32 and of the low byte.
///
/// The lift decides each select, so no helper reaches these texts; the
/// helper's own value is held to the machine in `reg_shift`'s unit tests.
#[test]
fn a_shift_by_constants_folds_to_what_the_emulator_leaves_at_every_edge_amount() {
    for (shift, helper) in [
        (A_LSL[0], "lsl32"),
        (A_LSR[0], "lsr32"),
        (A_ASR[0], "asr32"),
    ] {
        for x in WORDS {
            for n in AMOUNTS {
                let code = loaded(x, n, shift);
                let want = machine_r0(Code::Arm(&code), 0, 0);
                assert!(want.is_some(), "{helper} {x:#x} by {n}: no run");
                let text = agreed_in(Code::Arm(&code));
                assert_eq!(returned(&text), want, "{helper} {x:#x} by {n}: {text}");
            }
        }
    }
}

/// The prefixes that leave `r2` one of two amounts, chosen by the sign of
/// the incoming `r3`.
///
/// Each pair has one amount below 32 or 256 and one at or above, so every seed of the check that draws `r3` negative and every
/// one that draws it positive runs a different side of the helper.
const PAIRS: [(&[u32], &str); 4] = [
    (
        &[
            // ASM: lsr r2, r3, #31
            0xe1a0_2fa3,
            // ASM: lsl r2, r2, #5
            0xe1a0_2282,
        ],
        "0 or 32",
    ),
    (
        &[
            // ASM: lsr r2, r3, #31
            0xe1a0_2fa3,
            // ASM: lsl r2, r2, #5
            0xe1a0_2282,
            // ASM: orr r2, r2, #1
            0xe382_2001,
        ],
        "1 or 33",
    ),
    (
        &[
            // ASM: lsr r2, r3, #31
            0xe1a0_2fa3,
            // ASM: lsl r2, r2, #5
            0xe1a0_2282,
            // ASM: orr r2, r2, #31
            0xe382_201f,
        ],
        "31 or 63",
    ),
    (
        &[
            // ASM: lsr r2, r3, #31
            0xe1a0_2fa3,
            // ASM: add r2, r2, #255
            0xe282_20ff,
        ],
        "255 or 256",
    ),
];

/// A shift by one of two amounts across 32 agrees with the emulator as its
/// helper.
///
/// The amount comes from a register at entry the lift cannot fold and lies
/// on either side of 32 or of the low byte; the text prints the helper, and
/// the lift and the statements agree with the emulator.
///
/// The check seeds `r3` from values with the sign set and clear (zero, one,
/// the signed and unsigned limits), so it runs both amounts of each pair.
#[test]
fn a_shift_by_one_of_two_amounts_across_32_agrees_with_the_emulator_as_its_helper() {
    for (shift, helper) in [
        (A_LSL[0], "lsl32"),
        (A_LSR[0], "lsr32"),
        (A_ASR[0], "asr32"),
    ] {
        for (prefix, amounts) in PAIRS {
            let mut code = prefix.to_vec();
            // ASM: bx lr
            code.extend([shift, 0xe12f_ff1e]);
            let text = agreed_in(Code::Arm(&code));
            assert!(
                text.contains(&format!("return {helper}(a2, ")),
                "{amounts}: {text}"
            );
            assert!(!body(&text).contains('?'), "{amounts}: {text}");
        }
    }
}

/// A shift by an amount masked below 32 is C's own `<<`, and one masked
/// to six bits, which may reach 32, keeps the helper.
#[test]
fn a_shift_by_a_register_masked_below_32_agrees_with_the_emulator_as_a_plain_shift() {
    let masked = agreed_in(Code::Arm(&[
        // ASM: and r2, r2, #31
        0xe202_201f,
        // ASM: lsl r0, r1, r2
        0xe1a0_0211,
        // ASM: bx lr
        0xe12f_ff1e,
    ]));
    assert!(masked.contains("a2 << (a3 & 0x1f)"), "{masked}");
    assert!(
        !masked.contains("lsl32") && !masked.contains('?'),
        "{masked}"
    );
    let six = agreed_in(Code::Arm(&[
        // ASM: and r2, r2, #63
        0xe202_203f,
        // ASM: lsl r0, r1, r2
        0xe1a0_0211,
        // ASM: bx lr
        0xe12f_ff1e,
    ]));
    assert!(six.contains("lsl32(a2, a3 & 0x3f)"), "{six}");
    assert!(!body(&six).contains('?'), "{six}");
}
