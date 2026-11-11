//! The arm64 emulator.
//!
//! Words assembled by LLVM (`clang --target=aarch64-linux-gnu`, linked by
//! `ld.lld` where an address matters) and checked against
//! `llvm-objdump` — the scalar float and vector ones hand-encoded from the
//! Arm ARM and checked against the decoder —
//! run in [`Machine`] from a raw arm64 image: a table of short routines
//! with the registers set before and the registers, memory and vector
//! registers expected after; the flag truth tables of the adds, subtracts
//! and conditional compares; every way a run stops; an XOR decryption loop
//! end to end, alone and through the `emulate` and `run` surfaces; and
//! random words, which run to a stop without a panic.
#![expect(
    clippy::missing_panics_doc,
    clippy::expect_used,
    reason = "assertions are the point of a test"
)]

use borer_engine::analysis::{Analysis, Overlay, render};
use borer_engine::emulate::a64::Machine;
use borer_engine::emulate::{Stop, fill_byte};
use borer_engine::program::{Arch, Program, Section};

mod cases;

use cases::CASES;

/// Where every routine is placed and run from.
const BASE: u64 = 0x1_0000;

/// Where [`DATA`] is planted before each routine runs.
const DATA_AT: u64 = 0x3_0000;

/// The bytes the loads read: a doubleword, a doubleword whose bytes have
/// their top bits set, and eight rising bytes; zeros follow.
const DATA: [u8; 24] = [
    0x88, 0x77, 0x66, 0x55, 0x44, 0x33, 0x22, 0x11, 0x80, 0xff, 0x01, 0x80, 0xfe, 0xff, 0xff, 0xff,
    0x10, 0x20, 0x30, 0x40, 0x50, 0x60, 0x70, 0x80,
];

/// Bytes planted at [`DATA_AT`]: [`DATA`], then zeros a store can be read
/// back from.
const PLANTED: usize = 64;

/// [`DATA`]'s first sixteen bytes as one `v` register.
const QWORDS: u128 = 0xffff_fffe_8001_ff80_1122_3344_5566_7788;

/// [`DATA`]'s eight rising bytes, then zeros, as one `v` register.
const RISING: u128 = 0x8070_6050_4030_2010;

/// A lane's value replicated `times` times through a `v` register, as
/// `dup` leaves it.
///
/// # Arguments
///
/// * `v` - One lane's value.
/// * `times` - How many lanes the arrangement holds.
const fn rep(v: u64, times: u8) -> u128 {
    let each = 128 / (times as u64);
    let mut acc = v as u128;
    let mut k = 1;
    while k < times as u64 {
        acc |= (v as u128) << (k * each);
        k += 1;
    }
    acc
}

/// The stack pointer a run starts with.
const SP: u64 = 0x7fff_0000_0000;

/// What the link register holds when a run starts.
const RETURN_TO: u64 = 0x7fff_ffff_f000;

/// The return every short routine ends with.
// ASM: ret
const RET: u32 = 0xd65f_03c0;

/// A raw arm64 image whose only section, at [`BASE`], holds `words`.
///
/// # Arguments
///
/// * `words` - The code, in order.
fn image(words: &[u32]) -> Program {
    let code: Vec<u8> = words.iter().flat_map(|w| w.to_le_bytes()).collect();
    let len = u64::try_from(code.len()).expect("a small image");
    let text = Section::mapped(".text", BASE, 0, len, false, true);
    Program::raw(code, Arch::Arm64, 0, Some(BASE), vec![text])
}

/// A machine over `p` with [`DATA`] planted.
///
/// # Arguments
///
/// * `p` - The image.
fn machine(p: &Program) -> Machine<'_> {
    let mut m = Machine::new(p, 10_000).expect("an arm64 machine");
    for (at, k) in (DATA_AT..).zip(0..PLANTED) {
        m.poke(at, DATA.get(k).copied().unwrap_or(0));
    }
    m
}

/// One routine of the table: its words, the registers set before it runs,
/// and what it leaves.
struct Case {
    /// The routine's name, for a failure message.
    name: &'static str,
    /// The routine, run from [`BASE`]; it returns.
    words: &'static [u32],
    /// Registers set before the run, by name.
    set: &'static [(&'static str, u64)],
    /// Registers expected after it, by name.
    want: &'static [(&'static str, u64)],
    /// Bytes expected in memory after it, by address.
    mem: &'static [(u64, &'static [u8])],
    /// `v` registers expected after it, by number.
    vregs: &'static [(usize, u128)],
}

/// Every routine of the table returns and leaves the registers, memory and
/// vector registers the architecture says it does.
#[test]
fn routines_compute_what_the_architecture_says() {
    for c in CASES {
        let p = image(c.words);
        let mut m = machine(&p);
        for &(name, v) in c.set {
            assert!(m.set_register(name, v), "{}: {name} sets nothing", c.name);
        }
        let run = m.run(BASE);
        assert_eq!(run.stop, Stop::Returned, "{}: {run:?}", c.name);
        for &(name, v) in c.want {
            assert_eq!(m.register(name), Some(v), "{}: {name}", c.name);
        }
        for &(at, bytes) in c.mem {
            let got: Vec<Option<u8>> = (at..).take(bytes.len()).map(|a| m.byte_at(a)).collect();
            let want: Vec<Option<u8>> = bytes.iter().copied().map(Some).collect();
            assert_eq!(got, want, "{}: memory at {at:#x}", c.name);
        }
        for &(n, v) in c.vregs {
            assert_eq!(m.vregs().get(n).copied(), Some(v), "{}: v{n}", c.name);
        }
    }
}

/// `fcvtzu` of a value in `[2^63, 2^64)` keeps that value.
///
/// The float is planted with `fmov`, because a vector register has no
/// name `set_register` accepts. Casting the truncated value through a
/// signed 64-bit integer saturates at the signed maximum; the architecture
/// does not. Each row is the conversion, the float's bits and `x0`
/// after; the 32-bit row moves `w0` into `s0`.
#[test]
fn an_unsigned_conversion_of_two_to_the_63_keeps_the_high_bit() {
    let rows: &[(u32, u32, u64, u64)] = &[
        // ASM: fcvtzu x0, d0
        (
            0x9e67_0000,
            0x9e79_0000,
            0x43E0_0000_0000_0000,
            0x8000_0000_0000_0000,
        ),
        (
            0x9e67_0000,
            0x9e79_0000,
            0x43EF_FFFF_FFFF_FFFF,
            0xffff_ffff_ffff_f800,
        ),
        (0x9e67_0000, 0x9e79_0000, 0x43F0_0000_0000_0000, u64::MAX),
        (0x9e67_0000, 0x9e79_0000, 0x7FF0_0000_0000_0000, u64::MAX),
        (0x9e67_0000, 0x9e79_0000, 0xBFF0_0000_0000_0000, 0),
        // ASM: fcvtzs x0, d0
        (
            0x9e67_0000,
            0x9e78_0000,
            0x43E0_0000_0000_0000,
            0x7fff_ffff_ffff_ffff,
        ),
        (
            0x9e67_0000,
            0x9e78_0000,
            0xC3E0_0000_0000_0000,
            0x8000_0000_0000_0000,
        ),
        // ASM: fmov s0, w0 / fcvtzu w0, s0. 2^31 fits; 2^32 saturates.
        (0x1e27_0000, 0x1e39_0000, 0x4f00_0000, 0x8000_0000),
        (0x1e27_0000, 0x1e39_0000, 0x4f80_0000, 0xffff_ffff),
    ];
    for &(mov, op, bits, want) in rows {
        let p = image(&[mov, op, RET]);
        let mut m = machine(&p);
        assert!(m.set_register("x0", bits), "{bits:#x} sets nothing");
        assert_eq!(m.run(BASE).stop, Stop::Returned, "{bits:#x}");
        assert_eq!(m.register("x0"), Some(want), "{op:#x} of {bits:#x}");
    }
}

/// A float compare with a NaN leaves `NZCV` at `0011`: unordered is not
/// equal, and C and V are set.
#[test]
fn an_unordered_float_compare_sets_only_carry_and_overflow() {
    let rows: &[(u64, u64, u64)] = &[
        (0x7ff8_0000_0000_0000, 0x3ff0_0000_0000_0000, C | V),
        (0x3ff0_0000_0000_0000, 0x7ff8_0000_0000_0000, C | V),
        (0x3ff0_0000_0000_0000, 0x3ff0_0000_0000_0000, Z | C),
        (0x0000_0000_0000_0000, 0x3ff0_0000_0000_0000, N),
        (0x4000_0000_0000_0000, 0x3ff0_0000_0000_0000, C),
    ];
    // ASM: fmov d0, x0 / fmov d1, x1 / fcmp d0, d1 / mrs x0, NZCV / ret
    let p = image(&[0x9e67_0000, 0x9e67_0021, 0x1e61_2000, 0xd53b_4200, RET]);
    for &(a, b, want) in rows {
        let mut m = machine(&p);
        assert!(m.set_register("x0", a), "{a:#x} sets nothing");
        assert!(m.set_register("x1", b), "{b:#x} sets nothing");
        assert_eq!(m.run(BASE).stop, Stop::Returned, "{a:#x} {b:#x}");
        assert_eq!(m.register("x0"), Some(want), "{a:#x} vs {b:#x}");
    }
}

/// `adds w0, w1, w2`.
// ASM: adds w0, w1, w2
const ADDS_W: u32 = 0x2b02_0020;

/// `adds x0, x1, x2`.
// ASM: adds x0, x1, x2
const ADDS_X: u32 = 0xab02_0020;

/// `subs w0, w1, w2`.
// ASM: subs w0, w1, w2
const SUBS_W: u32 = 0x6b02_0020;

/// `subs x0, x1, x2`.
// ASM: subs x0, x1, x2
const SUBS_X: u32 = 0xeb02_0020;

/// `adcs w0, w1, w2`.
// ASM: adcs w0, w1, w2
const ADCS_W: u32 = 0x3a02_0020;

/// `sbcs w0, w1, w2`.
// ASM: sbcs w0, w1, w2
const SBCS_W: u32 = 0x7a02_0020;

/// `ccmp x1, x2, #0x4, ne`: the compare's flags when Z is clear, else Z.
// ASM: ccmp x1, x2, #0x4, ne
const CCMP: u32 = 0xfa42_1024;

/// `ccmn w1, #0x3, #0x9, hs`: the add's flags when C is set, else N and V.
// ASM: ccmn w1, #0x3, #0x9, hs
const CCMN: u32 = 0x3a43_2829;

/// One flag case: the word, `x1`, `x2`, the flags before, `x0` after (or
/// `None` when the instruction writes no register) and the flags after.
type FlagRow = (u32, u64, u64, u64, Option<u64>, u64);

/// The negative flag, as `NZCV` holds it.
const N: u64 = 1 << 31;

/// The zero flag.
const Z: u64 = 1 << 30;

/// The carry flag.
const C: u64 = 1 << 29;

/// The overflow flag.
const V: u64 = 1 << 28;

/// The adds and subtracts set exactly the flags of `AddWithCarry`.
///
/// An add's carry is its carry out, a subtract's carry is not-borrow,
/// overflow is signed, and the carry in feeds `adcs` and `sbcs`; a
/// conditional compare takes the compare's flags when its condition holds
/// and its immediate flags when it does not.
#[test]
fn flags_follow_add_with_carry() {
    const M32: u64 = 0xffff_ffff;
    const M64: u64 = u64::MAX;
    const MIN64: u64 = 1 << 63;
    let rows: &[FlagRow] = &[
        (ADDS_W, 1, 2, 0, Some(3), 0),
        (ADDS_W, 0x7fff_ffff, 1, 0, Some(0x8000_0000), N | V),
        (ADDS_W, M32, 1, 0, Some(0), Z | C),
        (ADDS_W, 0x8000_0000, 0x8000_0000, 0, Some(0), Z | C | V),
        (ADDS_W, M32, M32, 0, Some(0xffff_fffe), N | C),
        (ADDS_X, MIN64 - 1, 1, 0, Some(MIN64), N | V),
        (ADDS_X, M64, 1, 0, Some(0), Z | C),
        (ADDS_X, MIN64, M64, 0, Some(MIN64 - 1), C | V),
        (SUBS_W, 5, 3, 0, Some(2), C),
        (SUBS_W, 3, 5, 0, Some(0xffff_fffe), N),
        (SUBS_W, 5, 5, 0, Some(0), Z | C),
        (SUBS_W, 0x8000_0000, 1, 0, Some(0x7fff_ffff), C | V),
        (SUBS_W, 0x7fff_ffff, M32, 0, Some(0x8000_0000), N | V),
        (SUBS_W, 0, 0, N | V, Some(0), Z | C),
        (SUBS_X, 0, 1, 0, Some(M64), N),
        (SUBS_X, MIN64, 1, 0, Some(MIN64 - 1), C | V),
        (ADCS_W, M32, 0, C, Some(0), Z | C),
        (ADCS_W, 1, 1, 0, Some(2), 0),
        (ADCS_W, 0x7fff_ffff, 0, C, Some(0x8000_0000), N | V),
        (SBCS_W, 5, 3, C, Some(2), C),
        (SBCS_W, 5, 3, 0, Some(1), C),
        (SBCS_W, 3, 3, 0, Some(M32), N),
        (SBCS_W, 0, 0, C, Some(0), Z | C),
        (CCMP, 5, 5, 0, None, Z | C),
        (CCMP, 3, 5, 0, None, N),
        (CCMP, 3, 5, Z, None, Z),
        (CCMN, 0xffff_fffd, 0, C, None, Z | C),
        (CCMN, 0x7fff_fffd, 0, C, None, N | V),
        (CCMN, 0xffff_fffd, 0, 0, None, N | V),
    ];
    for &(word, x1, x2, flags, x0, want) in rows {
        let p = image(&[word, RET]);
        let mut m = machine(&p);
        assert!(m.set_register("x0", 0x5a5a) && m.set_register("x1", x1));
        assert!(m.set_register("x2", x2) && m.set_register("nzcv", flags));
        let run = m.run(BASE);
        assert_eq!(run.stop, Stop::Returned, "{word:#010x}");
        let case = format!(
            "{word:#010x} on {x1:#x}, {x2:#x} with nzcv {:#x}",
            flags >> 28
        );
        assert_eq!(m.register("nzcv"), Some(want), "{case}");
        assert_eq!(m.register("x0"), Some(x0.unwrap_or(0x5a5a)), "{case}");
    }
}

/// Every way a run stops is named.
///
/// A run ends at the step budget, at a fault on a load or a fetch, on code
/// on the stack, on an instruction the machine does not model, at an exit
/// call, and at a requested stop.
#[test]
fn every_stop_is_named() {
    /// Steps the budget case is given.
    const BUDGET: usize = 100;
    /// A jump to itself.
    // ASM: b .
    const SPIN: u32 = 0x1400_0000;
    /// A load through `x1`.
    // ASM: ldr x0, [x1]
    const LOAD: u32 = 0xf940_0020;
    /// A jump through `x1`.
    // ASM: br x1
    const JUMP: u32 = 0xd61f_0020;
    /// The call number of `exit`.
    // ASM: mov x8, #93
    const EXIT: u32 = 0xd280_0ba8;
    /// The call number of `exit_group`.
    // ASM: mov x8, #94
    const EXIT_GROUP: u32 = 0xd280_0bc8;
    /// The call number of `write`.
    // ASM: mov x8, #64
    const WRITE: u32 = 0xd280_0808;
    /// A Linux system call.
    // ASM: svc #0
    const SVC: u32 = 0xd400_0001;
    let stop = |words: &[u32], set: &[(&str, u64)], budget: usize| {
        let p = image(words);
        let mut m = machine(&p);
        m.set_budget(budget);
        for &(name, v) in set {
            assert!(m.set_register(name, v), "{name}");
        }
        let run = m.run(BASE);
        (run.stop, run.steps, m.last_ip())
    };
    assert_eq!(stop(&[SPIN], &[], BUDGET), (Stop::Budget, BUDGET, BASE));
    assert_eq!(
        stop(&[LOAD, RET], &[("x1", 0x10)], BUDGET).0,
        Stop::Fault(0x10)
    );
    let far = 0x5000_0000;
    assert_eq!(
        stop(&[JUMP], &[("x1", far)], BUDGET),
        (Stop::Fault(far), 1, BASE)
    );
    assert_eq!(
        stop(&[JUMP], &[("x1", BASE + 2)], BUDGET).0,
        Stop::Fault(BASE + 2)
    );
    assert_eq!(
        stop(&[JUMP], &[("x1", SP - 0x100)], BUDGET).0,
        Stop::Derailed(SP - 0x100)
    );
    let cases: [(&[u32], &str); 5] = [
        // ASM: faddp v0.4s, v0.4s, v1.4s (the pairwise form; the plain one runs)
        (&[0x6e21_d400], "faddp"),
        // ASM: cmeq v0.16b, v0.16b, v1.16b (a lane compare; the lane selects run)
        (&[0x6e21_8c00], "cmeq"),
        // ASM: brk #0x3e8
        (&[0xd420_7d00], "brk"),
        // ASM: svc #0x80
        (&[0xd400_1001], "svc #0x80"),
        // ASM: movz w0, #0x1, lsl #32 (unallocated: a 32-bit form shifted by 32), hand-encoded
        (&[0x52c0_0020], "mov w0, #0x0"),
    ];
    for (words, text) in cases {
        match stop(words, &[], BUDGET).0 {
            Stop::Unmodeled(what) => assert!(what.contains(text), "{what} for {text}"),
            other => panic!("{text}: {other:?}"),
        }
    }
    assert_eq!(stop(&[EXIT, SVC], &[], BUDGET), (Stop::Exited, 2, BASE + 4));
    assert_eq!(stop(&[EXIT_GROUP, SVC], &[], BUDGET).0, Stop::Exited);
    {
        // ASM: b .-8
        const BACK: u32 = 0x17ff_fffe;
        let p = image(&[WRITE, SVC, BACK]);
        let mut m = machine(&p);
        m.set_budget(1_000_000);
        let run = m.run(BASE);
        assert_eq!(
            run.stop,
            Stop::Limit(borer_engine::emulate::Limit::Calls),
            "a syscall loop stops when its record is full"
        );
        assert_eq!(m.api_names().len(), borer_engine::emulate::RECORDS_MAX);
    }
    {
        let p = image(&[WRITE, SVC, RET]);
        let mut m = machine(&p);
        m.set_budget(BUDGET);
        assert!(m.set_register("x2", 7));
        let run = m.run(BASE);
        assert_eq!(run.stop, Stop::Returned, "{run:?}");
        assert_eq!(m.api_names(), ["write"]);
        assert_eq!(m.register("x0"), Some(7));
    }
    // ASM: an unallocated branch-register word
    match stop(&[0xd600_0000], &[], BUDGET).0 {
        Stop::Unmodeled(what) => assert_eq!(what, format!("bad opcode at {BASE:#x}")),
        other => panic!("bad opcode: {other:?}"),
    }
    let p = image(&[SPIN]);
    let mut m = machine(&p);
    m.stop_at(Some(BASE));
    assert_eq!(m.run(BASE).stop, Stop::Stopped(BASE));
}

/// An XOR decryption routine, linked at [`BASE`]: it finds its blob with
/// `adrp` and `add`, then decrypts it into the buffer `x0` points at under
/// a key that steps by seven, `x1` bytes long.
const XOR_DECRYPT: [u32; 17] = [
    // ASM: stp x29, x30, [sp, #-0x10]!
    0xa9bf_7bfd,
    // ASM: mov x29, sp
    0x9100_03fd,
    // ASM: adrp x9, 0x10000
    0x9000_0009,
    // ASM: add x9, x9, #0x34
    0x9100_d129,
    // ASM: mov w10, #0x5a
    0x5280_0b4a,
    // ASM: ldrb w11, [x9], #0x1
    0x3840_152b,
    // ASM: eor w11, w11, w10
    0x4a0a_016b,
    // ASM: strb w11, [x0], #0x1
    0x3800_140b,
    // ASM: add w10, w10, #0x7
    0x1100_1d4a,
    // ASM: subs x1, x1, #0x1
    0xf100_0421,
    // ASM: b.ne 0x10014
    0x54ff_ff61,
    // ASM: ldp x29, x30, [sp], #0x10
    0xa8c1_7bfd,
    // ASM: ret
    0xd65f_03c0,
    // ASM: .word 0x0a1a0e38 (the blob)
    0x0a1a_0e38,
    // ASM: .word 0xfef65d04
    0xfef6_5d04,
    // ASM: .word 0xc680eafc
    0xc680_eafc,
    // ASM: .word 0xf78ad8dc
    0xf78a_d8dc,
];

/// What [`XOR_DECRYPT`] writes.
const PLAINTEXT: &[u8; 16] = b"borer runs arm64";

/// Where the decrypted text goes.
const OUT_AT: u64 = 0x4_0000;

/// Steps [`XOR_DECRYPT`] takes over sixteen bytes: five to set up, six per
/// byte, two to return.
const XOR_STEPS: usize = 5 + 6 * 16 + 2;

/// The XOR loop decrypts its blob into the buffer and returns, writing its
/// frame record and the plaintext, with a trace of its last instructions.
#[test]
fn an_xor_loop_decrypts_its_blob() {
    let p = image(&XOR_DECRYPT);
    let mut m = Machine::new(&p, 10_000).expect("an arm64 machine");
    m.set_arg(0, OUT_AT);
    m.set_arg(1, 16);
    m.set_trace(3);
    let run = m.run(BASE);
    assert_eq!((run.stop, run.steps), (Stop::Returned, XOR_STEPS));
    let out: Vec<Option<u8>> = (OUT_AT..).take(16).map(|a| m.byte_at(a)).collect();
    let want: Vec<Option<u8>> = PLAINTEXT.iter().copied().map(Some).collect();
    assert_eq!(out, want);
    assert_eq!(run.written, 16 + 16, "the frame record and the text");
    assert_eq!(run.history.len(), 16 + 16);
    assert_eq!(
        (m.register("sp"), m.register("x30")),
        (Some(SP), Some(RETURN_TO))
    );
    let trace = m.trace();
    assert_eq!(trace.len(), 3, "{trace:?}");
    assert!(trace[0].starts_with("0x10028  b.ne 0x10014"), "{trace:?}");
    assert!(trace[1].contains("x29=0x0 sp=0x7fff00000000"), "{trace:?}");
    assert!(trace[2].ends_with("stopped: returned"), "{trace:?}");
}

/// A load through a pointer nothing backs faults, unless a fill is set:
/// then it reads the fill's hash of each address, while a jump there
/// still faults, since a fill answers loads and never fetches.
#[test]
fn a_fill_answers_a_load_nothing_backs() {
    /// An address no image, stack or planted byte takes.
    const NOWHERE: u64 = 0x5000_0000;
    /// The fill's seed.
    const SEED: u64 = 7;
    let load = image(&[
        // ASM: ldr x0, [x1]
        0xf940_0020,
        RET,
    ]);
    let mut m = machine(&load);
    assert!(m.set_register("x1", NOWHERE));
    assert_eq!(m.run(BASE).stop, Stop::Fault(NOWHERE));
    let mut m = machine(&load);
    m.set_fill(Some(SEED));
    assert!(m.set_register("x1", NOWHERE));
    assert_eq!(m.run(BASE).stop, Stop::Returned);
    let want = (0..8)
        .rev()
        .fold(0, |v, k| (v << 8) | u64::from(fill_byte(SEED, NOWHERE + k)));
    assert_eq!(m.register("x0"), Some(want));
    let jump = image(&[
        // ASM: br x1
        0xd61f_0020,
    ]);
    let mut m = machine(&jump);
    m.set_fill(Some(SEED));
    assert!(m.set_register("x1", NOWHERE));
    assert_eq!(m.run(BASE).stop, Stop::Fault(NOWHERE));
}

/// The experiment and typed-run surfaces run arm64 code.
///
/// `emulate` reports the stop, the registers and the text the routine
/// wrote, and `run` tabulates the call on its inputs, unchecked (the
/// decompile answer checks an arm64 text block by block instead); the
/// surfaces built on the x86 machine refuse it.
#[test]
fn emulate_and_run_answer_for_arm64() {
    let p = image(&XOR_DECRYPT);
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let out = render::emulate_tsv(&p, &a, &o, &format!("{BASE:#x},x0={OUT_AT:#x},a2=16"))
        .expect("an arm64 routine runs");
    assert!(
        out.starts_with(&format!(
            "# ran sub_10000 from 0x10000 with x0={OUT_AT:#x} a2=0x10: returned after {XOR_STEPS} steps, 32 bytes written\n# registers: x0={:#x} x1=0x0 ",
            OUT_AT + 16
        )),
        "{out}"
    );
    assert!(out.contains("\"borer runs arm64\""), "{out}");
    let traced = render::emulate_tsv(&p, &a, &o, "0x10000,x0=0x40000,x1=2,trace=2,dump=0x40000:2")
        .expect("a traced run");
    assert!(
        traced.contains("# trace: address, instruction, registers it changed\n0x1002c  ldp"),
        "{traced}"
    );
    assert!(traced.contains("# dump 0x40000..0x40002\n"), "{traced}");
    let refused = render::emulate_tsv(&p, &a, &o, "0x10000,rax=1").expect_err("an x86 name");
    assert!(refused.contains("use x0..x30"), "{refused}");
    let refused = render::emulate_tsv(&p, &a, &o, "0x10000,profile=4").expect_err("x86 only");
    assert!(refused.contains("x86 run only"), "{refused}");
    let table = render::run_tsv(&p, &a, &o, "0x10000/out:16,16").expect("a typed run");
    assert!(
        table.contains("returned\t103\ta1=\"borer runs arm64\"") && table.contains("\tunchecked\n"),
        "{table}"
    );
    assert!(
        table.contains("an arm64 text is checked block by block against the arm64 machine")
            && table.contains("(no signature: an arm64 run passes its inputs untyped)")
            && !table.contains("does not decompile"),
        "{table}"
    );
    for refused in [
        render::oracle_tsv(&p, &a, &o, "0x10000"),
        render::solve_tsv(&p, &a, &o, "0x10000"),
        render::unpack_tsv(&p, &a, &o, "0x10000"),
        render::devirtualize_tsv(&p, &a, &o, "0x10000"),
    ] {
        let why = refused.expect_err("x86 only");
        assert!(
            why.contains("runs x86 and x86-64 code only for now"),
            "{why}"
        );
    }
    assert!(render::hidden_strings_tsv(&p, &a, &o, "").contains("only for now"));
}

/// Random words, with every register pointing into them, run to a stop
/// without a panic from any instruction the decoder hands the machine,
/// and the same words run the same way twice.
#[test]
fn random_words_run_to_a_stop_the_same_way_twice() {
    /// Words in each image.
    const WORDS: usize = 512;
    /// Images run.
    const IMAGES: u64 = 48;
    /// Steps each run is given.
    const STEPS: usize = 2_000;
    let mut x = 0x9e37_79b9_7f4a_7c15u64;
    let mut next = move || {
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        x
    };
    for _ in 0..IMAGES {
        let words: Vec<u32> = (0..WORDS)
            .map(|_| u32::try_from(next() >> 32).expect("32 bits"))
            .collect();
        let p = image(&words);
        let span = u64::try_from(WORDS * 4).expect("a small image");
        let regs: Vec<u64> = (0..31).map(|_| BASE + next() % span).collect();
        let start = BASE + (next() % span) / 4 * 4;
        let run = |p: &Program| {
            let mut m = machine(p);
            m.set_budget(STEPS);
            for (n, v) in regs.iter().enumerate() {
                assert!(m.set_register(&format!("x{n}"), *v));
            }
            let run = m.run(start);
            (run.stop, run.steps, m.registers(), m.vregs())
        };
        assert_eq!(run(&p), run(&p), "from {start:#x}");
    }
}
