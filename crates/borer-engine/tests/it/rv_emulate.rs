//! The RISC-V machine.
//!
//! Short routines, hand-encoded from the ISA manual's tables, run in
//! [`Machine`] from a raw RISC-V image with the registers set before and
//! the registers the manual says each leaves: a loop of compressed
//! instructions, the stack and the divide and remainder edge cases, an
//! atomic, the `w` forms, RV32's wrap at 32 bits, a Linux `exit`, and a
//! float operation the machine does not model, which stops the run.
#![expect(
    clippy::missing_panics_doc,
    clippy::expect_used,
    reason = "assertions are the point of a test"
)]

use borer_engine::emulate::Stop;
use borer_engine::emulate::rv::Machine;
use borer_engine::program::{Arch, Program, Section};

/// Where a routine is placed and run.
pub(crate) const AT: u64 = 0x1_0000;

/// Most instructions a routine runs.
const BUDGET: usize = 10_000;

/// Lays out encodings one after the other: a 16-bit one takes two bytes,
/// a 32-bit one four.
///
/// # Arguments
///
/// * `parts` - Each encoding and its length in bytes.
pub(crate) fn assemble(parts: &[(u32, usize)]) -> Vec<u8> {
    parts
        .iter()
        .flat_map(|&(w, n)| w.to_le_bytes().into_iter().take(n))
        .collect()
}

/// A raw RISC-V image of `code` at [`AT`], one page of executable and
/// writable memory.
///
/// # Arguments
///
/// * `code` - The bytes.
/// * `arch` - [`Arch::RiscV64`] or [`Arch::RiscV32`].
pub(crate) fn image(code: &[u8], arch: Arch) -> Program {
    let mut bytes = code.to_vec();
    bytes.resize(0x1000, 0);
    let text = Section::mapped(".text", AT, 0, 0x1000, true, true);
    Program::raw(bytes, arch, 0, Some(AT), vec![text])
}

/// Runs `code` with registers set, and returns the machine after it.
///
/// # Arguments
///
/// * `p` - The image.
/// * `set` - Registers set before the run, by name.
/// * `want` - The stop expected.
fn run<'a>(p: &'a Program, set: &[(&str, u64)], want: &Stop) -> Machine<'a> {
    let mut m = Machine::new(p, BUDGET).expect("RISC-V code");
    for &(name, v) in set {
        assert!(m.set_register(name, v), "{name}");
    }
    let run = m.run(AT);
    assert_eq!(&run.stop, want);
    m
}

/// A loop of compressed instructions sums `n` down to 1.
#[test]
fn a_compressed_loop_sums_down_to_one() {
    let code = assemble(&[
        (0x4581, 2), // ASM: li a1, 0
        (0x95aa, 2), // ASM: add a1, a1, a0
        (0x157d, 2), // ASM: addi a0, a0, -1
        (0xfd75, 2), // ASM: bnez a0, 0x10002
        (0x852e, 2), // ASM: mv a0, a1
        (0x8082, 2), // ASM: ret
    ]);
    let p = image(&code, Arch::RiscV64);
    let m = run(&p, &[("a0", 10)], &Stop::Returned);
    assert_eq!(m.register("a0"), Some(55));
}

/// A value stored on the stack reads back, and division by zero and the
/// one signed overflow give what the M extension defines.
#[test]
fn division_by_zero_and_overflow_are_defined() {
    let code = assemble(&[
        (0x1141, 2),      // ASM: addi sp, sp, -16
        (0xe42a, 2),      // ASM: sd a0, 8(sp)
        (0x6622, 2),      // ASM: ld a2, 8(sp)
        (0x02b6_46b3, 4), // ASM: div a3, a2, a1
        (0x02b6_6733, 4), // ASM: rem a4, a2, a1
        (0x0141, 2),      // ASM: addi sp, sp, 16
        (0x8082, 2),      // ASM: ret
    ]);
    let p = image(&code, Arch::RiscV64);
    let m = run(&p, &[("a0", 7), ("a1", 0)], &Stop::Returned);
    assert_eq!(m.register("a3"), Some(u64::MAX));
    assert_eq!(m.register("a4"), Some(7));
    let min = 1u64 << 63;
    let m = run(&p, &[("a0", min), ("a1", u64::MAX)], &Stop::Returned);
    assert_eq!(m.register("a3"), Some(min));
    assert_eq!(m.register("a4"), Some(0));
    assert_eq!(
        m.register("sp"),
        Machine::new(&p, 0).and_then(|m| m.register("sp"))
    );
}

/// An atomic add hands back the old word sign-extended and stores the sum;
/// the `w` forms sign-extend their 32-bit results.
#[test]
fn an_atomic_and_the_word_forms_sign_extend() {
    let code = assemble(&[
        (0x1141, 2),      // ASM: addi sp, sp, -16
        (0xc02a, 2),      // ASM: sw a0, 0(sp)
        (0x00b1_262f, 4), // ASM: amoadd.w a2, a1, (sp)
        (0x4682, 2),      // ASM: lw a3, 0(sp)
        (0x00b5_073b, 4), // ASM: addw a4, a0, a1
        (0x0141, 2),      // ASM: addi sp, sp, 16
        (0x8082, 2),      // ASM: ret
    ]);
    let p = image(&code, Arch::RiscV64);
    let m = run(&p, &[("a0", 0x7fff_ffff), ("a1", 1)], &Stop::Returned);
    assert_eq!(m.register("a2"), Some(0x7fff_ffff));
    assert_eq!(m.register("a3"), Some(0xffff_ffff_8000_0000));
    assert_eq!(m.register("a4"), Some(0xffff_ffff_8000_0000));
}

/// On RV32 a register holds 32 bits: an add wraps and a shift right
/// arithmetic reads bit 31 as the sign.
#[test]
fn rv32_registers_wrap_at_32_bits() {
    let code = assemble(&[
        (0x0505, 2),      // ASM: addi a0, a0, 1
        (0x41f5_d593, 4), // ASM: srai a1, a1, 0x1f
        (0x8082, 2),      // ASM: ret
    ]);
    let p = image(&code, Arch::RiscV32);
    let m = run(
        &p,
        &[("a0", 0xffff_ffff), ("a1", 0x8000_0000)],
        &Stop::Returned,
    );
    assert_eq!(m.register("a0"), Some(0));
    assert_eq!(m.register("a1"), Some(0xffff_ffff));
}

/// `ecall` with `a7` 93 is Linux `exit`, which ends the run.
#[test]
fn an_exit_call_ends_the_run() {
    let code = assemble(&[
        (0x05d0_0893, 4), // ASM: li a7, 93
        (0x0000_0073, 4), // ASM: ecall
        (0x8082, 2),      // ASM: ret
    ]);
    let p = image(&code, Arch::RiscV64);
    run(&p, &[], &Stop::Exited);
}

/// A float operation the machine does not model stops the run, naming it.
#[test]
fn an_unmodeled_float_operation_stops_the_run() {
    let code = assemble(&[
        (0x02b5_7553, 4), // ASM: fadd.d fa0, fa0, fa1
        (0x8082, 2),      // ASM: ret
    ]);
    let p = image(&code, Arch::RiscV64);
    run(
        &p,
        &[],
        &Stop::Unmodeled("fadd.d fa0, fa0, fa1 at 0x10000".to_owned()),
    );
}

/// Random words run to a stop without a panic at both widths.
#[test]
fn random_words_run_to_a_stop() {
    let mut x: u64 = 0x2545_f491_4f6c_dd1d;
    for _ in 0..2_000 {
        let code: Vec<u8> = (0..16)
            .flat_map(|_| {
                x ^= x << 13;
                x ^= x >> 7;
                x ^= x << 17;
                x.to_le_bytes()
            })
            .collect();
        for arch in [Arch::RiscV64, Arch::RiscV32] {
            let p = image(&code, arch);
            let mut m = Machine::new(&p, 64).expect("RISC-V code");
            let run = m.run(AT);
            assert!(run.steps <= 64);
        }
    }
}

/// On RV32 the program counter wraps at 32 bits: code at the top of the
/// address space runs on into address 0.
#[test]
fn rv32_code_wraps_to_address_0() {
    let mut bytes = assemble(&[(0x0015_0513, 4)]); // ASM: addi a0, a0, 1
    bytes.resize(0x1000, 0);
    bytes.extend(assemble(&[(0x0000_8067, 4)])); // ASM: ret
    bytes.resize(0x2000, 0);
    let top = Section::mapped(".top", 0xffff_fffc, 0, 4, false, true);
    let low = Section::mapped(".low", 0, 0x1000, 0x1000, false, true);
    let p = Program::raw(bytes, Arch::RiscV32, 0, Some(0xffff_fffc), vec![top, low]);
    let mut m = Machine::new(&p, BUDGET).expect("RISC-V code");
    assert!(m.set_register("a0", 1));
    assert_eq!(m.run(0xffff_fffc).stop, Stop::Returned);
    assert_eq!(m.register("a0"), Some(2));
}
