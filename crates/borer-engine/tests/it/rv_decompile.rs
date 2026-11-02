//! RISC-V functions decompiled to pseudo-C.
//!
//! Hand-encoded routines decompile with the parameters the calling
//! convention passes in `a0` to `a7` and the result it hands back in `a0`:
//! a sum of two parameters at both register widths, a call whose argument
//! and result travel in `a0` with the frame's save of `ra` left out, a
//! signed comparison choosing what to return, a wrapper whose `tail`
//! sequence hands its parameter on, and a value a preserved register
//! loaded from a slot kept across a call that may change the slot.
#![expect(
    clippy::missing_panics_doc,
    clippy::expect_used,
    reason = "assertions are the point of a test"
)]

use borer_engine::analysis::decompile::decompile;
use borer_engine::analysis::protos::Proto;
use borer_engine::analysis::render::calls_tsv;
use borer_engine::analysis::{Analysis, Overlay};
use borer_engine::program::{Arch, Symbol, SymbolKind};

use crate::rv_emulate::{AT, assemble, image};

/// Decompiles every function of a routine, in address order.
///
/// # Arguments
///
/// * `code` - The routine's encodings and their lengths.
/// * `arch` - [`Arch::RiscV64`] or [`Arch::RiscV32`].
fn decompiled(code: &[(u32, usize)], arch: Arch) -> Vec<String> {
    let p = image(&assemble(code), arch);
    let a = Analysis::compute(&p);
    a.functions
        .iter()
        .map(|f| decompile(&p, &a, &Overlay::default(), f.entry).expect("decompiles"))
        .collect()
}

/// `add a0, a0, a1; ret` takes two parameters and returns their sum, at
/// the width of each machine's registers.
#[test]
fn a_sum_takes_two_parameters() {
    let code = [
        (0x00b5_0533, 4), // ASM: add a0, a0, a1
        (0x0000_8067, 4), // ASM: ret
    ];
    let text = decompiled(&code, Arch::RiscV64).concat();
    assert!(
        text.contains("uint64_t sub_10000(uint64_t a1, uint64_t a2)"),
        "{text}"
    );
    assert!(text.contains("return a1 + a2;"), "{text}");
    let text = decompiled(&code, Arch::RiscV32).concat();
    assert!(
        text.contains("uint32_t sub_10000(uint32_t a1, uint32_t a2)"),
        "{text}"
    );
}

/// A call passes its argument in `a0` and its result comes back there;
/// the prologue's save of `ra` and the stack adjustments print nothing,
/// and the callee reads its parameter as a pointer.
#[test]
fn a_call_passes_and_returns_in_a0() {
    let code = [
        (0xff01_0113, 4), // ASM: addi sp, sp, -16
        (0x0011_3423, 4), // ASM: sd ra, 8(sp)
        (0x0055_0513, 4), // ASM: addi a0, a0, 5
        (0x0140_00ef, 4), // ASM: jal 0x10020
        (0x0081_3083, 4), // ASM: ld ra, 8(sp)
        (0x0101_0113, 4), // ASM: addi sp, sp, 16
        (0x0000_8067, 4), // ASM: ret
        (0x0000_0013, 4), // ASM: nop
        (0x0085_2503, 4), // ASM: lw a0, 8(a0)
        (0x0000_8067, 4), // ASM: ret
    ];
    let texts = decompiled(&code, Arch::RiscV64);
    let caller = texts.first().expect("the caller");
    assert!(caller.contains("return sub_10020(a1 + 5);"), "{caller}");
    let mut words = caller.split(|c: char| !c.is_ascii_alphanumeric());
    assert!(!words.any(|w| w == "ra"), "{caller}");
    let callee = texts.get(1).expect("the callee");
    assert!(callee.contains("sub_10020(void *a1)"), "{callee}");
    assert!(callee.contains("return *(int32_t*)(a1 + 8);"), "{callee}");
}

/// A signed comparison of two parameters chooses which one comes back.
#[test]
fn a_signed_branch_chooses_the_result() {
    let code = [
        (0x00b5_4463, 4), // ASM: blt a0, a1, 0x10008
        (0x0005_8513, 4), // ASM: mv a0, a1
        (0x0000_8067, 4), // ASM: ret
    ];
    let text = decompiled(&code, Arch::RiscV64).concat();
    assert!(text.contains("(int64_t)a1 >= (int64_t)a2"), "{text}");
    assert!(text.contains("return a2;"), "{text}");
}

/// A wrapper that hands its unchanged `a0` on through a `tail` sequence
/// (`auipc` and `jr`) to a function a symbol names takes it as a
/// parameter.
#[test]
fn a_tail_through_auipc_hands_its_parameter_on() {
    let code = [
        (0x0000_0317, 4), // ASM: auipc t1, 0x0
        (0x0103_0067, 4), // ASM: jr 16(t1)
        (0x0000_0013, 4), // ASM: nop
        (0x0000_0013, 4), // ASM: nop
        (0x0085_2503, 4), // ASM: lw a0, 8(a0)
        (0x0000_8067, 4), // ASM: ret
    ];
    let mut p = image(&assemble(&code), Arch::RiscV64);
    p.symbols.push(Symbol {
        name: "callee".to_owned(),
        addr: AT + 0x10,
        kind: SymbolKind::Local,
    });
    let a = Analysis::compute(&p);
    let wrapper = decompile(&p, &a, &Overlay::default(), AT).expect("decompiles");
    assert!(wrapper.contains("sub_10000(uint64_t a1)"), "{wrapper}");
    assert!(wrapper.contains("return callee(a1);"), "{wrapper}");
}

/// A value loaded from a stack slot into a preserved register before a
/// call that is handed the slot's address keeps what it loaded: the call
/// may change the slot, not the register.
#[test]
fn a_slot_read_before_a_call_keeps_its_value() {
    let code = [
        (0xfe01_0113, 4), // ASM: addi sp, sp, -32
        (0x0011_3c23, 4), // ASM: sd ra, 24(sp)
        (0x0081_3823, 4), // ASM: sd s0, 16(sp)
        (0x0000_0013, 4), // ASM: nop
        (0x0081_3403, 4), // ASM: ld s0, 8(sp)
        (0x0081_0513, 4), // ASM: addi a0, sp, 8
        (0x0180_00ef, 4), // ASM: jal 0x10030
        (0x0004_0513, 4), // ASM: mv a0, s0
        (0x0181_3083, 4), // ASM: ld ra, 24(sp)
        (0x0101_3403, 4), // ASM: ld s0, 16(sp)
        (0x0201_0113, 4), // ASM: addi sp, sp, 32
        (0x0000_8067, 4), // ASM: ret
        (0x0005_3023, 4), // ASM: sd zero, 0(a0)
        (0x0000_8067, 4), // ASM: ret
    ];
    let texts = decompiled(&code, Arch::RiscV64);
    let caller = texts.first().expect("the caller");
    eprintln!("{caller}");
    assert!(
        caller.contains("return a1;") || caller.contains("return s0;"),
        "{caller}"
    );
}

/// A division or remainder by zero gives what RISC-V defines, not C's
/// undefined result: all ones for a quotient, the dividend for a
/// remainder, tested where the divisor may be zero.
#[test]
fn a_zero_divisor_gives_what_risc_v_defines() {
    let cases: [(u32, &str); 3] = [
        (0x0205_5533, "return -1;"), // ASM: divu a0, a0, zero
        (0x02b5_5533, "return (a2 == 0 ? -1 : a1 / a2);"), // ASM: divu a0, a0, a1
        (0x02b5_7533, "return (a2 == 0 ? a1 : a1 % a2);"), // ASM: remu a0, a0, a1
    ];
    for (word, want) in cases {
        let text = decompiled(&[(word, 4), (0x0000_8067, 4)], Arch::RiscV64).concat();
        assert!(text.contains(want), "{text}");
    }
}

/// A call through a register holding an odd constant goes where the
/// machine goes, bit 0 cleared, and names the function there.
#[test]
fn a_call_through_an_odd_constant_clears_bit_0() {
    let code = [
        (0x0000_0297, 4), // ASM: auipc t0, 0x0
        (0x0112_8293, 4), // ASM: addi t0, t0, 17
        (0x0002_80e7, 4), // ASM: jalr t0
        (0x0000_8067, 4), // ASM: ret
        (0x0015_0513, 4), // ASM: addi a0, a0, 1
        (0x0000_8067, 4), // ASM: ret
    ];
    let mut p = image(&assemble(&code), Arch::RiscV64);
    p.symbols.push(Symbol {
        name: "callee".to_owned(),
        addr: AT + 0x10,
        kind: SymbolKind::Local,
    });
    let a = Analysis::compute(&p);
    let text = decompile(&p, &a, &Overlay::default(), AT).expect("decompiles");
    assert!(text.contains("callee("), "{text}");
}

/// A signed division by a register that may hold -1 gives the negated
/// dividend there, as RISC-V defines the one overflowing case.
#[test]
fn a_signed_division_by_minus_one_negates() {
    let code = [
        (0x02b5_4533, 4), // ASM: div a0, a0, a1
        (0x0000_8067, 4), // ASM: ret
    ];
    let text = decompiled(&code, Arch::RiscV64).concat();
    assert!(
        text.contains("a2 == -1 ? -a1 : (int64_t)a1 / (int64_t)a2"),
        "{text}"
    );
}

/// A store the lifter does not model may change any stack slot, so a load
/// after it reads the slot rather than what an earlier store left there.
#[test]
fn an_unmodeled_store_ends_what_a_slot_held() {
    let code = [
        (0xff01_0113, 4), // ASM: addi sp, sp, -16
        (0x0001_3023, 4), // ASM: sd zero, 0(sp)
        (0x00a1_3027, 4), // ASM: fsd fa0, 0(sp)
        (0x0001_3503, 4), // ASM: ld a0, 0(sp)
        (0x0101_0113, 4), // ASM: addi sp, sp, 16
        (0x0000_8067, 4), // ASM: ret
    ];
    let text = decompiled(&code, Arch::RiscV64).concat();
    assert!(!text.contains("return 0;"), "{text}");
}

/// Decompiles a caller and a callee a symbol names: `code` calls
/// `AT + 0x10`, where the callee returns.
///
/// # Arguments
///
/// * `code` - The routine.
/// * `callee` - The callee's name, which may carry a declaration.
fn with_named_callee(code: &[(u32, usize)], callee: &str) -> (String, String) {
    let mut p = image(&assemble(code), Arch::RiscV64);
    p.symbols.push(Symbol {
        name: callee.to_owned(),
        addr: AT + 0x10,
        kind: SymbolKind::Export,
    });
    let a = Analysis::compute(&p);
    let text = |at| decompile(&p, &a, &Overlay::default(), at).expect("decompiles");
    (text(AT), text(AT + 0x10))
}

/// A call to a function declared with a variable list passes the values
/// the caller set past the fixed arguments.
#[test]
fn a_variadic_call_passes_its_extra_values() {
    let code = [
        (0x0070_0593, 4), // ASM: li a1, 7
        (0x00c0_00ef, 4), // ASM: jal 0x10010
        (0x0000_8067, 4), // ASM: ret
        (0x0000_0013, 4), // ASM: nop
        (0x0000_8067, 4), // ASM: ret
    ];
    let (caller, callee) = with_named_callee(&code, "printf");
    assert!(caller.contains("printf(a1, 7)"), "{caller}");
    assert!(callee.contains("printf(uint64_t a1, ...)"), "{callee}");
}

/// A function declared with more integer parameters than registers takes
/// the rest on the stack, and a call passes them from its stack words.
#[test]
fn declared_parameters_past_the_registers_travel_on_the_stack() {
    let code = [
        (0x0000_0013, 4), // ASM: nop
        (0x00c0_00ef, 4), // ASM: jal 0x10010
        (0x0000_8067, 4), // ASM: ret
        (0x0000_0013, 4), // ASM: nop
        (0x0000_8067, 4), // ASM: ret
    ];
    let (caller, callee) = with_named_callee(&code, "CreateProcessA");
    assert!(callee.contains("uint64_t a9, uint64_t a10)"), "{callee}");
    assert!(caller.contains("a8, arg_0, arg_8)"), "{caller}");
}

/// On RV32 a call's stack arguments take the positions after its eight
/// register arguments in the recorded calls, not the first ones.
#[test]
fn rv32_stack_arguments_follow_the_registers_in_recorded_calls() {
    let code = [
        (0x0000_0013, 4), // ASM: nop
        (0x00c0_00ef, 4), // ASM: jal 0x10010
        (0x0000_8067, 4), // ASM: ret
        (0x0000_0013, 4), // ASM: nop
        (0x0000_8067, 4), // ASM: ret
    ];
    let mut p = image(&assemble(&code), Arch::RiscV32);
    p.symbols.push(Symbol {
        name: "CreateProcessA".to_owned(),
        addr: AT + 0x10,
        kind: SymbolKind::Export,
    });
    let a = Analysis::compute(&p);
    let out = calls_tsv(&p, &a, &Overlay::default(), "CreateProcessA").expect("calls");
    assert!(
        out.contains("CreateProcessA(a1, a2, a3, a4, a5, a6, a7, a8, arg_0, arg_4)"),
        "{out}"
    );
}

/// A loop whose two registers each take the other's value tests its
/// condition at the loop's end.
#[test]
fn a_loop_of_registers_reading_each_other_keeps_its_test() {
    let code = [
        (0x00b5_02b3, 4), // ASM: add t0, a0, a1
        (0x0005_8513, 4), // ASM: mv a0, a1
        (0x0002_8593, 4), // ASM: mv a1, t0
        (0xfec5_4ae3, 4), // ASM: blt a0, a2, 0x10000
        (0x0000_8067, 4), // ASM: ret
    ];
    let text = decompiled(&code, Arch::RiscV64).concat();
    assert!(text.contains("while ((int64_t)"), "{text}");
}

/// A function that reads all eight integer argument registers and `fa0`
/// lists the double first, and a caller's declaration of it agrees with
/// its own signature.
#[test]
fn a_float_past_eight_integers_keeps_its_type() {
    let code = [
        (0x0000_0013, 4), // ASM: nop
        (0x00c0_00ef, 4), // ASM: jal 0x10010
        (0x0000_8067, 4), // ASM: ret
        (0x0000_0013, 4), // ASM: nop
        (0x00b5_02b3, 4), // ASM: add t0, a0, a1
        (0x00d6_02b3, 4), // ASM: add t0, a2, a3
        (0x00f7_02b3, 4), // ASM: add t0, a4, a5
        (0x0118_02b3, 4), // ASM: add t0, a6, a7
        (0xe205_0353, 4), // ASM: fmv.x.d t1, fa0
        (0x0000_8067, 4), // ASM: ret
    ];
    let texts = decompiled(&code, Arch::RiscV64);
    let callee = texts.get(1).expect("the callee");
    assert!(
        callee.contains("sub_10010(double a1, uint64_t a2"),
        "{callee}"
    );
    let caller = texts.first().expect("the caller");
    assert!(caller.contains("sub_10010(double, uint64_t, "), "{caller}");
}

/// Decompiles a routine's function at `AT` under a declared prototype.
///
/// # Arguments
///
/// * `code` - The routine.
/// * `arch` - [`Arch::RiscV64`] or [`Arch::RiscV32`].
/// * `declared` - The prototype, in C.
fn declared_as(code: &[(u32, usize)], arch: Arch, declared: &str) -> String {
    let p = image(&assemble(code), arch);
    let a = Analysis::compute(&p);
    let mut o = Overlay::default();
    o.prototypes
        .insert(AT, Proto::parse(declared).expect("parses"));
    decompile(&p, &a, &o, AT).expect("decompiles")
}

/// On RV32 a declared double is one parameter in `fa0`, not the two
/// stack words an x86 build passes it in.
#[test]
fn an_rv32_declared_double_is_one_parameter() {
    let code = [(0x0000_8067, 4)]; // ASM: ret
    let text = declared_as(&code, Arch::RiscV32, "double f(double x)");
    assert!(text.contains("(double x)"), "{text}");
}

/// A function declared with a double and nine integers takes the ninth
/// integer, its tenth parameter `j`, from the first stack word.
#[test]
fn a_stack_parameter_past_a_float_takes_its_own_position() {
    let code = [
        (0x0001_3503, 4), // ASM: ld a0, 0(sp)
        (0x0000_8067, 4), // ASM: ret
    ];
    let declared =
        "long f(double x, long a, long b, long c, long d, long e, long g, long h, long i, long j)";
    let text = declared_as(&code, Arch::RiscV64, declared);
    assert!(text.contains("return j;"), "{text}");
}

/// On RV32 a declared 64-bit integer takes the pair `a0` and `a1`, which
/// the declaration's positions cannot say, so the body places the
/// parameters and a read of `a2` is the third one, not a local.
#[test]
fn an_rv32_wide_integer_takes_a_register_pair() {
    let code = [
        (0x0006_0513, 4), // ASM: mv a0, a2
        (0x0000_8067, 4), // ASM: ret
    ];
    let text = declared_as(&code, Arch::RiscV32, "uint32_t f(uint64_t x, uint32_t y)");
    assert!(text.contains("return a3;"), "{text}");
}

/// A wrapper that jumps to a wrapper that jumps to a function reading
/// `a0` and `a1` takes both: the walk follows the chain of wrappers.
#[test]
fn a_chain_of_wrappers_takes_what_its_end_reads() {
    let code = [
        (0x0040_006f, 4), // ASM: j 0x10004
        (0x0040_006f, 4), // ASM: j 0x10008
        (0x00b5_0533, 4), // ASM: add a0, a0, a1
        (0x0000_8067, 4), // ASM: ret
    ];
    let mut p = image(&assemble(&code), Arch::RiscV64);
    for (name, addr) in [("first", AT), ("second", AT + 4), ("leaf", AT + 8)] {
        p.symbols.push(Symbol {
            name: name.to_owned(),
            addr,
            kind: SymbolKind::Export,
        });
    }
    let a = Analysis::compute(&p);
    let text = decompile(&p, &a, &Overlay::default(), AT).expect("decompiles");
    assert!(text.contains("first(uint64_t a1, uint64_t a2)"), "{text}");
}

/// A jump that links in a register other than `ra` leaves the address
/// after it there, as a call does.
#[test]
fn a_jump_linking_in_t1_leaves_the_next_address() {
    let code = [
        (0x0040_036f, 4), // ASM: jal t1, 0x10004
        (0x0003_0513, 4), // ASM: mv a0, t1
        (0x0000_8067, 4), // ASM: ret
    ];
    let text = decompiled(&code, Arch::RiscV64).concat();
    assert!(text.contains("return 0x10004;"), "{text}");
}
