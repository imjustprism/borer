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
use borer_engine::program::{Arch, BinaryFormat, Program, Section, Symbol, SymbolKind};

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
    assert!(text.contains("(int64_t a1, int64_t a2)"), "{text}");
    assert!(text.contains("if (a1 >= a2) {"), "{text}");
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
    assert!(text.contains("} while (var2 < a3);"), "{text}");
    assert!(text.contains("int64_t a3)"), "{text}");
}

/// A function that reads all eight integer argument registers and `fa0`
/// lists the double first, and a caller's declaration of it agrees with
/// its own signature.
///
/// `fclass`, which the lifter leaves as asm, keeps the callee a
/// declaration rather than an inlined body.
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
        (0xe205_1353, 4), // ASM: fclass.d t1, fa0
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

/// A callee that hands on what its own callee leaves in `a0`, and whose
/// only caller writes `a0` after the call before reading it, returns
/// nothing: its declaration is `void` and it hands no value back.
#[test]
fn a_result_no_caller_reads_is_void() {
    let code = [
        (0x0000_0013, 4), // ASM: nop
        (0x00c0_00ef, 4), // ASM: jal 0x10010
        (0x0000_0513, 4), // ASM: li a0, 0
        (0x0000_8067, 4), // ASM: ret
        (0x0100_00ef, 4), // ASM: jal 0x10020
        (0x0000_8067, 4), // ASM: ret
        (0x0000_0013, 4), // ASM: nop
        (0x0000_0013, 4), // ASM: nop
        (0x00b5_3023, 4), // ASM: sd a1, 0(a0)
        (0x0000_8067, 4), // ASM: ret
    ];
    let texts = decompiled(&code, Arch::RiscV64);
    let callee = texts.get(1).expect("the callee");
    assert!(callee.contains("void sub_10010("), "{callee}");
    assert!(!callee.contains("return"), "{callee}");
}

/// Decompiles a routine with functions named at `AT` offsets, each by its
/// offset, in the order given.
///
/// # Arguments
///
/// * `code` - The routine.
/// * `named` - Each function's name and offset from `AT`.
fn decompiled_named(code: &[(u32, usize)], named: &[(&str, u64)]) -> Vec<String> {
    let mut p = image(&assemble(code), Arch::RiscV64);
    for &(name, off) in named {
        p.symbols.push(Symbol {
            name: name.to_owned(),
            addr: AT + off,
            kind: SymbolKind::Export,
        });
    }
    let a = Analysis::compute(&p);
    named
        .iter()
        .map(|&(_, off)| decompile(&p, &a, &Overlay::default(), AT + off).expect("decompiles"))
        .collect()
}

/// A result an `ecall` may read after the call is not taken as dropped:
/// a function handing on its own callee's `a0` keeps its result open.
#[test]
fn a_result_a_syscall_may_read_is_not_dropped() {
    let code = [
        (0x0000_0013, 4), // ASM: nop
        (0x01c0_00ef, 4), // ASM: jal 0x10020
        (0x0400_0893, 4), // ASM: li a7, 64
        (0x0000_0073, 4), // ASM: ecall
        (0x0000_0513, 4), // ASM: li a0, 0
        (0x0000_8067, 4), // ASM: ret
        (0x0000_0013, 4), // ASM: nop
        (0x0000_0013, 4), // ASM: nop
        (0x0100_00ef, 4), // ASM: jal 0x10030
        (0x0000_8067, 4), // ASM: ret
        (0x0000_0013, 4), // ASM: nop
        (0x0000_0013, 4), // ASM: nop
        (0x0030_0513, 4), // ASM: li a0, 3
        (0x0000_8067, 4), // ASM: ret
    ];
    let texts = decompiled_named(&code, &[("forward", 0x20), ("three", 0x30)]);
    let forward = texts.first().expect("the forwarder");
    assert!(!forward.contains("void forward("), "{forward}");
}

/// A double a function leaves in `fa0` and a later call takes as its
/// first float argument is the function's result: `g(f())`.
#[test]
fn a_float_passed_on_to_the_next_call_is_a_result() {
    let code = [
        (0x0000_0013, 4), // ASM: nop
        (0x01c0_00ef, 4), // ASM: jal 0x10020
        (0x0280_00ef, 4), // ASM: jal 0x10030
        (0x0000_8067, 4), // ASM: ret
        (0x0000_0013, 4), // ASM: nop
        (0x0000_0013, 4), // ASM: nop
        (0x0000_0013, 4), // ASM: nop
        (0x0000_0013, 4), // ASM: nop
        (0x0100_00ef, 4), // ASM: jal 0x10030
        (0x0000_8067, 4), // ASM: ret
        (0x0000_0013, 4), // ASM: nop
        (0x0000_0013, 4), // ASM: nop
        (0xe205_0553, 4), // ASM: fmv.x.d a0, fa0
        (0x0000_8067, 4), // ASM: ret
    ];
    let texts = decompiled_named(&code, &[("make", 0x20), ("take", 0x30)]);
    let make = texts.first().expect("the maker");
    assert!(make.contains("double make("), "{make}");
}

/// A result an instruction the decoder leaves unknown may read after the
/// call is not taken as dropped.
#[test]
fn a_result_an_unknown_instruction_may_read_is_not_dropped() {
    let code = [
        (0x0000_0013, 4), // ASM: nop
        (0x01c0_00ef, 4), // ASM: jal 0x10020
        (0x6005_1593, 4), // ASM: clz a1, a0
        (0x0000_0513, 4), // ASM: li a0, 0
        (0x0000_8067, 4), // ASM: ret
        (0x0000_0013, 4), // ASM: nop
        (0x0000_0013, 4), // ASM: nop
        (0x0000_0013, 4), // ASM: nop
        (0x0100_00ef, 4), // ASM: jal 0x10030
        (0x0000_8067, 4), // ASM: ret
        (0x0000_0013, 4), // ASM: nop
        (0x0000_0013, 4), // ASM: nop
        (0x0030_0513, 4), // ASM: li a0, 3
        (0x0000_8067, 4), // ASM: ret
    ];
    let texts = decompiled_named(&code, &[("forward", 0x20), ("three", 0x30)]);
    let forward = texts.first().expect("the forwarder");
    assert!(!forward.contains("void forward("), "{forward}");
}

/// A result the next callee may read after its first branch is not taken
/// as dropped: that callee's prologue does not say.
#[test]
fn a_result_a_branching_callee_may_read_is_not_dropped() {
    let code = [
        (0x0000_0013, 4), // ASM: nop
        (0x01c0_00ef, 4), // ASM: jal 0x10020
        (0x0380_00ef, 4), // ASM: jal 0x10040
        (0x0000_8067, 4), // ASM: ret
        (0x0000_0013, 4), // ASM: nop
        (0x0000_0013, 4), // ASM: nop
        (0x0000_0013, 4), // ASM: nop
        (0x0000_0013, 4), // ASM: nop
        (0x0100_00ef, 4), // ASM: jal 0x10030
        (0x0000_8067, 4), // ASM: ret
        (0x0000_0013, 4), // ASM: nop
        (0x0000_0013, 4), // ASM: nop
        (0x0030_0513, 4), // ASM: li a0, 3
        (0x0000_8067, 4), // ASM: ret
        (0x0000_0013, 4), // ASM: nop
        (0x0000_0013, 4), // ASM: nop
        (0x0005_8463, 4), // ASM: beqz a1, 0x10048
        (0x0015_0513, 4), // ASM: addi a0, a0, 1
        (0x0000_8067, 4), // ASM: ret
    ];
    let texts = decompiled_named(
        &code,
        &[("forward", 0x20), ("three", 0x30), ("branchy", 0x40)],
    );
    let forward = texts.first().expect("the forwarder");
    assert!(!forward.contains("void forward("), "{forward}");
}
/// A caller reading `a1` after the call, the high word of a pair, uses the
/// result though it overwrites `a0`: the callee is not void.
#[test]
fn a_read_of_the_second_result_word_keeps_the_result() {
    let code = [
        (0x0000_0013, 4), // ASM: nop
        (0x01c0_00ef, 4), // ASM: jal 0x10020
        (0x0005_8613, 4), // ASM: mv a2, a1
        (0x0000_0513, 4), // ASM: li a0, 0
        (0x0000_8067, 4), // ASM: ret
        (0x0000_0013, 4), // ASM: nop
        (0x0000_0013, 4), // ASM: nop
        (0x0000_0013, 4), // ASM: nop
        (0x0100_00ef, 4), // ASM: jal 0x10030
        (0x0000_8067, 4), // ASM: ret
        (0x0000_0013, 4), // ASM: nop
        (0x0000_0013, 4), // ASM: nop
        (0x0030_0513, 4), // ASM: li a0, 3
        (0x0000_8067, 4), // ASM: ret
    ];
    let texts = decompiled_named(&code, &[("forward", 0x20), ("three", 0x30)]);
    let forward = texts.first().expect("the forwarder");
    assert!(!forward.contains("void forward("), "{forward}");
}

/// A second result word the next call takes in `a1` is used, though the
/// caller overwrites `a0` first: the callee is not void.
#[test]
fn a_second_result_word_passed_on_keeps_the_result() {
    let code = [
        (0x0000_0013, 4), // ASM: nop
        (0x01c0_00ef, 4), // ASM: jal 0x10020
        (0x0000_0513, 4), // ASM: li a0, 0
        (0x0340_00ef, 4), // ASM: jal 0x10040
        (0x0000_8067, 4), // ASM: ret
        (0x0000_0013, 4), // ASM: nop
        (0x0000_0013, 4), // ASM: nop
        (0x0000_0013, 4), // ASM: nop
        (0x0100_00ef, 4), // ASM: jal 0x10030
        (0x0000_8067, 4), // ASM: ret
        (0x0000_0013, 4), // ASM: nop
        (0x0000_0013, 4), // ASM: nop
        (0x0030_0513, 4), // ASM: li a0, 3
        (0x0000_8067, 4), // ASM: ret
        (0x0000_0013, 4), // ASM: nop
        (0x0000_0013, 4), // ASM: nop
        (0x0005_8613, 4), // ASM: mv a2, a1
        (0x0000_8067, 4), // ASM: ret
    ];
    let texts = decompiled_named(&code, &[("forward", 0x20), ("three", 0x30), ("take", 0x40)]);
    let forward = texts.first().expect("the forwarder");
    assert!(!forward.contains("void forward("), "{forward}");
}

/// Double and single arithmetic on the float argument registers decompiles
/// to the C operators at each width, the parameters and the result typed
/// so.
#[test]
fn float_arithmetic_takes_and_returns_floats() {
    let double = [
        (0x12b5_7553, 4), // ASM: fmul.d fa0, fa0, fa1
        (0x0000_8067, 4), // ASM: ret
    ];
    let text = decompiled(&double, Arch::RiscV64).concat();
    assert!(
        text.contains("double sub_10000(double a1, double a2)"),
        "{text}"
    );
    assert!(text.contains("a1 * a2"), "{text}");
    let single = [
        (0x00b5_7553, 4), // ASM: fadd.s fa0, fa0, fa1
        (0x0000_8067, 4), // ASM: ret
    ];
    let text = decompiled(&single, Arch::RiscV64).concat();
    assert!(
        text.contains("float sub_10000(float a1, float a2)"),
        "{text}"
    );
    assert!(text.contains("a1 + a2"), "{text}");
}

/// A double a function computes and stores is not what it hands back:
/// nothing calls it, and the store, not the return, takes `fa0`.
#[test]
fn a_stored_double_is_no_result() {
    let code = [
        (0x02b5_7553, 4), // ASM: fadd.d fa0, fa0, fa1
        (0x00a5_3027, 4), // ASM: fsd fa0, 0(a0)
        (0x0000_8067, 4), // ASM: ret
    ];
    let text = decompiled(&code, Arch::RiscV64).concat();
    assert!(!text.contains("double sub_10000("), "{text}");
}

/// A double two branches compute into one register and the join reads is
/// a double variable, not an integer one.
#[test]
fn a_double_two_branches_compute_stays_a_double() {
    let code = [
        (0x0005_0663, 4), // ASM: beqz a0, 0x1000c
        (0x02b5_7053, 4), // ASM: fadd.d ft0, fa0, fa1
        (0x0080_006f, 4), // ASM: j 0x10010
        (0x12b5_7053, 4), // ASM: fmul.d ft0, fa0, fa1
        (0xe200_0553, 4), // ASM: fmv.x.d a0, ft0
        (0x0000_8067, 4), // ASM: ret
    ];
    let text = decompiled(&code, Arch::RiscV64).concat();
    assert!(text.contains("double "), "{text}");
    assert!(!text.contains("uint64_t v"), "{text}");
}

/// A negation of a minimum and an absolute value of a fused multiply-add
/// stay the C operators on the call, not integer bit masks of it.
#[test]
fn a_sign_of_a_library_result_stays_a_float_operator() {
    let neg = [
        (0x2ab5_0053, 4), // ASM: fmin.d ft0, fa0, fa1
        (0x2200_1553, 4), // ASM: fneg.d fa0, ft0
        (0x0000_8067, 4), // ASM: ret
    ];
    let text = decompiled(&neg, Arch::RiscV64).concat();
    assert!(text.contains("-fmin(a1, a2)"), "{text}");
    assert!(!text.contains('^'), "{text}");
    let abs = [
        (0x62b5_70c3, 4), // ASM: fmadd.d ft1, fa0, fa1, fa2
        (0x2210_a553, 4), // ASM: fabs.d fa0, ft1
        (0x0000_8067, 4), // ASM: ret
    ];
    let text = decompiled(&abs, Arch::RiscV64).concat();
    assert!(text.contains("fabs(fma(a1, a2, a3))"), "{text}");
    assert!(!text.contains('&'), "{text}");
}

/// An atomic memory operation reads the old value and stores what the
/// operation makes of it.
///
/// The cases are a sum, a signed minimum at the word and an unsigned
/// maximum. A store-conditional is a store that hands back 0.
#[test]
fn atomics_read_then_store_what_they_make() {
    let ret = (0x0000_8067, 4); // ASM: ret
    let cases: [((u32, usize), &[&str]); 4] = [
        ((0x00b5_25af, 4), &["*(uint32_t*)a1 = ", " + a2;"]), // ASM: amoadd.w a1, a1, (a0)
        ((0x80b5_25af, 4), &["(int32_t)", " <= (int32_t)a2"]), // ASM: amomin.w a1, a1, (a0)
        ((0xe0b5_35af, 4), &["umax(*(uint64_t*)a1, a2)"]),    // ASM: amomaxu.d a1, a1, (a0)
        ((0x18b5_252f, 4), &["*(uint32_t*)a1 = a2;", "return 0;"]), // ASM: sc.w a0, a1, (a0)
    ];
    for (insn, wants) in cases {
        let text = decompiled(&[insn, ret], Arch::RiscV64).concat();
        for want in wants {
            assert!(text.contains(want), "{want}: {text}");
        }
        assert!(!text.contains("/* asm"), "{text}");
    }
}

/// Decompiles a routine's first function as a Linux image's.
///
/// # Arguments
///
/// * `code` - The routine's encodings and their lengths.
fn decompiled_elf(code: &[(u32, usize)]) -> String {
    let mut p = image(&assemble(code), Arch::RiscV64);
    p.format = BinaryFormat::Elf;
    let a = Analysis::compute(&p);
    decompile(&p, &a, &Overlay::default(), AT).expect("decompiles")
}

/// An `ecall` with `a7` set to a number the generic table names is that
/// call, its arguments from `a0` up and parameters of the function; a
/// number it does not name stays asm.
#[test]
fn an_ecall_a_number_names_is_that_call() {
    let named = [
        (0x0400_0893, 4), // ASM: li a7, 64
        (0x0000_0073, 4), // ASM: ecall
        (0x0000_8067, 4), // ASM: ret
    ];
    let text = decompiled_elf(&named);
    assert!(text.contains("write(a1, a2, a3);"), "{text}");
    assert!(!text.contains("/* asm"), "{text}");
    let unnamed = [
        (0x3e80_0893, 4), // ASM: li a7, 1000
        (0x0000_0073, 4), // ASM: ecall
        (0x0000_8067, 4), // ASM: ret
    ];
    let text = decompiled_elf(&unnamed);
    assert!(text.contains("/* asm: ecall */"), "{text}");
}

/// A buffer a named `read` fills is read again after it, not the zero
/// stored before the call.
#[test]
fn a_buffer_a_syscall_fills_is_read_again() {
    let code = [
        (0xff01_0113, 4), // ASM: addi sp, sp, -16
        (0x0001_3023, 4), // ASM: sd zero, 0(sp)
        (0x03f0_0893, 4), // ASM: li a7, 63
        (0x0000_0513, 4), // ASM: li a0, 0
        (0x0001_0593, 4), // ASM: mv a1, sp
        (0x0080_0613, 4), // ASM: li a2, 8
        (0x0000_0073, 4), // ASM: ecall
        (0x0001_3503, 4), // ASM: ld a0, 0(sp)
        (0x0101_0113, 4), // ASM: addi sp, sp, 16
        (0x0000_8067, 4), // ASM: ret
    ];
    let text = decompiled_elf(&code);
    assert!(text.contains("read(0, "), "{text}");
    assert!(!text.contains("return 0;"), "{text}");
}

/// An `ecall` stays asm when its call takes a variable argument list, or
/// when its number reaches `a7` where the parameters were not found.
#[test]
fn an_ecall_without_known_arguments_stays_asm() {
    let variadic = [
        (0x0380_0893, 4), // ASM: li a7, 56
        (0x0000_0073, 4), // ASM: ecall
        (0x0000_8067, 4), // ASM: ret
    ];
    let moved = [
        (0x0400_0293, 4), // ASM: li t0, 64
        (0x0002_8893, 4), // ASM: mv a7, t0
        (0x0000_0073, 4), // ASM: ecall
        (0x0000_8067, 4), // ASM: ret
    ];
    for code in [&variadic[..], &moved[..]] {
        let text = decompiled_elf(code);
        assert!(text.contains("/* asm: ecall */"), "{text}");
    }
}

/// A value loaded before a named syscall is what the call takes, not a
/// read through it, and a second syscall's argument the first one's
/// result is no parameter.
#[test]
fn a_syscall_takes_what_was_loaded_and_its_result_is_no_parameter() {
    let loaded = [
        (0x0005_3503, 4), // ASM: ld a0, 0(a0)
        (0x0390_0893, 4), // ASM: li a7, 57
        (0x0000_0073, 4), // ASM: ecall
        (0x0000_8067, 4), // ASM: ret
    ];
    let text = decompiled_elf(&loaded);
    assert!(!text.contains("close(*"), "{text}");
    let chained = [
        (0x0ac0_0893, 4), // ASM: li a7, 172
        (0x0000_0073, 4), // ASM: ecall
        (0x0390_0893, 4), // ASM: li a7, 57
        (0x0000_0073, 4), // ASM: ecall
        (0x0000_8067, 4), // ASM: ret
    ];
    let text = decompiled_elf(&chained);
    assert!(text.contains("sub_10000()"), "{text}");
    assert!(text.contains("getpid()"), "{text}");
}

/// Where the jump-table tests keep their table, inside the image's page.
const TABLE: u64 = AT + 0x400;

/// Lays out a switch's code with its table at [`TABLE`], resolves it and
/// decompiles the function at [`AT`].
///
/// # Arguments
///
/// * `code` - The encodings and their lengths.
/// * `entries` - The table's 32-bit entries.
/// * `jr` - The `jr`'s offset from [`AT`].
/// * `arch` - [`Arch::RiscV64`] or [`Arch::RiscV32`].
///
/// # Returns
///
/// The table the analysis resolved for the `jr` at `jr`, if any, and the
/// text.
fn switched(
    code: &[(u32, usize)],
    entries: &[u32],
    jr: u64,
    arch: Arch,
) -> (Option<Vec<u64>>, String) {
    let mut bytes = assemble(code);
    bytes.resize(0x400, 0);
    bytes.extend(entries.iter().flat_map(|e| e.to_le_bytes()));
    let p = image(&bytes, arch);
    let a = Analysis::compute(&p);
    let text = decompile(&p, &a, &Overlay::default(), AT).unwrap_or_default();
    (a.jump_tables.get(&(AT + jr)).cloned(), text)
}

/// Returns 32-bit table entries: case addresses at `cases` from [`AT`],
/// less `minus`.
fn entries(cases: [u64; 3], minus: u64) -> Vec<u32> {
    cases
        .iter()
        .map(|c| u32::try_from((AT + c).wrapping_sub(minus) & 0xffff_ffff).expect("32 bits"))
        .collect()
}

/// A switch through a jump table reads as a `switch` with every case.
///
/// The shapes clang writes: at `-O2`, compressed, the table's address
/// from `lui`/`addi` and absolute entries, its check falling through to
/// the dispatch or branching to it (`bgeu c, x, dispatch; j default`), or
/// a store or another load scheduled between the entry's load and the
/// jump; at `-O0` the
/// index spilled to a frame slot across its check; and
/// position-independent, the table formed with `auipc` and each entry an
/// offset from it.
#[test]
fn a_switch_through_a_jump_table_reads_as_one() {
    let optimized = optimized();
    let mut taken = optimized.clone();
    taken[1] = (0x00a5_f363, 4); // ASM: bgeu a1, a0, 0x10008
    taken.insert(2, (0xa831, 2)); // ASM: j 0x10022
    let spilled = spilled();
    let mut stored = optimized.clone();
    stored[1] = (0x02a5_e163, 4); // ASM: bltu a1, a0, 0x10024
    stored.insert(7, (0x00c6_b023, 4)); // ASM: sd a2, 0(a3)
    let mut loaded = stored.clone();
    loaded[7] = (0x0045_a603, 4); // ASM: lw a2, 4(a1)
    let mut relative = vec![
        (0x0020_0593, 4), // ASM: li a1, 2
        (0x02a5_ec63, 4), // ASM: bltu a1, a0, 0x1003c
        (0x0025_1513, 4), // ASM: slli a0, a0, 2
        (0x0000_0597, 4), // ASM: auipc a1, 0
        (0x3f45_8593, 4), // ASM: addi a1, a1, 0x3f4
        (0x00b5_0533, 4), // ASM: add a0, a0, a1
        (0x0005_2503, 4), // ASM: lw a0, 0(a0)
        (0x00b5_0533, 4), // ASM: add a0, a0, a1
        (0x0005_0067, 4), // ASM: jr a0          (0x10020)
    ];
    for value in [0x00a0_0513, 0x0140_0513, 0x01e0_0513, 0x0000_0513] {
        relative.extend([(value, 4), (0x0000_8067, 4)]); // ASM: li a0, v; ret
    }
    for (name, code, cases, minus, jr) in [
        ("-O2", &optimized, [0x14, 0x18, 0x1c], 0, 0x12),
        ("taken check", &taken, [0x16, 0x1a, 0x1e], 0, 0x14),
        ("-O0", &spilled, [0x34, 0x40, 0x4c], 0, 0x30),
        (
            "a store before the jump",
            &stored,
            [0x18, 0x1c, 0x20],
            0,
            0x16,
        ),
        (
            "a load before the jump",
            &loaded,
            [0x18, 0x1c, 0x20],
            0,
            0x16,
        ),
        ("relative", &relative, [0x24, 0x2c, 0x34], TABLE, 0x20),
    ] {
        let (table, text) = switched(code, &entries(cases, minus), jr, Arch::RiscV64);
        assert_eq!(
            table,
            Some(cases.map(|c| AT + c).to_vec()),
            "{name}: {text}"
        );
        assert!(text.contains("switch ("), "{name}: {text}");
        assert!(text.contains("return 20;"), "{name}: {text}");
        assert!(!text.contains("goto *"), "{name}: {text}");
    }
}

/// A jump no check bounds on every way to it resolves no table.
///
/// The cases: no check, a check of another register, entries outside the
/// code, a byte reload of the index on RV32, an `ecall` between the check
/// and the jump, and a second way into the dispatch with a wider check.
#[test]
fn a_switch_its_check_does_not_bound_resolves_none() {
    let optimized = optimized();
    let mut unchecked = optimized.clone();
    unchecked[1] = (0x0000_0013, 4); // ASM: nop
    let mut elsewhere = optimized.clone();
    elsewhere[1] = (0x00c5_ef63, 4); // ASM: bltu a1, a2, 0x10020
    let mut narrowed = spilled();
    narrowed[1] = (0x00a1_2423, 4); // ASM: sw a0, 8(sp)
    narrowed[2] = (0x0081_2583, 4); // ASM: lw a1, 8(sp)
    narrowed[3] = (0x00b1_0823, 4); // ASM: sb a1, 16(sp)
    narrowed[6] = (0x0101_0503, 4); // ASM: lb a0, 16(sp)
    let narrow = entries([0x34, 0x40, 0x4c], 0);
    let (found, text) = switched(&narrowed, &narrow, 0x30, Arch::RiscV32);
    assert_eq!(found, None, "a byte reload on RV32: {text}");
    let mut called = optimized.clone();
    called[1] = (0x02a5_e163, 4); // ASM: bltu a1, a0, 0x10024
    called.insert(2, (0x0000_0073, 4)); // ASM: ecall
    let mut joined = optimized.clone();
    joined.insert(0, (0xc21d, 2)); // ASM: beqz a2, 0x10026
    joined.extend([(0x4591, 2), (0xfea5_ede3, 4), (0xbff1, 2)]); // ASM: li a1, 4; bltu a1, a0, 0x10022; j 0x10008
    let near = entries([0x14, 0x18, 0x1c], 0);
    for (name, code, table, jr) in [
        ("no check", &unchecked, near.clone(), 0x12),
        ("a check of another register", &elsewhere, near, 0x12),
        (
            "entries outside the code",
            &optimized,
            vec![0x9000_0000; 3],
            0x12,
        ),
        (
            "an ecall after the check",
            &called,
            entries([0x18, 0x1c, 0x20], 0),
            0x16,
        ),
        (
            "a second way in",
            &joined,
            entries([0x16, 0x1a, 0x1e], 0),
            0x14,
        ),
    ] {
        let (found, text) = switched(code, &table, jr, Arch::RiscV64);
        assert_eq!(found, None, "{name}: {text}");
    }
}

/// The `-O2` shape of a three-case switch: compressed, its table at
/// [`TABLE`], its `jr` at `0x12` and its cases at `0x14`, `0x18`, `0x1c`.
fn optimized() -> Vec<(u32, usize)> {
    vec![
        (0x4589, 2),      // ASM: li a1, 2
        (0x00a5_ef63, 4), // ASM: bltu a1, a0, 0x10020
        (0x050a, 2),      // ASM: slli a0, a0, 2
        (0x65c1, 2),      // ASM: lui a1, 0x10
        (0x4005_8593, 4), // ASM: addi a1, a1, 0x400
        (0x952e, 2),      // ASM: add a0, a0, a1
        (0x4108, 2),      // ASM: lw a0, 0(a0)
        (0x8502, 2),      // ASM: jr a0          (0x10012)
        (0x4529, 2),      // ASM: li a0, 10
        (0x8082, 2),      // ASM: ret
        (0x4551, 2),      // ASM: li a0, 20
        (0x8082, 2),      // ASM: ret
        (0x4579, 2),      // ASM: li a0, 30
        (0x8082, 2),      // ASM: ret
        (0x4501, 2),      // ASM: li a0, 0
        (0x8082, 2),      // ASM: ret
    ]
}

/// The `-O0` shape of the same switch: the index spilled to a frame slot
/// across its check, its `jr` at `0x30` and its cases at `0x34`, `0x40`,
/// `0x4c`.
fn spilled() -> Vec<(u32, usize)> {
    let mut code = vec![
        (0xfe01_0113, 4), // ASM: addi sp, sp, -32
        (0x00a1_3423, 4), // ASM: sd a0, 8(sp)
        (0x0081_3583, 4), // ASM: ld a1, 8(sp)
        (0x00b1_3823, 4), // ASM: sd a1, 16(sp)
        (0x0020_0513, 4), // ASM: li a0, 2
        (0x04b5_6263, 4), // ASM: bltu a0, a1, 0x10058
        (0x0101_3503, 4), // ASM: ld a0, 16(sp)
        (0x0025_1513, 4), // ASM: slli a0, a0, 2
        (0x0001_05b7, 4), // ASM: lui a1, 0x10
        (0x4005_8593, 4), // ASM: addi a1, a1, 0x400
        (0x00b5_0533, 4), // ASM: add a0, a0, a1
        (0x0005_2503, 4), // ASM: lw a0, 0(a0)
        (0x0005_0067, 4), // ASM: jr a0          (0x10030)
    ];
    for value in [0x00a0_0513, 0x0140_0513, 0x01e0_0513, 0x0000_0513] {
        code.extend([(value, 4), (0x0201_0113, 4), (0x0000_8067, 4)]); // ASM: li a0, v; addi sp, sp, 32; ret
    }
    code
}

/// A check admitting more entries than a table may hold resolves no
/// table, rather than the first 4096 of its cases.
#[test]
fn a_switch_too_wide_for_a_table_resolves_none() {
    let mut bytes = assemble(&[
        (0x6585, 2),      // ASM: lui a1, 0x1
        (0x3885_8593, 4), // ASM: addi a1, a1, 0x388  (5000)
        (0x00a5_eb63, 4), // ASM: bltu a1, a0, 0x1001c
        (0x050a, 2),      // ASM: slli a0, a0, 2
        (0x65c1, 2),      // ASM: lui a1, 0x10
        (0x4005_8593, 4), // ASM: addi a1, a1, 0x400
        (0x952e, 2),      // ASM: add a0, a0, a1
        (0x4108, 2),      // ASM: lw a0, 0(a0)
        (0x8502, 2),      // ASM: jr a0          (0x10016)
        (0x4529, 2),      // ASM: li a0, 10
        (0x8082, 2),      // ASM: ret
        (0x4501, 2),      // ASM: li a0, 0
        (0x8082, 2),      // ASM: ret
    ]);
    bytes.resize(0x400, 0);
    let case = u32::try_from(AT + 0x18).expect("32 bits");
    bytes.extend((0..5001).flat_map(|_| case.to_le_bytes()));
    bytes.resize(0x8000, 0);
    let text = Section::mapped(".text", AT, 0, 0x8000, true, true);
    let p = Program::raw(bytes, Arch::RiscV64, 0, Some(AT), vec![text]);
    let a = Analysis::compute(&p);
    let cases = a.jump_tables.get(&(AT + 0x16)).map(Vec::len);
    assert_eq!(cases, None, "a table cut to its first cases");
}
