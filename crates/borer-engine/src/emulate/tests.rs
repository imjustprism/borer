use super::fpu::{extended_to_f64, f64_to_extended};
use super::{Emulator, PageRun, Stop, TRACE_MAX, fill_byte, lo8};
use crate::program::{Arch, BinaryFormat, Program, Section};

/// Vector moves and clears run instead of stopping the machine.
///
/// A compiler emits these constantly, so a machine without them stops on
/// the first `movaps`: across a hundred functions of one real binary,
/// vector moves were 29 of the 33 unmodeled stops.
///
/// # Panics
///
/// When the run does not reach the return.
#[test]
fn vector_moves_and_clears_run() {
    // ASM: xorps xmm0,xmm0; movaps xmm1,xmm0; movss xmm2,xmm1; ret
    let code: &[u8] = &[
        0x0f, 0x57, 0xc0, 0x0f, 0x28, 0xc8, 0xf3, 0x0f, 0x10, 0xd1, 0xc3,
    ];
    returned(image(code, &[]));
}

/// A `setcc` writes the flag it tests instead of stopping the machine.
///
/// # Panics
///
/// When the run does not reach the return, or the byte is not the flag.
#[test]
fn setcc_writes_the_condition() {
    // ASM: xor eax,eax; cmp eax,0; sete al; ret
    let code: &[u8] = &[0x31, 0xc0, 0x83, 0xf8, 0x00, 0x0f, 0x94, 0xc0, 0xc3];
    let emu = returned(image(code, &[]));
    assert_eq!(emu.register("rax"), Some(1));
}

/// A division divides its whole dividend with its sign.
///
/// `idiv` after `cdq` divides the negative `eax` as negative, a byte
/// `div` divides all of `ax`, and a quotient too wide for its register
/// stops the run where the CPU raises a divide error. Taking only `eax`,
/// unsigned, answered `-7 / 2` with `0x7ffffffc` remainder `1`.
///
/// # Panics
///
/// When a quotient or remainder differs from the CPU's, or the
/// overflowing division runs on.
#[test]
fn a_division_divides_the_whole_signed_dividend() {
    // ASM: mov eax,-7; cdq; mov ecx,2; idiv ecx; ret
    let code: &[u8] = &[
        0xb8, 0xf9, 0xff, 0xff, 0xff, 0x99, 0xb9, 0x02, 0x00, 0x00, 0x00, 0xf7, 0xf9, 0xc3,
    ];
    let emu = returned(image(code, &[]));
    assert_eq!(emu.register("rax"), Some(0xffff_fffd), "quotient -3");
    assert_eq!(emu.register("rdx"), Some(0xffff_ffff), "remainder -1");

    // ASM: mov ax,0x107; mov cl,2; div cl; ret
    let code: &[u8] = &[0x66, 0xb8, 0x07, 0x01, 0xb1, 0x02, 0xf6, 0xf1, 0xc3];
    let emu = returned(image(code, &[]));
    assert_eq!(emu.register("rax"), Some(0x0183), "263 / 2: al 131, ah 1");

    // ASM: mov edx,2; mov eax,0; mov ecx,1; div ecx; ret
    let code: &[u8] = &[
        0xba, 0x02, 0x00, 0x00, 0x00, 0xb8, 0x00, 0x00, 0x00, 0x00, 0xb9, 0x01, 0x00, 0x00, 0x00,
        0xf7, 0xf1, 0xc3,
    ];
    let p = image(code, &[]);
    let mut emu = Emulator::new(&p, 100).expect("emulator");
    let run = emu.run(0x1000);
    assert!(
        matches!(&run.stop, Stop::Unmodeled(why) if why == "divide overflow"),
        "{:?}",
        run.stop
    );
}

/// `neg` sets the flags of `0 - operand`.
///
/// An absolute value is `neg` then `cmovs`, and `neg` then `sbb` turns
/// "not zero" into a mask; with the flags left as they were, both took
/// whatever the instruction before had set.
///
/// # Panics
///
/// When the sign or carry after `neg` is not the subtraction's.
#[test]
fn neg_sets_the_flags_of_a_subtraction_from_zero() {
    // ASM: mov eax,5; neg eax; sets cl; setc dl; ret
    let code: &[u8] = &[
        0xb8, 0x05, 0x00, 0x00, 0x00, 0xf7, 0xd8, 0x0f, 0x98, 0xc1, 0x0f, 0x92, 0xc2, 0xc3,
    ];
    let emu = returned(image(code, &[]));
    assert_eq!(emu.register("rcx"), Some(1), "-5 is negative");
    assert_eq!(emu.register("rdx"), Some(1), "5 is not zero, so carry");
}

/// `ah`, `bh`, `ch` and `dh` are bits 8 to 15 of their register.
///
/// Read as the low byte, `movzx ecx, ah` answered `al`; written as the
/// low byte, `div cl` put its remainder over its quotient.
///
/// # Panics
///
/// When a high byte reads or writes any other bits.
#[test]
fn a_high_byte_register_is_bits_8_to_15() {
    // ASM: mov eax,0x1234; movzx ecx,ah; mov bh,0x56; mov bl,0x78; ret
    let code: &[u8] = &[
        0xb8, 0x34, 0x12, 0x00, 0x00, 0x0f, 0xb6, 0xcc, 0xb7, 0x56, 0xb3, 0x78, 0xc3,
    ];
    let emu = returned(image(code, &[]));
    assert_eq!(emu.register("rcx"), Some(0x12));
    assert_eq!(emu.register("rbx").map(|v| v & 0xffff), Some(0x5678));
}

/// A 32-bit address of 64-bit code wraps at 4 GiB, as the machine sums
/// it.
///
/// `lea rax, [ecx+8]` with `rcx` 0xffffffff is 7; summed at 64 bits it
/// read `0x100000007`.
///
/// # Panics
///
/// When the sum is not cut at 32 bits.
#[test]
fn a_32_bit_address_of_64_bit_code_wraps_at_4_gib() {
    let code: &[u8] = &[
        0x67, 0x48, 0x8d, 0x41, 0x08, // ASM: lea rax, [ecx+8]
        0xc3, // ASM: ret
    ];
    let p = image(code, &[]);
    let mut emu = Emulator::new(&p, 10).expect("emulator");
    assert!(emu.set_register("rcx", 0xffff_ffff));
    assert_eq!(emu.run(0x1000).stop, Stop::Returned);
    assert_eq!(emu.register("rax"), Some(7));
}

/// A stop reason reads as words with its address in hex, not as the
/// enum's syntax or a decimal.
///
/// # Panics
///
/// When a reason reads as a variant or an address as decimal.
#[test]
fn a_stop_reason_reads_as_words_in_hex() {
    for (stop, words) in [
        (Stop::Fault(0x7fff_0000_0028), "fault at 0x7fff00000028"),
        (Stop::Stopped(0x1400), "stopped at 0x1400"),
        (Stop::Derailed(0x2000), "derailed at 0x2000"),
        (Stop::Unmodeled("Xgetbv".to_owned()), "unmodeled Xgetbv"),
        (Stop::Returned, "returned"),
        (Stop::Budget, "budget exhausted"),
        (Stop::Exited, "the program exited"),
        (
            Stop::Limit(super::Limit::Calls),
            "stopped: api call limit (65536 recorded)",
        ),
        (Stop::Limit(super::Limit::Time), "stopped: time limit"),
    ] {
        assert_eq!(stop.to_string(), words);
    }
}

/// A `syscall` is answered instead of stopping an ELF's bootstrap.
///
/// `mmap` hands out a region the following store writes through,
/// `write` returns its count, an unknown number answers zero with the
/// run continuing, and the exit numbers end the program.
///
/// # Panics
///
/// When any answer, the clobbered `rcx`, or the exit differs.
#[test]
fn a_syscall_is_answered_and_the_exit_numbers_end_the_program() {
    // ASM: mov eax,9; xor edi,edi; mov esi,0x1000; xor edx,edx;
    //      mov r10d,0x22; xor r8d,r8d; xor r9d,r9d; syscall;
    //      mov rsi,rax; mov dword [rsi],0x44434241; mov eax,[rsi]; ret
    let code: &[u8] = &[
        0xb8, 0x09, 0x00, 0x00, 0x00, 0x31, 0xff, 0xbe, 0x00, 0x10, 0x00, 0x00, 0x31, 0xd2, 0x41,
        0xba, 0x22, 0x00, 0x00, 0x00, 0x45, 0x31, 0xc0, 0x45, 0x31, 0xc9, 0x0f, 0x05, 0x48, 0x89,
        0xc6, 0xc7, 0x06, 0x41, 0x42, 0x43, 0x44, 0x8b, 0x06, 0xc3,
    ];
    let p = image(code, &[]);
    let mut emu = Emulator::new(&p, 100).expect("emulator");
    let run = emu.run(0x1000);
    assert!(matches!(run.stop, Stop::Returned), "{}", run.stop);
    assert_eq!(
        emu.register("rax"),
        Some(0x4443_4241),
        "the store wrote through the mmap answer"
    );
    assert_eq!(
        emu.peek(super::ALLOC_BASE),
        Some(0x41),
        "mmap handed out the allocator's first region"
    );
    assert_eq!(
        emu.register("rcx"),
        Some(0x101c),
        "syscall left its return address in rcx"
    );
    assert_eq!(
        emu.api_calls()
            .iter()
            .map(|c| (c.syscall, c.api.as_str()))
            .collect::<Vec<_>>(),
        vec![(Some(9), "mmap")],
        "the number seen was noted"
    );

    // ASM: mov eax,1; mov edi,1; xor esi,esi; mov edx,5; syscall;
    //      mov r8d,eax; mov eax,999; syscall; mov r9d,eax; ret
    let code: &[u8] = &[
        0xb8, 0x01, 0x00, 0x00, 0x00, 0xbf, 0x01, 0x00, 0x00, 0x00, 0x31, 0xf6, 0xba, 0x05, 0x00,
        0x00, 0x00, 0x0f, 0x05, 0x41, 0x89, 0xc0, 0xb8, 0xe7, 0x03, 0x00, 0x00, 0x0f, 0x05, 0x41,
        0x89, 0xc1, 0xc3,
    ];
    let p = image(code, &[]);
    let mut emu = Emulator::new(&p, 100).expect("emulator");
    let run = emu.run(0x1000);
    assert!(matches!(run.stop, Stop::Returned), "{}", run.stop);
    assert_eq!(emu.register("r8"), Some(5), "write returned its count");
    assert_eq!(
        emu.register("r9"),
        Some(0),
        "an unknown number answered zero and the run continued"
    );
    assert!(
        emu.api_calls()
            .iter()
            .any(|c| c.syscall == Some(999) && c.api == "sys_999")
    );
    assert!(emu.neutralized().is_empty(), "{:?}", emu.neutralized());

    // ASM: mov eax,60; xor edi,edi; syscall; mov eax,1; ret
    let code: &[u8] = &[
        0xb8, 0x3c, 0x00, 0x00, 0x00, 0x31, 0xff, 0x0f, 0x05, 0xb8, 0x01, 0x00, 0x00, 0x00, 0xc3,
    ];
    let p = image(code, &[]);
    let mut emu = Emulator::new(&p, 100).expect("emulator");
    let run = emu.run(0x1000);
    assert_eq!(run.stop, Stop::Exited, "{run:?}");
}
/// A byte written before the run executes as code when the run reaches it.
///
/// This is what patching a check away rests on: the bytes go through the
/// same memory a load reads, so instruction fetch has to see them too,
/// and a fetch that shortcut to the image would run the original.
///
/// # Panics
///
/// When the run does not return, or the patch did not execute.
#[test]
fn a_patched_instruction_executes() {
    let p = image(&[0x31, 0xc0, 0xc3], &[]);
    let mut emu = Emulator::new(&p, 100).expect("emulator");
    for (k, b) in [0xb8, 0x34, 0x12, 0x00, 0x00, 0xc3].into_iter().enumerate() {
        emu.poke(0x1000 + k as u64, b);
    }
    let run = emu.run(0x1000);
    assert!(matches!(run.stop, Stop::Returned), "{}", run.stop);
    assert_eq!(emu.register("rax"), Some(0x1234));
}
/// A patch is not reported as code the program unpacked.
///
/// The unpacking trace answers "what did this program write and then
/// run", and an experiment's own patch is not part of that answer.
///
/// # Panics
///
/// When the run does not return, or the patch reads as unpacked code.
#[test]
fn a_patch_is_not_unpacked_code() {
    let p = image(&[0x31, 0xc0, 0xc3], &[]);
    let mut emu = Emulator::new(&p, 100).expect("emulator");
    emu.poke(0x1000, 0xc3);
    let run = emu.run(0x1000);
    assert!(matches!(run.stop, Stop::Returned), "{}", run.stop);
    assert_eq!(emu.oep(), None, "a patch read as an unpacked entry point");
}
/// A run starting at the top of the address space faults, and does not panic.
///
/// The fetch window there runs past the end of the address space, which
/// is not a range a set can be asked for.
///
/// # Panics
///
/// When the run does not fault.
#[test]
fn an_entry_at_the_top_of_memory_faults() {
    let p = image(&[0xc3], &[]);
    let mut emu = Emulator::new(&p, 100).expect("emulator");
    emu.poke(0x1000, 0x90);
    let run = emu.run(u64::MAX);
    assert!(matches!(run.stop, Stop::Fault(_)), "{}", run.stop);
}
/// Every register that can be set can be read back, and a typo is refused.
///
/// # Panics
///
/// When a name sets nothing, is missing from the readout, or a typo is
/// accepted as a register.
#[test]
fn the_register_names_agree() {
    let p = image(&[0xc3], &[]);
    let mut emu = Emulator::new(&p, 100).expect("emulator");
    for (i, name) in super::READOUT_ORDER.iter().enumerate() {
        assert!(emu.set_register(name, i as u64), "{name} sets nothing");
        assert_eq!(emu.register(name), Some(i as u64), "{name} reads back");
    }
    let reported: Vec<&str> = emu.registers().iter().map(|(n, _)| *n).collect();
    assert_eq!(reported, super::READOUT_ORDER.to_vec());
    for typo in ["eaxx", "zzz", "", "RAX", "rsp "] {
        assert!(!emu.set_register(typo, 1), "{typo} was accepted");
    }
    assert!(emu.set_register("eax", 7), "the 32-bit spelling sets rax");
    assert_eq!(emu.register("rax"), Some(7));
}
/// An argument past the fourth lands in the stack slot the callee reads.
///
/// The Microsoft x64 convention puts arguments five and up on the stack,
/// so a routine of more than four arguments cannot be set up at all
/// without writing them there.
///
/// # Panics
///
/// When the run does not return, or the argument did not arrive.
#[test]
fn a_fifth_argument_goes_on_the_stack() {
    // ASM: mov rax,[rsp+0x28]; ret  -- reads argument index 4
    let p = image(&[0x48, 0x8b, 0x44, 0x24, 0x28, 0xc3], &[]);
    let mut emu = Emulator::new(&p, 100).expect("emulator");
    emu.set_arg(4, 0xdead_beef);
    let run = emu.run(0x1000);
    assert!(matches!(run.stop, Stop::Returned), "{}", run.stop);
    assert_eq!(emu.register("rax"), Some(0xdead_beef));
}
/// `jg` is not taken when the compared values are equal.
///
/// Reading the sign flag alone makes "greater" true for equal operands,
/// because equality leaves the sign flag clear. The zero flag is what
/// separates them, so a routine that loops while a counter is greater
/// than a limit ran one iteration too many, silently.
///
/// # Panics
///
/// When the run does not return, or the branch was taken.
#[test]
fn a_greater_than_branch_is_not_taken_on_equality() {
    // ASM: xor eax,eax; cmp eax,eax; jg .taken; mov eax,1; ret
    //      .taken: mov eax,2; ret
    let code: &[u8] = &[
        0x31, 0xc0, 0x39, 0xc0, 0x7f, 0x06, 0xb8, 0x01, 0x00, 0x00, 0x00, 0xc3, 0xb8, 0x02, 0x00,
        0x00, 0x00, 0xc3,
    ];
    let emu = returned(image(code, &[]));
    assert_eq!(emu.register("rax"), Some(1), "the branch was taken");
}

/// A signed comparison reads the overflow flag, not the sign flag.
///
/// Comparing -128 with 1 as bytes leaves the sign flag clear and the
/// overflow flag set, so "less" is true only for a machine that has both.
///
/// # Panics
///
/// When the run does not return, or the branch was not taken.
#[test]
fn a_less_than_branch_reads_the_overflow_flag() {
    // ASM: mov al,0x80; cmp al,1; jl .taken; mov eax,1; ret
    //      .taken: mov eax,2; ret
    let code: &[u8] = &[
        0xb0, 0x80, 0x3c, 0x01, 0x7c, 0x06, 0xb8, 0x01, 0x00, 0x00, 0x00, 0xc3, 0xb8, 0x02, 0x00,
        0x00, 0x00, 0xc3,
    ];
    let emu = returned(image(code, &[]));
    assert_eq!(emu.register("rax"), Some(2), "the branch was not taken");
}

/// A one-bit shift's overflow decides the jump that reads it.
///
/// `shl eax, 1` of `0x40000000` makes `0x80000000`: the carry out is
/// clear and the result's sign set, so the overflow the SDM defines
/// for a count of one — the result's sign xored with the carry — is
/// set, and `jo` is taken where the run used to stop.
///
/// # Panics
///
/// When the run does not return, or the branch was not taken.
#[test]
fn a_one_bit_shifts_overflow_decides_its_jump() {
    // ASM: mov eax,0x40000000; shl eax,1; jo .taken; mov eax,1; ret
    //      .taken: mov eax,2; ret
    let code: &[u8] = &[
        0xb8, 0x00, 0x00, 0x00, 0x40, 0xd1, 0xe0, 0x70, 0x06, 0xb8, 0x01, 0x00, 0x00, 0x00, 0xc3,
        0xb8, 0x02, 0x00, 0x00, 0x00, 0xc3,
    ];
    let emu = returned(image(code, &[]));
    assert_eq!(emu.register("rax"), Some(2), "the branch was not taken");
}

/// The overflow the one-bit right shifts leave is the SDM's.
///
/// `shr` sets it to the sign of the operand it halved, so halving
/// `0x80000000` sets it and `jo` is taken; `sar` clears it, so the
/// `jo` after halving the same operand arithmetically is not.
///
/// # Panics
///
/// When a run does not return, or either branch went the wrong way.
#[test]
fn the_one_bit_right_shifts_overflow_is_the_sdms() {
    // ASM: mov eax,0x80000000; shr eax,1; jo .taken; mov eax,1; ret
    //      .taken: mov eax,2; ret
    let shr: &[u8] = &[
        0xb8, 0x00, 0x00, 0x00, 0x80, 0xd1, 0xe8, 0x70, 0x06, 0xb8, 0x01, 0x00, 0x00, 0x00, 0xc3,
        0xb8, 0x02, 0x00, 0x00, 0x00, 0xc3,
    ];
    let emu = returned(image(shr, &[]));
    assert_eq!(emu.register("rax"), Some(2), "shr's overflow was clear");

    // ASM: mov eax,0x80000000; sar eax,1; jo .taken; mov eax,1; ret
    //      .taken: mov eax,2; ret
    let sar: &[u8] = &[
        0xb8, 0x00, 0x00, 0x00, 0x80, 0xd1, 0xf8, 0x70, 0x06, 0xb8, 0x01, 0x00, 0x00, 0x00, 0xc3,
        0xb8, 0x02, 0x00, 0x00, 0x00, 0xc3,
    ];
    let emu = returned(image(sar, &[]));
    assert_eq!(emu.register("rax"), Some(1), "sar's overflow was set");
}

/// A signed jump on flags nothing computed stops instead of guessing.
///
/// The overflow of a shift by more than one bit is undefined, which
/// the emulator leaves unknown. Picking a direction would send the run
/// down a path the machine might not take, and every answer after that
/// would belong to the wrong path.
///
/// # Panics
///
/// When the run does not stop, or stops for another reason.
#[test]
fn a_signed_jump_on_unknown_flags_stops() {
    // ASM: mov eax,5; shl eax,2; jg +1; ret; ret
    let code: &[u8] = &[
        0xb8, 0x05, 0x00, 0x00, 0x00, 0xc1, 0xe0, 0x02, 0x7f, 0x01, 0xc3, 0xc3,
    ];
    let p = image(code, &[]);
    let mut emu = Emulator::new(&p, 100).expect("emulator");
    let run = emu.run(0x1000);
    match run.stop {
        Stop::Unmodeled(ref what) => {
            assert!(what.contains("did not set"), "{what}");
        }
        other => panic!("expected an unmodeled stop, got {other}"),
    }
}

/// Lane-wise addition wraps within the lane instead of carrying across.
///
/// A keystream written with SSE mixes several words at once, and a carry
/// leaking into the next lane would corrupt every word after it.
///
/// # Panics
///
/// When the run does not return, or the lane did not wrap.
#[test]
fn a_packed_add_wraps_inside_its_lane() {
    // ASM: mov rax,-1; movq xmm0,rax; mov rax,2; movq xmm1,rax;
    //      paddq xmm0,xmm1; movq rax,xmm0; ret
    let code: &[u8] = &[
        0x48, 0xb8, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x66, 0x48, 0x0f, 0x6e, 0xc0,
        0x48, 0xc7, 0xc0, 0x02, 0x00, 0x00, 0x00, 0x66, 0x48, 0x0f, 0x6e, 0xc8, 0x66, 0x0f, 0xd4,
        0xc1, 0x66, 0x48, 0x0f, 0x7e, 0xc0, 0xc3,
    ];
    let emu = returned(image(code, &[]));
    assert_eq!(emu.register("rax"), Some(1));
}

/// Widening the accumulator keeps its sign.
///
/// # Panics
///
/// When the run does not return, or the value was zero-extended.
#[test]
fn the_accumulator_widens_with_its_sign() {
    // ASM: mov eax,0xffffffff; cdqe; ret
    let code: &[u8] = &[0xb8, 0xff, 0xff, 0xff, 0xff, 0x48, 0x98, 0xc3];
    let emu = returned(image(code, &[]));
    assert_eq!(emu.register("rax"), Some(u64::MAX));
}

/// `cpuid` answers as a plain machine, the same way every run.
///
/// # Panics
///
/// When the vendor is wrong, a hypervisor is reported, or two calls of
/// the same leaf disagree.
#[test]
fn cpuid_reports_a_machine_with_no_hypervisor() {
    let (max, b, c, d) = super::cpuid_leaf(0);
    assert!(max >= 1);
    let vendor: Vec<u8> = [b, d, c].iter().flat_map(|w| w.to_le_bytes()).collect();
    assert_eq!(String::from_utf8_lossy(&vendor), "GenuineIntel");
    assert_eq!(super::cpuid_leaf(1).2 >> 31, 0, "a hypervisor was reported");
    assert_eq!(super::cpuid_leaf(0x4000_0000), (0, 0, 0, 0));
    assert_eq!(super::cpuid_leaf(1), super::cpuid_leaf(1));
}

/// A trace keeps the run's last instructions and says what each changed.
///
/// Final registers answer what a routine computed, not how: a loop's
/// thousand iterations leave one result. The trace follows the run to
/// its end, so the instructions before it stopped are the ones on
/// record, and a run's start is watched by giving it a small budget.
///
/// # Panics
///
/// When the trace is the wrong length or does not name the change.
#[test]
fn a_trace_records_what_each_step_changed() {
    // ASM: mov eax,5; inc rcx; inc rcx; ret
    let code: &[u8] = &[
        0xb8, 0x05, 0x00, 0x00, 0x00, 0x48, 0xff, 0xc1, 0x48, 0xff, 0xc1, 0xc3,
    ];
    let p = image(code, &[]);
    let mut emu = Emulator::new(&p, 100).expect("emulator");
    emu.set_trace(2);
    let run = emu.run(0x1000);
    assert!(matches!(run.stop, Stop::Returned), "{}", run.stop);
    let trace = emu.trace();
    assert_eq!(trace.len(), 2, "{trace:?}");
    assert!(trace[0].contains("rcx=0x2"), "the second inc: {}", trace[0]);
    assert!(trace[1].contains("stopped"), "the return: {}", trace[1]);
    assert!(trace[0].contains("0x1008"), "{}", trace[0]);
}

/// A trace follows a loop to its last iteration, not its first.
///
/// A ring that kept the head would show the counter starting out; one
/// that keeps the tail shows the iteration the run stopped in, which is
/// the one a diagnosis reads.
///
/// # Panics
///
/// When the traced lines are not the loop's last iterations.
#[test]
fn a_trace_keeps_the_tail_of_a_loop() {
    // ASM: mov ecx,3; L: dec ecx; jnz L; ret
    let code: &[u8] = &[0xb9, 0x03, 0x00, 0x00, 0x00, 0xff, 0xc9, 0x75, 0xfc, 0xc3];
    let p = image(code, &[]);
    let mut emu = Emulator::new(&p, 100).expect("emulator");
    emu.set_trace(3);
    emu.run(0x1000);
    let trace = emu.trace();
    assert_eq!(trace.len(), 3, "{trace:?}");
    assert!(
        !trace.iter().any(|l| l.contains("mov")),
        "the loop's head is not the tail: {trace:?}"
    );
    assert!(
        trace.iter().any(|l| l.contains("rcx=0x0")),
        "the final count: {trace:?}"
    );
    assert!(
        trace[2].contains("stopped"),
        "the run's last instruction is its return: {trace:?}"
    );
}

/// The origin watch names the instruction that first produced a value.
///
/// A run's result names a value the analyst did not expect; the watch
/// answers where it was born, in a register or in memory, so the next
/// question (what fed that instruction) has an address to start from.
///
/// # Panics
///
/// When the birth is missed or misnamed.
#[test]
fn an_origin_watch_names_the_birth_instruction() {
    // ASM: mov eax,0x46; shl rax,32; ret
    let code: &[u8] = &[0xb8, 0x46, 0x00, 0x00, 0x00, 0x48, 0xc1, 0xe0, 0x20, 0xc3];
    let p = image(code, &[]);
    let mut emu = Emulator::new(&p, 100).expect("emulator");
    emu.set_origin(Some(0x46_0000_0000));
    emu.run(0x1000);
    let (at, instr) = emu.origin().expect("the shift births the value");
    assert_eq!(at, 0x1005, "{at:#x}");
    assert!(instr.contains("shl"), "{instr}");
}

/// A value assembled in memory by two narrow stores is born by the
/// store that completes it, without ever sitting in a register.
///
/// # Panics
///
/// When the birth is missed or misnamed.
#[test]
fn an_origin_watch_catches_a_value_assembled_in_memory() {
    // ASM: mov dword [0x2000],0; mov eax,0x46; mov [0x2004],eax; ret
    let code: &[u8] = &[
        0xc7, 0x05, 0x00, 0x20, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, // ASM: mov dword ptr [0x2000],0
        0xb8, 0x46, 0x00, 0x00, 0x00, // ASM: mov eax,0x46
        0xa3, 0x04, 0x20, 0x00, 0x00, // ASM: mov [0x2004],eax
        0xc3, // ASM: ret
    ];
    let text = Section::mapped(".text", 0x1000, 0, 0x1000, false, true);
    let data = Section::mapped(".data", 0x2000, 0x1000, 0x1000, true, false);
    let p = Program::raw(code.to_vec(), Arch::X86, 0, Some(0x1000), vec![text, data]);
    let mut emu = Emulator::new(&p, 100).expect("emulator");
    emu.set_origin(Some(0x46_0000_0000));
    emu.run(0x1000);
    let (at, instr) = emu.origin().expect("the second store births the value");
    assert_eq!(at, 0x100f, "{at:#x}");
    assert!(instr.contains("mov"), "{instr}");
}

/// Nothing is recorded unless a trace was asked for.
///
/// # Panics
///
/// When an untraced run records anything.
#[test]
fn an_untraced_run_records_nothing() {
    let p = image(&[0xb8, 0x05, 0x00, 0x00, 0x00, 0xc3], &[]);
    let mut emu = Emulator::new(&p, 100).expect("emulator");
    let _ = emu.run(0x1000);
    assert!(emu.trace().is_empty());
}

/// A shift sets the carry flag from the bit it shifted out.
///
/// The flag was left holding whatever the last arithmetic put there, so
/// a bit test written as a shift and a carry branch read a stale answer.
///
/// # Panics
///
/// When the run does not return, or the branch was not taken.
#[test]
fn a_shift_sets_the_carry_it_shifted_out() {
    // ASM: mov eax,3; shr eax,1; jb .taken; mov eax,1; ret
    //      .taken: mov eax,2; ret
    let code: &[u8] = &[
        0xb8, 0x03, 0x00, 0x00, 0x00, 0xd1, 0xe8, 0x72, 0x06, 0xb8, 0x01, 0x00, 0x00, 0x00, 0xc3,
        0xb8, 0x02, 0x00, 0x00, 0x00, 0xc3,
    ];
    let emu = returned(image(code, &[]));
    assert_eq!(emu.register("rax"), Some(2), "the carry was not set");
}

/// A shift count is taken modulo the operand's width.
///
/// A 32-bit shift by 33 shifts by one. Masking every count at 64-bit
/// width instead cleared the register.
///
/// # Panics
///
/// When the run does not return, or the count was not reduced.
#[test]
fn a_shift_count_wraps_at_the_operand_width() {
    // ASM: mov eax,1; shl eax,33; ret
    let code: &[u8] = &[0xb8, 0x01, 0x00, 0x00, 0x00, 0xc1, 0xe0, 0x21, 0xc3];
    let emu = returned(image(code, &[]));
    assert_eq!(emu.register("rax"), Some(2));
}

/// A rotate through carry carries the flag back into the operand.
///
/// The carry flag is one more bit of the value, which is how a bignum
/// add and a compiler's 128-bit shift are built.
///
/// # Panics
///
/// When the run does not return, or the carry did not come back in.
#[test]
fn a_rotate_through_carry_reads_the_flag() {
    // ASM: mov eax,0x80000000; shl eax,1; rcl eax,1; ret
    // The shift leaves zero with carry set; the rotate brings it back.
    let code: &[u8] = &[0xb8, 0x00, 0x00, 0x00, 0x80, 0xd1, 0xe0, 0xd1, 0xd0, 0xc3];
    let emu = returned(image(code, &[]));
    assert_eq!(emu.register("rax"), Some(1));
}

/// The x87 stack loads, divides and stores an integer.
///
/// A run that met a floating-point divide used to stop there. The
/// hardware keeps eighty-bit values and this keeps doubles, which is
/// exact for the integers these routines load.
///
/// # Panics
///
/// When the run does not return, or the quotient is wrong.
#[test]
fn the_x87_stack_divides_and_stores() {
    // ASM: fild dword [0x2000]; fidiv dword [0x2004];
    //      fistp dword [0x2008]; mov eax,[0x2008]; ret
    let code: &[u8] = &[
        0xdb, 0x04, 0x25, 0x00, 0x20, 0x00, 0x00, 0xda, 0x34, 0x25, 0x04, 0x20, 0x00, 0x00, 0xdb,
        0x1c, 0x25, 0x08, 0x20, 0x00, 0x00, 0x8b, 0x04, 0x25, 0x08, 0x20, 0x00, 0x00, 0xc3,
    ];
    let data: &[u8] = &[0x64, 0, 0, 0, 0x07, 0, 0, 0];
    let emu = returned(image(code, data));
    assert_eq!(emu.register("rax"), Some(14));
}

/// `fxch` swaps `st(0)` with the register it names, and bare `fxch`
/// with `st(1)`.
///
/// # Panics
///
/// When the run does not return, or a value lands in the wrong slot.
#[test]
fn fxch_swaps_st0_with_the_register_it_names() {
    // ASM: fild dword [0x2000]; fild dword [0x2004]; fild dword [0x2008];
    //      fxch st2; fistp dword [0x200c]; fxch; fistp dword [0x2010];
    //      fistp dword [0x2014]; ret
    let code: &[u8] = &[
        0xdb, 0x04, 0x25, 0x00, 0x20, 0x00, 0x00, 0xdb, 0x04, 0x25, 0x04, 0x20, 0x00, 0x00, 0xdb,
        0x04, 0x25, 0x08, 0x20, 0x00, 0x00, 0xd9, 0xca, 0xdb, 0x1c, 0x25, 0x0c, 0x20, 0x00, 0x00,
        0xd9, 0xc9, 0xdb, 0x1c, 0x25, 0x10, 0x20, 0x00, 0x00, 0xdb, 0x1c, 0x25, 0x14, 0x20, 0x00,
        0x00, 0xc3,
    ];
    let data: &[u8] = &[1, 0, 0, 0, 2, 0, 0, 0, 3, 0, 0, 0];
    let emu = returned(image(code, data));
    assert_eq!(emu.peek(0x200c), Some(1));
    assert_eq!(emu.peek(0x2010), Some(3));
    assert_eq!(emu.peek(0x2014), Some(2));
}

/// A 16-bit address reads `di`, not `edi`, and wraps at 64 KiB.
///
/// `edi` holds `0xabcd2001`, so `[di-1]` is `0x2000`: the displacement
/// is the word `0xffff`, and only the wrap makes it minus one.
///
/// # Panics
///
/// When the run does not return, or the byte was not added to.
#[test]
fn a_16_bit_address_reads_di_and_wraps() {
    // ASM: mov edi,0xabcd2001; mov dh,5; add [di-1],dh; ret
    let code: &[u8] = &[
        0xbf, 0x01, 0x20, 0xcd, 0xab, 0xb6, 0x05, 0x67, 0x00, 0x75, 0xff, 0xc3,
    ];
    let emu = returned(image32(code, &[7]));
    assert_eq!(emu.peek(0x2000), Some(12));
}

/// `pop es` pops into the segment register, never into `eax`.
///
/// The decoder numbers `es` 0 among the segment registers, as it numbers
/// `rax` among the general ones, and the pop once wrote the low word of
/// `eax`.
///
/// # Panics
///
/// When the run does not return, or `eax` changed.
#[test]
fn a_segment_register_is_not_eax() {
    // ASM: mov eax,0x11223344; push 0x5566; pop es; ret
    let code: &[u8] = &[
        0xb8, 0x44, 0x33, 0x22, 0x11, 0x68, 0x66, 0x55, 0x00, 0x00, 0x07, 0xc3,
    ];
    let emu = returned(image32(code, &[]));
    assert_eq!(emu.register("eax"), Some(0x1122_3344));
}

/// Builds a raw 32-bit image with `code` at 0x1000 and `data` at 0x2000.
fn image32(code: &[u8], data: &[u8]) -> Program {
    let mut p = image(code, data);
    p.arch = Arch::X86;
    p.is_64 = false;
    p
}

/// A 32-bit routine reads its arguments off the stack and returns.
///
/// `mov eax,[esp+4]; add eax,[esp+8]; ret` with 2 and 3 in the slots
/// answers 5, the stack pointer is back where it started, and the readout
/// names the registers the target has.
#[test]
fn a_32_bit_routine_takes_stack_arguments() {
    let p = image32(&[0x8b, 0x44, 0x24, 0x04, 0x03, 0x44, 0x24, 0x08, 0xc3], &[]);
    let mut emu = Emulator::new(&p, 100).expect("emulator");
    emu.set_arg(0, 2);
    emu.set_arg(1, 3);
    let run = emu.run(0x1000);
    assert_eq!(run.stop, Stop::Returned, "{run:?}");
    assert_eq!(emu.register("eax"), Some(5));
    assert_eq!(emu.register("esp"), Some(super::STACK_BASE_32));
    assert_eq!(emu.registers().first().map(|(n, _)| *n), Some("eax"));
}

/// A 32-bit access that runs past `0xffff_ffff` wraps to address zero,
/// byte by byte, as the machine's linear addresses do.
///
/// `mov eax, 0xfffffffe; mov dword [eax], 0x11223344; mov ecx, [eax]`
/// stores the high half at 0 and 1 and reads the word back whole; with
/// the store unwrapped, the high half lands above 4 GiB and the load
/// mixes it with the fill the verifier's own wrapped read never sees.
#[test]
fn a_32_bit_access_past_the_top_wraps_to_zero() {
    let p = image32(
        &[
            0xb8, 0xfe, 0xff, 0xff, 0xff, // ASM: mov eax, 0xfffffffe
            0xc7, 0x00, 0x44, 0x33, 0x22, 0x11, // ASM: mov dword [eax], 0x11223344
            0x8b, 0x08, // ASM: mov ecx, [eax]
            0xc3, // ASM: ret
        ],
        &[],
    );
    let mut emu = Emulator::new(&p, 10).expect("emulator");
    emu.set_permissive(true);
    emu.set_fill(Some(7));
    assert_eq!(emu.run(0x1000).stop, Stop::Returned);
    assert_eq!(emu.register("ecx"), Some(0x1122_3344));
    assert_eq!(emu.byte_at(0), Some(0x22));
    assert_eq!(emu.byte_at(1), Some(0x11));
    assert_eq!(
        emu.byte_at(0x1_0000_0000),
        Some(fill_byte(7, 0x1_0000_0000))
    );
}

/// A 32-bit allocation steps over an image loaded where allocations
/// start, and fails as the OS would once the space below the API stubs
/// is spent, rather than run into the stubs and the stack above them.
#[test]
fn allocations_step_over_the_image_and_stop_at_the_stubs() {
    let mut p = image32(&[0xc3], &[]);
    p.image_base = super::ALLOC_BASE_32;
    for s in &mut p.sections {
        s.va.0 += super::ALLOC_BASE_32;
    }
    let mut emu = Emulator::new(&p, 1).expect("emulator");
    let regions: Vec<u64> = std::iter::repeat_with(|| emu.allocate())
        .take_while(|&a| a != 0)
        .take(1000)
        .collect();
    assert_eq!(
        regions.first(),
        Some(&(super::ALLOC_BASE_32 + super::api::ALLOC_STRIDE))
    );
    assert!(
        regions
            .windows(2)
            .all(|w| w[1] - w[0] == super::api::ALLOC_STRIDE)
    );
    assert_eq!(
        regions.last().map(|a| a + super::api::ALLOC_STRIDE),
        Some(super::api::API_STUB_BASE_32)
    );
    assert_eq!(emu.allocate(), 0);
}

/// `ret imm16` releases the caller's stack arguments, not just the return
/// address.
///
/// `push 0; push 0; call callee; ret` with `callee: ret 10h` leaves the
/// stack pointer back at its start: the return pops the address and the
/// immediate releases the two pushed words. This is the stdcall epilogue
/// and the shape a packer's depacker returns through; ignoring the
/// immediate desynchronizes every later access to the caller's stack.
#[test]
fn ret_with_an_immediate_releases_arguments() {
    let code = [
        0x6a, 0x00, 0x6a, 0x00, 0xe8, 0x01, 0x00, 0x00, 0x00, 0xc3, 0xc2, 0x10, 0x00,
    ];
    let emu = returned(image(&code, &[]));
    assert_eq!(emu.register("rsp"), Some(super::STACK_BASE));
}

/// The 32-bit stdcall `ret imm16` releases its arguments too.
///
/// The same shape with `ret 8` on a 32-bit image, where each push and the
/// return address are four bytes, returns the stack pointer to its start.
#[test]
fn ret_with_an_immediate_releases_arguments_32() {
    let code = [
        0x6a, 0x00, 0x6a, 0x00, 0xe8, 0x01, 0x00, 0x00, 0x00, 0xc3, 0xc2, 0x08, 0x00,
    ];
    let emu = returned(image32(&code, &[]));
    assert_eq!(emu.register("esp"), Some(super::STACK_BASE_32));
}

/// `pushf`/`popf` round-trip the flags a branch reads.
///
/// The zero flag is set, saved, cleared, then restored from the stack; the
/// `je` afterward is taken because the pop brought the flag back. A
/// protector saves and restores the flags this way around its own work, and
/// before this the run stopped at the first `pushfq` a VM used.
#[test]
fn pushf_and_popf_round_trip_the_flags() {
    let code = [
        0x31, 0xc0, 0x9c, 0x83, 0xf8, 0x01, 0x9d, 0x74, 0x06, 0xb8, 0xaa, 0x00, 0x00, 0x00, 0xc3,
        0xb8, 0xbb, 0x00, 0x00, 0x00, 0xc3,
    ];
    let emu = returned(image(&code, &[]));
    assert_eq!(
        emu.register("eax"),
        Some(0xbb),
        "the pop did not restore ZF"
    );
}

/// The 32-bit `pushfd`/`popfd` round-trip the flags too.
#[test]
fn pushfd_and_popfd_round_trip_the_flags() {
    let code = [
        0x31, 0xc0, 0x9c, 0x83, 0xf8, 0x01, 0x9d, 0x74, 0x06, 0xb8, 0xaa, 0x00, 0x00, 0x00, 0xc3,
        0xb8, 0xbb, 0x00, 0x00, 0x00, 0xc3,
    ];
    let emu = returned(image32(&code, &[]));
    assert_eq!(
        emu.register("eax"),
        Some(0xbb),
        "the pop did not restore ZF"
    );
}

/// A push under a 66h prefix moves the stack two bytes, not the mode's
/// word.
///
/// Four word pushes, 7 first, fill the eight bytes `pop rax` takes, the 7
/// in the top word, and the stack pointer is back at its start for the
/// `ret`. Moving eight bytes a push, the pop read the last 0 and the
/// `ret` took a pushed word for its return address.
///
/// # Panics
///
/// When the run does not return, or `rax` is not the four words.
#[test]
fn a_word_push_moves_the_stack_two_bytes() {
    let code = [
        0x66, 0x6a, 0x07, // ASM: push word 7
        0x66, 0x6a, 0x00, // ASM: push word 0
        0x66, 0x6a, 0x00, // ASM: push word 0
        0x66, 0x6a, 0x00, // ASM: push word 0
        0x58, // ASM: pop rax
        0xc3, // ASM: ret
    ];
    let emu = returned(image(&code, &[]));
    assert_eq!(emu.register("rax"), Some(0x0007_0000_0000_0000));
    assert_eq!(emu.register("rsp"), Some(super::STACK_BASE));
}

/// A pop under a 66h prefix takes two bytes and writes only the low word
/// of its register, and so does the pop of a word `leave`.
///
/// The eight bytes of `push 7` come back a word at a time: `pop ax` takes
/// the 7 and leaves the rest of `rax`, three `pop dx` the zeros, and the
/// stack pointer is back at its start. `66 c9` sets the stack pointer
/// from `rbp` whole, then pops `bp` alone: `rbp` keeps the upper bits of
/// the frame address and takes the pushed 7 below them.
///
/// # Panics
///
/// When a run does not return, a register holds more than its word took,
/// or the stack pointer is not back at its start.
#[test]
fn a_word_pop_writes_only_its_word() {
    let code = [
        0x48, 0xc7, 0xc0, 0xff, 0xff, 0xff, 0xff, // ASM: mov rax, -1
        0x6a, 0x07, // ASM: push 7
        0x66, 0x58, // ASM: pop ax
        0x66, 0x5a, // ASM: pop dx
        0x66, 0x5a, // ASM: pop dx
        0x66, 0x5a, // ASM: pop dx
        0xc3, // ASM: ret
    ];
    let emu = returned(image(&code, &[]));
    assert_eq!(emu.register("rax"), Some(0xffff_ffff_ffff_0007));
    assert_eq!(emu.register("rsp"), Some(super::STACK_BASE));
    let code = [
        0x66, 0x6a, 0x07, // ASM: push word 7
        0x48, 0x89, 0xe5, // ASM: mov rbp, rsp
        0x66, 0xc9, // ASM: leave (word)
        0xc3, // ASM: ret
    ];
    let emu = returned(image(&code, &[]));
    let frame = super::STACK_BASE - 2;
    assert_eq!(emu.register("rbp"), Some((frame & !0xffff) | 7));
    assert_eq!(emu.register("rsp"), Some(super::STACK_BASE));
}

/// `pushf` and `popf` under a 66h prefix move the low word of the flags.
///
/// `xor eax, eax` leaves 0x46 (zero, parity and the reserved bit): two
/// word pushes of it fill the dword `pop eax` takes. A dword of zero
/// comes back as two word pops, the first clearing the zero flag, and the
/// stack pointer is back at its start.
///
/// # Panics
///
/// When a run does not return, a value is not the flags' words, or the
/// stack pointer is not back at its start.
#[test]
fn a_word_pushf_and_popf_move_a_word() {
    let code = [
        0x31, 0xc0, // ASM: xor eax, eax
        0x66, 0x9c, // ASM: pushfw
        0x66, 0x9c, // ASM: pushfw
        0x58, // ASM: pop eax
        0xc3, // ASM: ret
    ];
    let emu = returned(image32(&code, &[]));
    assert_eq!(emu.register("eax"), Some(0x0046_0046));
    let code = [
        0x31, 0xc0, // ASM: xor eax, eax
        0x6a, 0x00, // ASM: push 0
        0x66, 0x9d, // ASM: popfw
        0x66, 0x9d, // ASM: popfw
        0x0f, 0x94, 0xc0, // ASM: sete al
        0xc3, // ASM: ret
    ];
    let emu = returned(image32(&code, &[]));
    assert_eq!(emu.register("eax"), Some(0), "the pop did not clear ZF");
    assert_eq!(emu.register("esp"), Some(super::STACK_BASE_32));
}

/// `pusha` and `popa` under a 66h prefix move eight words, and `popa`
/// writes only the low word of each register.
///
/// `ax` comes back as the word pushed while the upper half of `eax` keeps
/// what was written between the two, and the stack pointer is back at
/// its start.
///
/// # Panics
///
/// When the run does not return, `eax` is not the merged value, or the
/// stack pointer is not back at its start.
#[test]
fn a_word_pusha_and_popa_move_eight_words() {
    let code = [
        0xb8, 0x78, 0x56, 0x34, 0x12, // ASM: mov eax, 0x12345678
        0x66, 0x60, // ASM: pushaw
        0xb8, 0xbb, 0xbb, 0xaa, 0xaa, // ASM: mov eax, 0xaaaabbbb
        0x66, 0x61, // ASM: popaw
        0xc3, // ASM: ret
    ];
    let emu = returned(image32(&code, &[]));
    assert_eq!(emu.register("eax"), Some(0xaaaa_5678));
    assert_eq!(emu.register("esp"), Some(super::STACK_BASE_32));
}

/// `fisttp` stores the truncated integer of `st(0)` and pops the stack.
///
/// `fld qword [2.9]; fisttp qword [out]; ret` leaves 2 at `out`: the SSE3
/// truncating integer store, which a Themida VM handler uses and the
/// emulator once rejected as unmodeled.
#[test]
fn fisttp_truncates_and_pops() {
    let code = [
        0xdd, 0x05, 0xfa, 0x0f, 0x00, 0x00, 0xdd, 0x0d, 0x04, 0x10, 0x00, 0x00, 0xc3,
    ];
    let data = [0x33, 0x33, 0x33, 0x33, 0x33, 0x33, 0x07, 0x40];
    let emu = returned(image(&code, &data));
    assert_eq!(
        emu.peek(0x2010),
        Some(2),
        "fisttp did not truncate 2.9 to 2"
    );
    assert_eq!(emu.peek(0x2011), Some(0), "the stored integer is not clean");
}

/// `fistp` rounds to nearest even and stores at the operand's width,
/// and a value the width cannot hold stores the integer indefinite.
#[test]
fn fistp_rounds_to_nearest_even_at_the_operand_width() {
    let code = [
        0xdd, 0x05, 0xfa, 0x0f, 0x00, 0x00, 0xdb, 0x1d, 0x1c, 0x10, 0x00, 0x00, 0xdd, 0x05, 0xf6,
        0x0f, 0x00, 0x00, 0xdf, 0x1d, 0x16, 0x10, 0x00, 0x00, 0xdd, 0x05, 0xf2, 0x0f, 0x00, 0x00,
        0xdb, 0x1d, 0x12, 0x10, 0x00, 0x00, 0xc3,
    ];
    let mut data = Vec::new();
    data.extend_from_slice(&2.5f64.to_le_bytes());
    data.extend_from_slice(&3.5f64.to_le_bytes());
    data.extend_from_slice(&1e20f64.to_le_bytes());
    data.extend_from_slice(&[0xee; 32]);
    let emu = returned(image(&code, &data));
    let dword = |emu: &Emulator<'_>, at: u64| -> u32 {
        u32::from_le_bytes([
            emu.peek(at).unwrap_or(0),
            emu.peek(at + 1).unwrap_or(0),
            emu.peek(at + 2).unwrap_or(0),
            emu.peek(at + 3).unwrap_or(0),
        ])
    };
    assert_eq!(dword(&emu, 0x2028), 2, "2.5 rounds to the even 2");
    assert_eq!(
        (emu.peek(0x202e), emu.peek(0x202f)),
        (Some(4), Some(0)),
        "3.5 rounds to the even 4 in a word"
    );
    assert!(
        emu.peek(0x2030).is_none_or(|b| b == 0xee),
        "a word store leaves the byte after it"
    );
    assert_eq!(dword(&emu, 0x2036), 0x8000_0000, "1e20 is the indefinite");
}

/// `fild word` and `fiadd word` read two bytes, sign-extended.
///
/// The load was clamped to four bytes, so a word operand took the two
/// bytes after it as its high half: `-2` followed by `0x7fff` read as
/// `0x7ffffffe`, and the sum overflowed the dword store into the
/// integer indefinite.
#[test]
fn fild_word_and_fiadd_word_read_two_bytes_sign_extended() {
    // ASM: fild dword [0x2004]; fiadd word [0x2000]; fistp dword [0x2008];
    //      fild word [0x2000]; fistp dword [0x200c];
    //      mov eax,[0x2008]; mov ebx,[0x200c]; ret
    let code: &[u8] = &[
        0xdb, 0x04, 0x25, 0x04, 0x20, 0x00, 0x00, 0xde, 0x04, 0x25, 0x00, 0x20, 0x00, 0x00, 0xdb,
        0x1c, 0x25, 0x08, 0x20, 0x00, 0x00, 0xdf, 0x04, 0x25, 0x00, 0x20, 0x00, 0x00, 0xdb, 0x1c,
        0x25, 0x0c, 0x20, 0x00, 0x00, 0x8b, 0x04, 0x25, 0x08, 0x20, 0x00, 0x00, 0x8b, 0x1c, 0x25,
        0x0c, 0x20, 0x00, 0x00, 0xc3,
    ];
    let data: &[u8] = &[0xfe, 0xff, 0xff, 0x7f, 0x0a, 0x00, 0x00, 0x00];
    let emu = returned(image(code, data));
    assert_eq!(emu.register("rax"), Some(8), "10 + (-2)");
    assert_eq!(emu.register("rbx"), Some(0xffff_fffe), "-2 as a dword");
}

/// `fsincos` leaves the sine and pushes the cosine, `fptan` leaves the
/// tangent and pushes 1.0, and `frndint` rounds to nearest even.
#[test]
fn the_x87_transcendentals_run() {
    let code = [
        0xdd, 0x04, 0x25, 0x00, 0x20, 0x00, 0x00, // ASM: fld qword [0x2000]
        0xd9, 0xfb, // ASM: fsincos
        0xdd, 0x1c, 0x25, 0x10, 0x20, 0x00, 0x00, // ASM: fstp qword [0x2010]
        0xdd, 0x1c, 0x25, 0x18, 0x20, 0x00, 0x00, // ASM: fstp qword [0x2018]
        0xdd, 0x04, 0x25, 0x00, 0x20, 0x00, 0x00, // ASM: fld qword [0x2000]
        0xd9, 0xf2, // ASM: fptan
        0xdd, 0x1c, 0x25, 0x20, 0x20, 0x00, 0x00, // ASM: fstp qword [0x2020]
        0xdd, 0x1c, 0x25, 0x28, 0x20, 0x00, 0x00, // ASM: fstp qword [0x2028]
        0xdd, 0x04, 0x25, 0x08, 0x20, 0x00, 0x00, // ASM: fld qword [0x2008]
        0xd9, 0xfc, // ASM: frndint
        0xdd, 0x1c, 0x25, 0x30, 0x20, 0x00, 0x00, // ASM: fstp qword [0x2030]
        0x48, 0x8b, 0x04, 0x25, 0x10, 0x20, 0x00, 0x00, // ASM: mov rax,[0x2010]
        0x48, 0x8b, 0x1c, 0x25, 0x18, 0x20, 0x00, 0x00, // ASM: mov rbx,[0x2018]
        0x48, 0x8b, 0x0c, 0x25, 0x20, 0x20, 0x00, 0x00, // ASM: mov rcx,[0x2020]
        0x48, 0x8b, 0x14, 0x25, 0x28, 0x20, 0x00, 0x00, // ASM: mov rdx,[0x2028]
        0x48, 0x8b, 0x34, 0x25, 0x30, 0x20, 0x00, 0x00, // ASM: mov rsi,[0x2030]
        0xc3, // ASM: ret
    ];
    let mut data = Vec::new();
    data.extend_from_slice(&0.5f64.to_le_bytes());
    data.extend_from_slice(&2.5f64.to_le_bytes());
    let emu = returned(image(&code, &data));
    assert_eq!(emu.register("rax"), Some(0.5f64.cos().to_bits()));
    assert_eq!(emu.register("rbx"), Some(0.5f64.sin().to_bits()));
    assert_eq!(emu.register("rcx"), Some(1.0f64.to_bits()));
    assert_eq!(emu.register("rdx"), Some(0.5f64.tan().to_bits()));
    assert_eq!(emu.register("rsi"), Some(2.0f64.to_bits()));
}

/// `fld tbyte` reads the extended format and `fstp tbyte` writes it back.
///
/// 1.5 is `0xc000_0000_0000_0000` under exponent `0x3fff`; read as its
/// low eight bytes it was the double -2.0.
#[test]
fn fld_and_fstp_tbyte_carry_the_extended_format() {
    // ASM: fld tbyte [0x2000]; fstp tbyte [0x2010]; fld tbyte [0x2010];
    //      fstp qword [0x2020]; mov rax,[0x2020]; ret
    let code: &[u8] = &[
        0xdb, 0x2c, 0x25, 0x00, 0x20, 0x00, 0x00, 0xdb, 0x3c, 0x25, 0x10, 0x20, 0x00, 0x00, 0xdb,
        0x2c, 0x25, 0x10, 0x20, 0x00, 0x00, 0xdd, 0x1c, 0x25, 0x20, 0x20, 0x00, 0x00, 0x48, 0x8b,
        0x04, 0x25, 0x20, 0x20, 0x00, 0x00, 0xc3,
    ];
    let extended: [u8; 10] = [0, 0, 0, 0, 0, 0, 0, 0xc0, 0xff, 0x3f];
    let emu = returned(image(code, &extended));
    assert_eq!(emu.register("rax"), Some(1.5f64.to_bits()));
    let written: Vec<u8> = (0..10).filter_map(|k| emu.peek(0x2010 + k)).collect();
    assert_eq!(written, extended, "fstp tbyte wrote the ten bytes back");
}

/// The extended format holds every double exactly, and a mantissa
/// wider than a double's rounds to nearest even.
#[test]
fn the_extended_format_round_trips_doubles_and_rounds_wider_mantissas() {
    for v in [
        0.0,
        -0.0,
        1.0,
        1.5,
        -3.25,
        1e300,
        -1e-300,
        f64::MIN_POSITIVE,
        5e-324,
        f64::MAX,
        f64::INFINITY,
        f64::NEG_INFINITY,
    ] {
        let (mantissa, high) = f64_to_extended(v);
        assert_eq!(
            extended_to_f64(mantissa, high).to_bits(),
            v.to_bits(),
            "{v}"
        );
    }
    let (mantissa, high) = f64_to_extended(f64::NAN);
    assert!(extended_to_f64(mantissa, high).is_nan());
    assert_eq!(f64_to_extended(1.5), (0xc000_0000_0000_0000, 0x3fff));
    assert_eq!(f64_to_extended(-2.0), (0x8000_0000_0000_0000, 0xc000));
    assert_eq!(
        extended_to_f64(u64::MAX, 0x3fff),
        2.0,
        "2 - 2^-63 rounds up"
    );
    assert_eq!(
        extended_to_f64(1 << 63 | 1 << 10, 0x3fff),
        1.0,
        "a tie rounds to the even 1"
    );
    assert_eq!(
        extended_to_f64(1 << 63 | 1 << 10 | 1, 0x3fff),
        1.0 + f64::EPSILON,
        "above the tie rounds up"
    );
    assert_eq!(
        extended_to_f64(1 << 63, 0x7ffe),
        f64::INFINITY,
        "past a double"
    );
    assert_eq!(
        extended_to_f64(1 << 63, 1),
        0.0,
        "below a double's denormals"
    );
    assert_eq!(extended_to_f64(1 << 62, 0), 0.0, "an extended denormal");
    assert_eq!(extended_to_f64(1 << 63, 0x7fff), f64::INFINITY);
    assert!(extended_to_f64(1 << 63 | 1 << 62, 0x7fff).is_nan());
}

/// Execution that lands on the scratch stack is a derailed run.
///
/// `mov rax,rsp; jmp rax` transfers into the stack, where no code lives.
/// A protector's VM produces exactly this when the run feeds it a value the
/// real process would have but the emulator cannot, so the stop reads as a
/// guard that won rather than a byte that happened to be unmapped.
#[test]
fn execution_on_the_stack_is_a_derail() {
    let code = [0x48, 0x89, 0xe0, 0xff, 0xe0];
    let p = image(&code, &[]);
    let mut emu = Emulator::new(&p, 100).expect("emulator");
    let run = emu.run(0x1000);
    assert!(matches!(run.stop, Stop::Derailed(_)), "{run:?}");
}

/// The segment reads of a 32-bit prologue answer as an unwatched process.
///
/// `mov eax,fs:[0]; push eax; mov fs:[0],esp; pop eax; mov fs:[0],eax;
/// mov eax,fs:[0x18]; mov ecx,fs:[0x30]; movzx eax,byte [ecx+2]; ret`
/// runs to its return with `eax` zero, since nothing is attached, and
/// `ecx` holding the process block.
#[test]
fn a_32_bit_thread_block_answers_segment_reads() {
    let code = [
        0x64, 0xa1, 0x00, 0x00, 0x00, 0x00, 0x50, 0x64, 0x89, 0x25, 0x00, 0x00, 0x00, 0x00, 0x58,
        0x64, 0xa3, 0x00, 0x00, 0x00, 0x00, 0x64, 0xa1, 0x18, 0x00, 0x00, 0x00, 0x64, 0x8b, 0x0d,
        0x30, 0x00, 0x00, 0x00, 0x0f, 0xb6, 0x41, 0x02, 0xc3,
    ];
    let emu = returned(image32(&code, &[]));
    assert_eq!(emu.register("eax"), Some(0));
    assert_eq!(emu.register("ecx"), Some(super::TEB_32 + 0x1000));
}

/// `loopne` runs while the counter and the zero flag allow:
/// `mov ecx,5; mov eax,0; L: inc eax; cmp eax,3; loopne L; ret` leaves
/// `eax` at 3 and `ecx` at 2.
#[test]
fn loopne_stops_on_the_zero_flag() {
    let code = [
        0xb9, 0x05, 0x00, 0x00, 0x00, 0xb8, 0x00, 0x00, 0x00, 0x00, 0x40, 0x83, 0xf8, 0x03, 0xe0,
        0xfa, 0xc3,
    ];
    let emu = returned(image32(&code, &[]));
    assert_eq!(emu.register("eax"), Some(3));
    assert_eq!(emu.register("ecx"), Some(2));
}

/// Below the first section only the headers are mapped.
///
/// A read there past the headers faults rather than returning the file
/// bytes at that offset, which belong to a section loaded elsewhere.
#[test]
fn only_the_headers_are_mapped_below_the_first_section() {
    let mut bytes = vec![0u8; 0x3000];
    bytes[0x10..0x14].copy_from_slice(&[0x4d, 0x5a, 0x90, 0x00]);
    let code: &[u8] = &[
        0x8b, 0x04, 0x25, 0x10, 0x00, 0x00, 0x10, 0x8b, 0x1c, 0x25, 0x00, 0x08, 0x00, 0x10, 0x8b,
        0x0c, 0x25, 0x00, 0x14, 0x00, 0x10, 0xc3,
    ];
    bytes[0x400..0x400 + code.len()].copy_from_slice(code);
    bytes[0x1400..0x1404].copy_from_slice(&[1, 2, 3, 4]);
    let text = Section::mapped(".text", 0x1001_0000, 0x400, 0x2c00, false, true);
    let mut p = Program::raw(
        bytes,
        Arch::X86_64,
        0x1000_0000,
        Some(0x1001_0000),
        vec![text],
    );
    p.format = BinaryFormat::Pe;
    let mut emu = Emulator::new(&p, 100).expect("emulator");
    let run = emu.run(0x1001_0000);
    assert!(
        matches!(run.stop, Stop::Fault(0x1000_1400)),
        "a read past the headers faults: {:?}",
        run.stop
    );
    assert_eq!(emu.register("rax"), Some(0x0090_5a4d), "the headers read");
    assert_eq!(
        emu.register("rbx"),
        Some(0),
        "the header page's tail reads zero"
    );
}

/// Builds a raw x86-64 image with `code` at 0x1000 and `data` at 0x2000.
pub(super) fn image(code: &[u8], data: &[u8]) -> Program {
    let mut bytes = vec![0u8; 0x3000];
    bytes[0x1000..0x1000 + code.len()].copy_from_slice(code);
    bytes[0x2000..0x2000 + data.len()].copy_from_slice(data);
    let flat = Section::mapped(".flat", 0, 0, 0x3000, true, true);
    Program::raw(bytes, Arch::X86_64, 0, Some(0x1000), vec![flat])
}

/// A routine reading its stack arguments and home space, none of them
/// given, reads zeros and runs on once the frame is backed, as it would
/// over a caller's frame, and faults as before when it is not.
///
/// # Panics
///
/// When the backed read faults or the unbacked one does not.
#[test]
fn stack_arguments_nobody_set_read_as_zero() {
    // ASM: mov rax,[rsp+0x28]; add rax,[rsp+8]; ret
    let code = [
        0x48, 0x8b, 0x44, 0x24, 0x28, 0x48, 0x03, 0x44, 0x24, 0x08, 0xc3,
    ];
    let p = image(&code, &[]);
    let mut strict = Emulator::new(&p, 200).expect("emulator");
    assert!(matches!(strict.run(0x1000).stop, Stop::Fault(_)));
    let mut emu = Emulator::new(&p, 200).expect("emulator");
    emu.back_arguments();
    assert!(matches!(emu.run(0x1000).stop, Stop::Returned));
    assert_eq!(emu.register("rax"), Some(0));
}

/// The stack pointer read without a machine is the one a new machine
/// starts with, at both widths.
///
/// # Panics
///
/// When the two differ.
#[test]
fn the_entry_stack_pointer_is_the_new_machines() {
    let mut p = image(&[0xc3], &[]);
    for arch in [Arch::X86_64, Arch::X86] {
        p.arch = arch;
        let built = Emulator::new(&p, 0).and_then(|e| e.register("rsp"));
        assert_eq!(Emulator::entry_sp(&p), built);
        assert!(built.is_some());
    }
}

/// Runs `p` from 0x1000 to its `ret` and returns the machine.
pub(super) fn returned(p: Program) -> Emulator<'static> {
    let p = Box::leak(Box::new(p));
    let mut emu = Emulator::new(p, 200).expect("emulator");
    let run = emu.run(0x1000);
    assert!(matches!(run.stop, Stop::Returned), "{:?}", run.stop);
    emu
}

/// The emulator runs a real XOR-decrypt loop and produces the plaintext.
///
/// The routine takes `rcx=dst, rdx=src, r8=len, r9=key` and XORs each
/// source byte with the key into the destination, the shape a crypter's
/// string decoder has. Given the ciphertext of "secret payload!!" under
/// key 0x5a, the bytes it writes to the destination are the plaintext.
#[test]
fn runs_an_xor_decrypt_loop() {
    let code = [
        0x4d, 0x31, 0xd2, 0x42, 0x0f, 0xb6, 0x04, 0x12, 0x44, 0x30, 0xc8, 0x42, 0x88, 0x04, 0x11,
        0x49, 0xff, 0xc2, 0x4d, 0x39, 0xc2, 0x72, 0xec, 0xc3,
    ];
    let enc = [
        0x29u8, 0x3f, 0x39, 0x28, 0x3f, 0x2e, 0x7a, 0x2a, 0x3b, 0x23, 0x36, 0x35, 0x3b, 0x3e, 0x7b,
        0x7b,
    ];
    let p = image(&code, &enc);
    let mut emu = Emulator::new(&p, 10_000).expect("bitness");
    emu.set_arg(0, 0x2800);
    emu.set_arg(1, 0x2000);
    emu.set_arg(2, enc.len() as u64);
    emu.set_arg(3, 0x5a);
    let run = emu.run(0x1000);
    assert_eq!(run.stop, Stop::Returned, "run did not return: {run:?}");
    let out: String = (0..enc.len())
        .filter_map(|k| emu.peek(0x2800 + k as u64))
        .map(char::from)
        .collect();
    assert_eq!(out, "secret payload!!", "{run:?}");
}

/// A profile counts loop landings and the pages a loop reads, and a
/// trace line names the loads and stores its instruction made.
///
/// The decrypt loop above lands at its head once per iteration after the
/// first, which falls into it, and reads its sixteen source bytes from
/// the one data page, every load made by the head's `movzx`.
#[test]
fn a_profile_names_the_loop_and_its_reads_and_a_trace_its_memory() {
    let code = [
        0x4d, 0x31, 0xd2, 0x42, 0x0f, 0xb6, 0x04, 0x12, 0x44, 0x30, 0xc8, 0x42, 0x88, 0x04, 0x11,
        0x49, 0xff, 0xc2, 0x4d, 0x39, 0xc2, 0x72, 0xec, 0xc3,
    ];
    let enc = [0x29u8; 16];
    let p = image(&code, &enc);
    let mut emu = Emulator::new(&p, 10_000).expect("bitness");
    emu.set_profile(true);
    emu.set_trace(TRACE_MAX);
    emu.set_arg(0, 0x2800);
    emu.set_arg(1, 0x2000);
    emu.set_arg(2, 16);
    emu.set_arg(3, 0x5a);
    let run = emu.run(0x1000);
    assert_eq!(run.stop, Stop::Returned, "{run:?}");
    let (hot, pages) = emu.profile(4);
    assert_eq!(
        hot.first(),
        Some(&(0x1003, 15)),
        "the loop head is landed at by every back edge: {hot:?}"
    );
    assert_eq!(
        pages,
        vec![PageRun {
            first: 0x2000,
            pages: 1,
            each: 16,
            by: 0x1003,
        }],
        "one page read sixteen times, first by the head's load"
    );
    let trace = emu.trace();
    assert!(
        trace.iter().any(|l| l.contains("r1[0x2000]=0x29")),
        "the first load is named with its value: {trace:?}"
    );
    assert!(
        trace.iter().any(|l| l.contains("w1[0x280f]=0x73")),
        "the last store is named with its value"
    );
}

/// Adjacent pages read equally often merge into one run, and a page read
/// a different number of times starts its own.
#[test]
fn a_profile_merges_equal_adjacent_pages() {
    // ASM: mov al,[0x2000]; mov al,[0x2000]; mov al,[0x3000];
    //      mov al,[0x3000]; mov al,[0x4000]; ret
    let code: &[u8] = &[
        0x8a, 0x04, 0x25, 0x00, 0x20, 0x00, 0x00, 0x8a, 0x04, 0x25, 0x00, 0x20, 0x00, 0x00, 0x8a,
        0x04, 0x25, 0x00, 0x30, 0x00, 0x00, 0x8a, 0x04, 0x25, 0x00, 0x30, 0x00, 0x00, 0x8a, 0x04,
        0x25, 0x00, 0x40, 0x00, 0x00, 0xc3,
    ];
    let mut bytes = vec![0u8; 0x5000];
    bytes[0x1000..0x1000 + code.len()].copy_from_slice(code);
    let flat = Section::mapped(".flat", 0, 0, 0x5000, true, true);
    let p = Program::raw(bytes, Arch::X86_64, 0, Some(0x1000), vec![flat]);
    let mut emu = Emulator::new(&p, 100).expect("emulator");
    emu.set_profile(true);
    let run = emu.run(0x1000);
    assert_eq!(run.stop, Stop::Returned, "{run:?}");
    let (_, pages) = emu.profile(8);
    assert_eq!(
        pages,
        vec![
            PageRun {
                first: 0x2000,
                pages: 2,
                each: 2,
                by: 0x1000,
            },
            PageRun {
                first: 0x4000,
                pages: 1,
                each: 1,
                by: 0x101c,
            },
        ],
        "two equal adjacent pages merge; the odd one stands alone"
    );
}

/// Three-operand `imul` is modeled: a key schedule that multiplies runs.
#[test]
fn runs_a_three_operand_imul() {
    let code = [
        0x48u8, 0xc7, 0xc0, 0x07, 0x00, 0x00, 0x00, 0x48, 0x6b, 0xc0, 0x06, 0x88, 0x04, 0x25, 0x00,
        0x28, 0x00, 0x00, 0xc3,
    ];
    let emu = returned(image(&code, &[]));
    assert_eq!(emu.peek(0x2800), Some(42), "imul result wrong");
}

/// The carry flag is the carry out of the operand width, not the register.
///
/// `add al, al` with `al = 0x80` overflows the byte and must set carry, so
/// the following `adc bl, bl` yields 1. A packer's bit reader pulls each
/// bit out of this carry; computing it from the 64-bit register instead
/// would leave carry clear and corrupt the decompressed stream.
#[test]
fn carry_is_taken_at_the_operand_width() {
    let code = [
        0xb0, 0x80, 0x00, 0xc0, 0x10, 0xdb, 0x88, 0x1c, 0x25, 0x00, 0x28, 0x00, 0x00, 0xc3,
    ];
    let emu = returned(image(&code, &[]));
    assert_eq!(emu.peek(0x2800), Some(1), "8-bit carry was dropped");
}

/// A loop of syscalls or of indirect jumps stops when its record is
/// full, not at the step budget with every call and jump kept.
///
/// # Panics
///
/// When a record grows past the cap or the run ends another way.
#[test]
fn a_record_that_fills_stops_the_run() {
    // ASM: mov eax,39; syscall; jmp 0x1000
    let calls = image(&[0xb8, 0x27, 0x00, 0x00, 0x00, 0x0f, 0x05, 0xeb, 0xf7], &[]);
    let mut emu = Emulator::new(&calls, 1_000_000).expect("emulator");
    let run = emu.run(0x1000);
    assert_eq!(run.stop, Stop::Limit(super::Limit::Calls), "{}", run.stop);
    assert_eq!(emu.api_calls().len(), super::RECORDS_MAX);
    // ASM: lea rax,[rip-7]; jmp rax
    let jumps = image(&[0x48, 0x8d, 0x05, 0xf9, 0xff, 0xff, 0xff, 0xff, 0xe0], &[]);
    let mut emu = Emulator::new(&jumps, 1_000_000).expect("emulator");
    let run = emu.run(0x1000);
    assert_eq!(run.stop, Stop::Limit(super::Limit::Jumps), "{}", run.stop);
    assert_eq!(emu.indirect_jumps().len(), super::RECORDS_MAX);
}

/// A raised cancel flag stops a run at a step boundary, and an
/// emulator made outside its scope never sees it.
///
/// # Panics
///
/// When the run ignores the raised flag or stops off a boundary.
#[test]
fn a_raised_cancel_flag_stops_the_run() {
    let p = image(&[0xeb, 0xfe], &[]);
    let flag = crate::cancel::Cancel::new();
    let mut free = Emulator::new(&p, 10_000).expect("bitness");
    let mut cut = flag.within(|| Emulator::new(&p, 10_000).expect("bitness"));
    let first = cut.run(0x1000);
    assert_eq!(first.stop, Stop::Budget, "an unraised flag stops nothing");
    flag.raise();
    let run = cut.run(0x1000);
    assert_eq!(run.stop, Stop::Limit(super::Limit::Time), "{}", run.stop);
    assert_eq!(run.stop.to_string(), "stopped: time limit");
    assert_eq!(run.steps % super::CANCEL_EVERY, 0);
    assert_eq!(free.run(0x1000).stop, Stop::Budget);
}

/// A run that never returns stops at its step budget rather than looping
/// forever.
#[test]
fn a_tight_loop_stops_at_the_budget() {
    let p = image(&[0xeb, 0xfe], &[]);
    let mut emu = Emulator::new(&p, 500).expect("bitness");
    let run = emu.run(0x1000);
    assert_eq!(run.stop, Stop::Budget);
    assert_eq!(run.steps, 500);
}

/// A best-effort run whose stack pointer has left the stack spends its
/// budget on the returns it skips, rather than popping its way up the
/// address space for free.
///
/// `mov rsp,0x100000000; ret` returns to zero, which nothing maps, and
/// each skip after it pops another zero. When a skip cost no step, a run
/// of 272 steps on one mutated image popped 134 million words over 25
/// seconds before the image header's base field sent it somewhere
/// mapped; without that field it would have run on until the stack.
#[test]
fn skipped_returns_spend_the_budget() {
    let code = [
        0x48, 0xbc, 0x00, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0xc3,
    ];
    let mut bytes = vec![0u8; 0x1000];
    bytes[..code.len()].copy_from_slice(&code);
    let text = Section::mapped(".text", 0x1000, 0, 0x1000, false, true);
    let p = Program::raw(bytes, Arch::X86_64, 0, Some(0x1000), vec![text]);
    let mut emu = Emulator::new(&p, 1000).expect("emulator");
    emu.set_permissive(true);
    let run = emu.run(0x1000);
    assert_eq!(run.stop, Stop::Budget, "{run:?}");
    assert_eq!(run.steps, 1000);
    assert_eq!(emu.skipped(), 998);
}

/// Each iteration of a `rep` string instruction past its first spends a
/// step.
///
/// A count of 64 million under a budget of five stops after three
/// stores, with the counter and pointer where an interrupt would leave
/// them. When an iteration cost nothing, this `rep stosw` ran its whole count
/// under a budget of five: over a second and 750 megabytes on a real
/// library, for a run that promised five steps.
#[test]
fn a_rep_iteration_spends_a_step() {
    let code = [
        0xb9, 0xff, 0xff, 0xff, 0x03, 0xbf, 0x00, 0x28, 0x00, 0x00, 0x66, 0xf3, 0xab, 0xc3,
    ];
    let p = image(&code, &[]);
    let mut emu = Emulator::new(&p, 5).expect("emulator");
    let run = emu.run(0x1000);
    assert_eq!(run.stop, Stop::Budget, "{run:?}");
    assert_eq!(run.steps, 5);
    assert_eq!(emu.register("rcx"), Some(0x03ff_fffc));
    assert_eq!(emu.register("rdi"), Some(0x2806));
    assert_eq!(run.history.len(), 6);
}

/// In 32-bit code a string instruction's pointer wraps at four
/// gigabytes.
///
/// Two `stosb` from `edi = 0xffffffff` write the top byte and then byte
/// zero, and leave `edi` at 1, where it once ran on to `0x100000001`.
#[test]
fn a_32_bit_string_pointer_wraps() {
    let code = [0xbf, 0xff, 0xff, 0xff, 0xff, 0xb0, 0x5a, 0xaa, 0xaa, 0xc3];
    let p = image32(&code, &[]);
    let mut emu = Emulator::new(&p, 20).expect("emulator");
    assert_eq!(emu.run(0x1000).stop, Stop::Returned);
    assert_eq!(emu.register("edi"), Some(1));
    assert_eq!(emu.peek(0xffff_ffff), Some(0x5a));
    assert_eq!(emu.peek(0), Some(0x5a));
    assert_eq!(emu.peek(0x1_0000_0000), None);
}

/// A run that would hold more distinct bytes than its cap stops at the
/// first byte past it, budget or not.
#[test]
fn memory_stops_growing_at_its_cap() {
    let code = [
        0xb9, 0x00, 0x10, 0x00, 0x00, 0xbf, 0x00, 0x28, 0x00, 0x00, 0xf3, 0xaa, 0xc3,
    ];
    let p = image(&code, &[]);
    let mut emu = Emulator::new(&p, 100_000).expect("emulator");
    emu.memory_max = emu.mem.len() + 16;
    let run = emu.run(0x1000);
    assert_eq!(run.stop, Stop::MemoryFull(0x2810), "{run:?}");
    assert_eq!(emu.mem.len(), emu.memory_max);
    assert_eq!(emu.register("rcx"), Some(0x0ff0));
}

/// A permissive run with a fill seed reads a hash of the address from
/// memory nothing backs, so loads at two offsets differ; without the
/// seed it reads zero, and without permissive mode it faults.
#[test]
fn an_unbacked_read_reads_the_fill() {
    let code = [
        0x48, 0x8b, 0x04, 0x25, 0x00, 0x00, 0x00, 0x50, 0x48, 0x8b, 0x1c, 0x25, 0x08, 0x00, 0x00,
        0x50, 0xc3,
    ];
    let p = image(&code, &[]);
    let word = |at: u64| {
        (0..8)
            .rev()
            .fold(0u64, |v, k| (v << 8) | u64::from(fill_byte(7, at + k)))
    };
    let mut emu = Emulator::new(&p, 10).expect("emulator");
    emu.set_permissive(true);
    emu.set_fill(Some(7));
    assert_eq!(emu.run(0x1000).stop, Stop::Returned);
    assert_eq!(emu.register("rax"), Some(word(0x5000_0000)));
    assert_eq!(emu.register("rbx"), Some(word(0x5000_0008)));
    assert_ne!(word(0x5000_0000), word(0x5000_0008));
    assert_eq!(emu.byte_at(0x5000_0003), Some(fill_byte(7, 0x5000_0003)));
    let mut zero = Emulator::new(&p, 10).expect("emulator");
    zero.set_permissive(true);
    assert_eq!(zero.run(0x1000).stop, Stop::Returned);
    assert_eq!(zero.register("rax"), Some(0));
    let mut strict = Emulator::new(&p, 10).expect("emulator");
    assert_eq!(strict.run(0x1000).stop, Stop::Fault(0x5000_0000));
}

/// The emulator never panics, whatever bytes it is pointed at.
///
/// The engine must not panic on input, so running over arbitrary bytes
/// from many offsets must always end in a [`Stop`], never an index or
/// arithmetic panic. This runs thousands of pseudo-random images and
/// asserts every run returns.
#[test]
fn never_panics_on_arbitrary_bytes() {
    let mut seed: u64 = 0x9e37_79b9_7f4a_7c15;
    let mut next = || {
        seed ^= seed << 13;
        seed ^= seed >> 7;
        seed ^= seed << 17;
        seed
    };
    for _ in 0..3000 {
        let mut code = vec![0u8; 256];
        for b in &mut code {
            *b = lo8(next() >> 24);
        }
        let p = image(&code, &[]);
        for start in 0..8u64 {
            let mut emu = Emulator::new(&p, 400).expect("bitness");
            let run = emu.run(0x1000 + start);
            let _ = run.steps;
        }
    }
}
