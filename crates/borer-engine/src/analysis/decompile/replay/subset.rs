//! The x86 instructions the replay can check: general registers, scalar
//! and packed integer and float lanes, and the flags a block sets.

use super::*;

/// Tells whether the replay can check an instruction: general registers
/// only, no `lock`, no access through `fs` or `gs`, memory no wider than
/// a word.
///
/// # Arguments
///
/// * `i` - The instruction.
/// * `info` - Register-access facts.
fn integer(i: &Instruction, info: &mut InstructionInfoFactory) -> bool {
    let segment = |r: Register| matches!(r, Register::FS | Register::GS);
    if i.has_lock_prefix() || segment(i.segment_prefix()) {
        return false;
    }
    let memory = (0..i.op_count()).any(|n| i.op_kind(n) == OpKind::Memory);
    if memory && (i.memory_size().size() > 8 || segment(i.memory_segment())) {
        return false;
    }
    info.info(i).used_registers().iter().all(|u| {
        let r = u.register();
        r.is_gpr()
            || matches!(r, Register::RIP | Register::EIP)
            || (r.is_segment_register() && !segment(r))
    })
}

/// Tells whether the replay can check a scalar-float instruction: a move,
/// an arithmetic operation, a compare or a conversion on the low lane of
/// an `xmm` register.
///
/// Every such instruction is one the emulator models and the lifter
/// writes a statement for. Memory stays within a word and off `fs`/`gs`,
/// and no register but a general one, an `xmm` one, or the `ymm`/`zmm` name
/// a VEX or EVEX scalar uses when it clears the bits above the xmm, is
/// touched, so a packed form, whose lanes the text does not model one by
/// one, is left out. A three-operand `vmovss` or `vmovsd` is in: the low
/// lane comes from the last source and the bits above it from the first.
/// `cvtss2si` and `cvtsd2si` are in: nearest, ties to even, then the
/// integer cast. `cmpeqss` and `cmpeqsd` are in: the ordered equality,
/// whose low bit is C's `==`. A fused multiply-add the emulator does not
/// model is left out with the packed forms, and so is any other compare
/// predicate.
///
/// # Arguments
///
/// * `i` - The instruction.
/// * `info` - Register-access facts.
fn scalar_float(i: &Instruction, info: &mut InstructionInfoFactory) -> bool {
    use Mnemonic as M;
    if i.has_lock_prefix() || matches!(i.segment_prefix(), Register::FS | Register::GS) {
        return false;
    }
    let m = i.mnemonic();
    let mask = matches!(m, M::Xorps | M::Xorpd | M::Andps | M::Andpd)
        && i.op_count() == 2
        && i.op0_kind() == OpKind::Register
        && i.op1_kind() == OpKind::Memory;
    if !mask
        && (0..i.op_count()).any(|n| i.op_kind(n) == OpKind::Memory)
        && (i.memory_size().size() > 8 || matches!(i.memory_segment(), Register::FS | Register::GS))
    {
        return false;
    }
    let two = i.op_count() == 2;
    let three = i.op_count() == 3;
    let reg_reg = two && i.op0_kind() == OpKind::Register && i.op1_kind() == OpKind::Register;
    let shape = match m {
        M::Movss | M::Movsd | M::Movd | M::Movq | M::Vmovd | M::Vmovq => two,
        M::Vmovss | M::Vmovsd => two || three,
        M::Movaps | M::Movups | M::Movapd | M::Movupd | M::Movdqa | M::Movdqu => reg_reg,
        M::Xorps | M::Xorpd | M::Andps | M::Andpd => mask,
        M::Addss
        | M::Subss
        | M::Mulss
        | M::Divss
        | M::Minss
        | M::Maxss
        | M::Sqrtss
        | M::Addsd
        | M::Subsd
        | M::Mulsd
        | M::Divsd
        | M::Minsd
        | M::Maxsd
        | M::Sqrtsd => two,
        M::Vaddss
        | M::Vsubss
        | M::Vmulss
        | M::Vdivss
        | M::Vminss
        | M::Vmaxss
        | M::Vsqrtss
        | M::Vaddsd
        | M::Vsubsd
        | M::Vmulsd
        | M::Vdivsd
        | M::Vminsd
        | M::Vmaxsd
        | M::Vsqrtsd
        | M::Vcvtsi2ss
        | M::Vcvtsi2sd
        | M::Vcvtss2sd
        | M::Vcvtsd2ss => three,
        M::Comiss
        | M::Ucomiss
        | M::Comisd
        | M::Ucomisd
        | M::Vcomiss
        | M::Vucomiss
        | M::Vcomisd
        | M::Vucomisd
        | M::Cvtsi2ss
        | M::Cvtsi2sd
        | M::Cvtss2sd
        | M::Cvtsd2ss
        | M::Cvttss2si
        | M::Cvttsd2si
        | M::Vcvttss2si
        | M::Vcvttsd2si
        | M::Cvtss2si
        | M::Cvtsd2si
        | M::Vcvtss2si
        | M::Vcvtsd2si => two,
        M::Cmpss | M::Cmpsd if i.immediate8() & 0x1f < 8 => {
            three && i.op0_kind() == OpKind::Register && i.op0_register().is_vector_register()
        }
        M::Vcmpss | M::Vcmpsd if i.immediate8() & 0x1f < 8 => {
            i.op_count() == 4
                && i.op0_kind() == OpKind::Register
                && i.op0_register().is_vector_register()
        }
        _ => false,
    };
    shape
        && info.info(i).used_registers().iter().all(|u| {
            let r = u.register();
            r.is_gpr()
                || r.is_xmm()
                || r.is_ymm()
                || r.is_zmm()
                || matches!(r, Register::RIP | Register::EIP)
                || (r.is_segment_register() && !matches!(r, Register::FS | Register::GS))
        })
}

/// The instructions of a block that set the flags, each as its address
/// and whether it was a float compare (`comiss` and its kin), beside the
/// addresses of those that read them.
///
/// The lifter writes a float compare's condition as a `Cmp` no differently
/// from an integer one, and its operands may carry no float type (a
/// parameter's variable), so the instructions themselves are the only
/// witness of which way the condition a reader stands at reads: the
/// setter before the reader (`setcc` and `and` both follow a compare,
/// only the first reading its flags).
///
/// # Arguments
///
/// * `code` - The block's instructions.
pub(super) fn flag_setters(code: &[Instruction]) -> (Vec<(u64, bool)>, Vec<u64>) {
    (
        code.iter()
            .filter(|i| i.rflags_modified() != 0)
            .map(|i| {
                (
                    i.ip(),
                    matches!(
                        i.mnemonic(),
                        Mnemonic::Comiss
                            | Mnemonic::Ucomiss
                            | Mnemonic::Comisd
                            | Mnemonic::Ucomisd
                            | Mnemonic::Vcomiss
                            | Mnemonic::Vucomiss
                            | Mnemonic::Vcomisd
                            | Mnemonic::Vucomisd
                    ),
                )
            })
            .collect(),
        code.iter()
            .filter(|i| i.rflags_read() != 0)
            .map(Instruction::ip)
            .collect(),
    )
}

/// Tells whether the replay can check a packed-integer instruction.
///
/// That is a 128-bit vector move to or from memory, a bitwise operation,
/// lane-wise addition and subtraction, a pack, an unpack or a shuffle:
/// each an instruction the emulator runs lane by lane and the lifter
/// writes a statement for, as the operation's own call.
///
/// The forms the two sides do not share stay out, each named: `pshufb`,
/// `palignr` and the VEX arithmetic (`vpaddb` and its kin), which the
/// emulator does not model; the lane compares, byte extremes, masks,
/// inserts, extracts and word shuffles, which both sides model but a
/// later slice admits; the 256-bit and `mmx` forms, whose registers no
/// word of this holds. A shift's count is an immediate, the only form
/// whose statement's argument names the count whole.
///
/// # Arguments
///
/// * `i` - The instruction.
/// * `info` - Register-access facts.
fn packed_integer(i: &Instruction, info: &mut InstructionInfoFactory) -> bool {
    use Mnemonic as M;
    if i.has_lock_prefix() || matches!(i.segment_prefix(), Register::FS | Register::GS) {
        return false;
    }
    let memory = (0..i.op_count()).any(|n| i.op_kind(n) == OpKind::Memory)
        && i.memory_size().size() == 16
        && !matches!(i.memory_segment(), Register::FS | Register::GS)
        && (matches!(
            i.memory_base(),
            Register::None | Register::RIP | Register::EIP
        ) || i.memory_base().is_gpr())
        && (i.memory_index() == Register::None || i.memory_index().is_gpr());
    let dst = i.op0_kind() == OpKind::Register && i.op0_register().is_xmm();
    let src = matches!(i.op1_kind(), OpKind::Register if i.op1_register().is_xmm()) || memory;
    let imm = i.op1_kind() == OpKind::Immediate8;
    let shape = match i.mnemonic() {
        M::Movaps | M::Movups | M::Movapd | M::Movupd | M::Movdqa | M::Movdqu => {
            i.op_count() == 2 && memory
        }
        M::Xorps
        | M::Xorpd
        | M::Andps
        | M::Andpd
        | M::Orps
        | M::Orpd
        | M::Andnps
        | M::Andnpd
        | M::Pxor
        | M::Pand
        | M::Pandn
        | M::Por
        | M::Paddb
        | M::Paddw
        | M::Paddd
        | M::Paddq
        | M::Psubb
        | M::Psubw
        | M::Psubd
        | M::Psubq
        | M::Packssdw
        | M::Packsswb
        | M::Packuswb
        | M::Punpcklbw
        | M::Punpcklwd
        | M::Punpckldq
        | M::Punpcklqdq
        | M::Punpckhbw
        | M::Punpckhwd
        | M::Punpckhdq
        | M::Punpckhqdq => i.op_count() == 2 && dst && src,
        M::Pshufd => {
            i.op_count() == 3
                && dst
                && (matches!(i.op1_kind(), OpKind::Register if i.op1_register().is_xmm()) || memory)
                && i.op2_kind() == OpKind::Immediate8
        }
        M::Psllw
        | M::Pslld
        | M::Psllq
        | M::Psrlw
        | M::Psrld
        | M::Psrlq
        | M::Psraw
        | M::Psrad
        | M::Pslldq
        | M::Psrldq => i.op_count() == 2 && dst && imm,
        _ => false,
    };
    shape
        && info.info(i).used_registers().iter().all(|u| {
            let r = u.register();
            r.is_gpr()
                || r.is_xmm()
                || matches!(r, Register::RIP | Register::EIP)
                || (r.is_segment_register() && !matches!(r, Register::FS | Register::GS))
        })
}

/// Tells whether the replay can check a block.
///
/// Every instruction is in the integer subset ([`integer`]), is a
/// scalar-float one ([`scalar_float`]), is a packed-integer one
/// ([`packed_integer`]), or is the zero fill of a structure, a vector
/// register zeroed (`xorps xmm0, xmm0`) and stored sixteen bytes at a
/// time (`movups [rsp+0x20], xmm0`), whose bytes both sides know.
///
/// # Arguments
///
/// * `code` - The block's instructions.
/// * `info` - Register-access facts.
pub(super) fn integer_or_zero_fill(
    code: &[Instruction],
    info: &mut InstructionInfoFactory,
) -> bool {
    let mut zeroed: Vec<Register> = Vec::new();
    code.iter().all(|i| {
        if integer(i, info) || scalar_float(i, info) {
            return true;
        }
        let regs = i.op_count() == 2 && i.op1_kind() == OpKind::Register;
        match i.mnemonic() {
            Mnemonic::Xorps | Mnemonic::Xorpd | Mnemonic::Pxor
                if regs
                    && i.op0_kind() == OpKind::Register
                    && i.op0_register() == i.op1_register()
                    && i.op0_register().is_xmm() =>
            {
                zeroed.push(i.op0_register());
                true
            }
            Mnemonic::Movups
            | Mnemonic::Movaps
            | Mnemonic::Movupd
            | Mnemonic::Movapd
            | Mnemonic::Movdqu
            | Mnemonic::Movdqa
                if regs
                    && i.op0_kind() == OpKind::Memory
                    && i.memory_size().size() == 16
                    && zeroed.contains(&i.op1_register())
                    && !matches!(i.memory_segment(), Register::FS | Register::GS)
                    && i.memory_base().is_gpr()
                    && (i.memory_index() == Register::None || i.memory_index().is_gpr()) =>
            {
                true
            }
            _ => packed_integer(i, info),
        }
    })
}

/// Why a block outside the checked subset ([`integer_or_zero_fill`]) is not
/// checked, by its first instruction outside it.
///
/// A memory access through `fs` or `gs` reads the thread block (the
/// exception chain, the stack bounds, thread-local storage), which is no
/// float; an instruction naming a floating-point or vector register, or an
/// x87 one, is the float/vector form the replay leaves alone; anything
/// else is an instruction no model covers.
///
/// # Arguments
///
/// * `code` - The block's instructions.
/// * `info` - Register-access facts.
pub(super) fn outside_subset(
    code: &[Instruction],
    info: &mut InstructionInfoFactory,
) -> &'static str {
    let Some(i) = code
        .iter()
        .find(|i| !(integer(i, info) || scalar_float(i, info) || packed_integer(i, info)))
    else {
        return OUTSIDE_FLOAT;
    };
    let memory = (0..i.op_count()).any(|n| i.op_kind(n) == OpKind::Memory);
    if memory && matches!(i.memory_segment(), Register::FS | Register::GS) {
        return "a read or write through the thread block";
    }
    let float = format!("{:?}", i.mnemonic()).starts_with('F')
        || info.info(i).used_registers().iter().any(|u| {
            let r = u.register();
            r.is_vector_register() || r.is_st() || r.is_mm() || r.is_k()
        });
    if float {
        OUTSIDE_FLOAT
    } else {
        "an instruction outside every checked form"
    }
}

/// Tells whether a block reads whole vector lanes: any of its instructions
/// is a packed-integer one ([`packed_integer`]), whose statements carry the
/// full 128 bits the machine's own registers hold.
///
/// # Arguments
///
/// * `code` - The block's instructions.
/// * `info` - Register-access facts.
pub(super) fn reads_whole_lanes(code: &[Instruction], info: &mut InstructionInfoFactory) -> bool {
    code.iter().any(|i| packed_integer(i, info))
}
