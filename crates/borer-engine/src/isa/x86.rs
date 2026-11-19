//! The x86 and x86-64 instruction-set surface the engine consumes.
//!
//! Everything downstream of x86 decoding (the lifter, the emulator,
//! function discovery, rendering) imports these names from here instead of
//! from `iced_x86`, so this module and [`regbank`] are the only places that
//! name the decoder crate. The module is a thin re-export of iced-x86 plus
//! the `regbank` accessors, the one piece of engine-owned mapping.
//!
//! # Inventory: what the engine consumes from the decoder
//!
//! The surface below is the whole contract between the engine and iced; an
//! item not listed here is not read.
//!
//! * decoding: [`Decoder::with_ip`] over a byte window at a known address
//!   and bitness, driven by `can_decode`, `decode_out` and `position` (or
//!   the `Iterator` impl); [`DecoderOptions`] is the knob set, and the
//!   engine passes `NONE` everywhere;
//! * extent: `ip`, `next_ip` and `len` of one decoded instruction, plus the
//!   `set_ip`/`set_len`/`set_next_ip` mutators the lifter uses on synthetic
//!   instructions;
//! * classification: `mnemonic` ([`Mnemonic`]), `code` against the
//!   `Code::INVALID` sentinel for undecodable bytes, `condition_code`
//!   ([`ConditionCode`]) for `jcc`/`cc`, and `flow_control` ([`FlowControl`])
//!   for next/branch/call/return/interrupt;
//! * operand kinds: `op_count`, `op_kind(n)` and the `opN_kind` shortcuts,
//!   `op_register(n)`; [`OpKind`] says register vs memory vs immediate vs
//!   branch distance vs constant;
//! * memory decomposition: `memory_base`, `memory_index`, `memory_size`
//!   ([`MemorySize`]), `memory_displacement64`/`32`, `memory_displ_size`,
//!   `segment`, `segment_prefix`, `is_ip_rel_memory_operand`,
//!   `ip_rel_memory_address`;
//! * branch resolution: `near_branch64`, `near_branch_target` and the
//!   `NearBranchNN` operand kinds they pair with;
//! * prefixes: `has_lock_prefix`, `has_rep_prefix`, `has_repe_prefix`,
//!   `has_repne_prefix`;
//! * flags: `rflags_modified` against [`RflagsBits`] (CF/ZF/SF/OF/PF/DF) in
//!   the lifter's flag-elision logic;
//! * encoding facts: [`InstructionInfoFactory`] with [`OpAccess`] (which
//!   operands and registers an instruction reads and writes) and
//!   `constant_offsets` ([`ConstantOffsets`]: where the displacement and
//!   immediate sit inside the encoding) for in-place byte patching;
//! * text: [`NasmFormatter`] through the [`Formatter`] trait renders one
//!   instruction as NASM syntax into a `String` or a [`FormatterOutput`]
//!   adapter ([`FormatterTextKind`], [`NumberKind`], [`PrefixKind`];
//!   [`crate::disasm`] owns the `(bad)` and paging rules around it);
//! * register identity: [`Register`] is compared against variants (`RAX`,
//!   `RSP`, `XMM0`, `ST0`, `RIP`, `None`), widened by `full_register` and
//!   `full_register32`, sized by `size`, and grouped by `is_gpr`/`is_xmm`/
//!   `is_ymm`/`is_zmm`; the `number` arithmetic that maps a register to a
//!   bank slot or a width view is not done by consumers but by the
//!   `regbank` accessors (`gpr_bank_index`, `st_register`). That numbering
//!   mapping is the deepest x86 assumption in the engine and the one item a
//!   second architecture will have to replace rather than re-implement;
//! * synthesis: `Instruction::default` as the `decode_out` target, and
//!   `Instruction::with_branch`/`with1` building the call a thunk would
//!   have made in the lifter's call analysis;
//! * encoding: [`BlockEncoder`] over an [`InstructionBlock`], with
//!   [`BlockEncoderOptions`], is how [`crate::patch`] re-encodes a run of
//!   instructions at a new address and fixes its relative branches and
//!   RIP-relative operands up. It is the one place the engine emits bytes;
//!   everywhere else `constant_offsets` rewrites an existing encoding in
//!   place and the synthetic instructions above exist to be classified.

mod regbank;

pub use iced_x86::{
    BlockEncoder, BlockEncoderOptions, Code, ConditionCode, ConstantOffsets, Decoder,
    DecoderOptions, FlowControl, Formatter, FormatterOutput, FormatterTextKind, Instruction,
    InstructionBlock, InstructionInfoFactory, MemorySize, Mnemonic, NasmFormatter, NumberKind,
    OpAccess, OpKind, PrefixKind, Register, RflagsBits,
};
pub(crate) use regbank::{
    as_xmm, gpr_bank_index, sized_register, st_depth, st_depth_mod8, st_register, xmm_slot,
};

/// Hands `f` each constant an x86 instruction's operands state.
///
/// An immediate comes at the width the operand reads it (one the encoding
/// sign-extends at the operand's width), a memory operand's displacement
/// at the address width (a RIP-relative one as the address it reaches); a
/// branch target is no constant.
///
/// # Arguments
///
/// * `i` - The instruction.
/// * `bits` - The decoder's bitness: the width of an address without an
///   address-size prefix.
/// * `f` - Called with each constant, in operand order.
pub(crate) fn constants(i: &Instruction, bits: u32, mut f: impl FnMut(super::Constant)) {
    for n in 0..i.op_count() {
        let operand = usize::try_from(n).unwrap_or(usize::MAX);
        let width = match i.op_kind(n) {
            OpKind::Immediate8 | OpKind::Immediate8_2nd => 8,
            OpKind::Immediate16 | OpKind::Immediate8to16 => 16,
            OpKind::Immediate32 | OpKind::Immediate8to32 => 32,
            OpKind::Immediate64 | OpKind::Immediate8to64 | OpKind::Immediate32to64 => 64,
            OpKind::Memory => {
                if i.memory_displ_size() > 0 {
                    let part = if i.is_ip_rel_memory_operand() {
                        super::Part::Address
                    } else {
                        super::Part::Displacement
                    };
                    f(super::Constant::new(
                        operand,
                        part,
                        i.memory_displacement64(),
                        address_bits(i, bits),
                    ));
                }
                continue;
            }
            _ => continue,
        };
        f(super::Constant::new(
            operand,
            super::Part::Immediate,
            i.immediate(n),
            width,
        ));
    }
}

/// Returns the width in bits of a memory operand's address: its base's or
/// index's width (an address-size prefix makes them 32-bit in 64-bit
/// code), `bits` for an absolute or RIP-relative one.
///
/// # Arguments
///
/// * `i` - The instruction, with a memory operand.
/// * `bits` - The decoder's bitness.
fn address_bits(i: &Instruction, bits: u32) -> u32 {
    [i.memory_base(), i.memory_index()]
        .into_iter()
        .find(|r| *r != Register::None)
        .map_or(bits, |r| match r {
            Register::RIP => 64,
            Register::EIP => 32,
            r => u32::try_from(r.size()).map_or(bits, |n| n * 8),
        })
}
