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
//!   `segment`, `is_ip_rel_memory_operand`;
//! * branch resolution: `near_branch64` and the `NearBranchNN` operand kinds
//!   it pairs with;
//! * prefixes: `has_lock_prefix`, `has_rep_prefix`, `has_repe_prefix`,
//!   `has_repne_prefix`;
//! * flags: `rflags_modified` against [`RflagsBits`] (CF/ZF/SF/OF/PF/DF) in
//!   the lifter's flag-elision logic;
//! * encoding facts: [`InstructionInfoFactory`] with [`OpAccess`] (which
//!   operands and registers an instruction reads and writes) and
//!   `constant_offsets` ([`ConstantOffsets`]: where the displacement and
//!   immediate sit inside the encoding) for in-place byte patching;
//! * text: [`NasmFormatter`] through the [`Formatter`] trait renders one
//!   instruction as NASM syntax ([`crate::disasm`] owns the `(bad)` and
//!   paging rules around it);
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
//!   have made in the lifter's call analysis.
//!
//! The engine never encodes bytes: patching rewrites existing encodings in
//! place through `constant_offsets`, and the synthetic instructions above
//! exist to be classified, not emitted.

mod regbank;

pub use iced_x86::{
    Code, ConditionCode, ConstantOffsets, Decoder, DecoderOptions, FlowControl, Formatter,
    Instruction, InstructionInfoFactory, MemorySize, Mnemonic, NasmFormatter, OpAccess, OpKind,
    Register, RflagsBits,
};
pub(crate) use regbank::{
    as_xmm, gpr_bank_index, sized_register, st_depth, st_depth_mod8, st_register, xmm_slot,
};
