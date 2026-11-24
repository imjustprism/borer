//! What a call site passes: the constants its straight-line setup puts in
//! the argument registers, the registers it sign-extends a value into,
//! and the class registrations it makes.

use super::walk::Called;
use super::*;
use crate::isa::x86::{InstructionInfoFactory, OpAccess};

/// Longest run of instructions searched back from a call for its arguments.
const ARG_SETUP_MAX: usize = 32;

/// The straight-line instructions leading into `call_va`, in address order.
///
/// At most [`ARG_SETUP_MAX`] of them, walked back through the records as
/// long as each has exactly one predecessor that falls through and nothing
/// else reaches it ([`Recorded::enters`]): where a branch, a jump table, a
/// handler or the caller comes in, the line starts, since the instructions
/// before it do not run on that way in.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `bitness` - Decode width.
/// * `call_va` - The call instruction's address.
/// * `recorded` - What the instructions walked so far say, for the
///   backward chain.
pub(super) fn straight_line_before(
    program: &Program,
    bitness: u32,
    call_va: u64,
    recorded: &Recorded,
) -> Vec<Instruction> {
    let mut window: Vec<Instruction> = Vec::new();
    let mut cur = call_va;
    while window.len() < ARG_SETUP_MAX && !recorded.enters(cur) {
        let Some(prev) = recorded.only_before(cur) else {
            break;
        };
        let Some(i) = decode_at(program, bitness, prev) else {
            break;
        };
        if i.flow_control() != FlowControl::Next {
            break;
        }
        window.push(i);
        cur = prev;
    }
    window.reverse();
    window
}

/// Reads the constants a call site puts in the argument registers, and
/// how it last wrote each of them ([`Ext`]).
///
/// Walks back from the call over at most [`ARG_SETUP_MAX`] instructions,
/// keeping for each argument register the last constant written to it and
/// forgetting the register when anything else writes it. `xor r, r` counts
/// as zero, which is how a compiler writes it.
///
/// # Arguments
///
/// * `program` - The loaded image, for the calling convention.
/// * `bitness` - Decode width.
/// * `call_va` - The call instruction's address.
/// * `callee` - The call's target.
/// * `recorded` - What the instructions walked so far say, for the
///   backward chain.
///
/// # Returns
///
/// One constant per argument register holding one the call did not
/// overwrite, and how the call last wrote its argument registers, `None`
/// when the window shows no such write but constants.
pub(super) fn call_arg_consts(
    program: &Program,
    bitness: u32,
    call_va: u64,
    callee: u64,
    recorded: &Recorded,
) -> (Vec<ArgConst>, Option<ArgExt>) {
    let args = crate::analysis::decompile::abi::conv(program, bitness).args;
    let window = straight_line_before(program, bitness, call_va, recorded);
    let mut held: BTreeMap<Register, Option<u64>> = BTreeMap::new();
    let mut exts: [Option<Ext>; ARG_SLOTS] = [None; ARG_SLOTS];
    let mut note = |r: Register, e: Option<Ext>| {
        if let Some(at) = args
            .iter()
            .position(|a| *a == r)
            .and_then(|k| exts.get_mut(k))
        {
            *at = e;
        }
    };
    let mut factory: Option<InstructionInfoFactory> = None;
    for i in &window {
        match writes_only_op0(i) {
            Some(writes) => {
                let r = i.op0_register().full_register();
                if writes && i.op0_kind() == OpKind::Register && args.contains(&r) {
                    note(r, arg_ext(i, r));
                }
            }
            None => {
                let info = factory
                    .get_or_insert_with(InstructionInfoFactory::new)
                    .info(i);
                for ur in info.used_registers() {
                    let r = ur.register().full_register();
                    if args.contains(&r)
                        && matches!(
                            ur.access(),
                            OpAccess::Write
                                | OpAccess::ReadWrite
                                | OpAccess::CondWrite
                                | OpAccess::ReadCondWrite
                        )
                    {
                        note(r, arg_ext(i, r));
                    }
                }
            }
        }
        if i.op0_kind() != OpKind::Register {
            continue;
        }
        let r = i.op0_register().full_register();
        if !args.contains(&r) {
            continue;
        }
        let value = match i.mnemonic() {
            Mnemonic::Mov if i.op1_kind() != OpKind::Register && i.op1_kind() != OpKind::Memory => {
                Some(i.immediate(1))
            }
            Mnemonic::Xor
                if i.op1_kind() == OpKind::Register && i.op1_register().full_register() == r =>
            {
                Some(0)
            }
            _ => None,
        };
        held.insert(r, value);
    }
    let slot = |r: Register| u8::try_from(args.iter().position(|a| *a == r)?).ok();
    let consts = held
        .into_iter()
        .filter_map(|(r, v)| {
            Some(ArgConst {
                callee,
                slot: slot(r)?,
                value: v?,
            })
        })
        .collect();
    let mask = |want: Ext| {
        exts.iter()
            .enumerate()
            .filter(|(_, e)| **e == Some(want))
            .fold(0u8, |m, (k, _)| m | 1 << k)
    };
    let (widened, other) = (mask(Ext::Widened), mask(Ext::Other));
    let ext = (widened | other != 0).then_some(ArgExt {
        callee,
        widened,
        other,
    });
    (consts, ext)
}

/// Most argument registers a convention passes in, a bit per slot in an
/// [`ArgExt`] mask.
const ARG_SLOTS: usize = 8;

/// How a call site's setup last wrote an argument register.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum Ext {
    /// Sign-extended a narrower value into the whole 64-bit register
    /// (`movsxd rsi, eax`, `movsx rsi, al`): the callee's formal is wider
    /// than the value, since a 32-bit formal needs no extension.
    Widened,
    /// Any other write but a constant: a narrower value (`mov esi, eax`,
    /// `movsx esi, al`), one an instruction writes without naming the
    /// register as its destination (`xchg eax, esi`, `cdq` into `rdx`), or
    /// a whole register whose width says nothing (`mov rsi, rax`).
    Other,
}

/// How one call sets its argument registers ([`Ext`]), a bit per slot
/// (the parameter's index among the argument registers).
pub(super) struct ArgExt {
    /// The callee.
    pub(super) callee: u64,
    /// The slots the call last wrote by a sign extension ([`Ext::Widened`]).
    pub(super) widened: u8,
    /// The slots it last wrote any other way but a constant ([`Ext::Other`]).
    pub(super) other: u8,
}

/// Tells whether `i` is a common instruction that writes no general
/// register but its first operand, and whether it writes that one.
///
/// `mov`, `lea`, the arithmetic and logic of two operands, the extensions,
/// the shifts, `inc`, `dec`, `neg`, `not`, `pop` and a two- or
/// three-operand `imul` write their first operand and no other general
/// register (`pop` also moves `rsp`, which is no argument register); `cmp`,
/// `test`, `push` and `nop` write none. Any other instruction may write a
/// register it does not name first (`xchg eax, esi`, `cdq` into `rdx`),
/// so the call site asks the decoder's register facts of it instead.
///
/// # Arguments
///
/// * `i` - The instruction.
///
/// # Returns
///
/// `Some(true)` when it writes only its first operand, `Some(false)` when
/// it writes no register, `None` for any other instruction.
fn writes_only_op0(i: &Instruction) -> Option<bool> {
    match i.mnemonic() {
        Mnemonic::Cmp | Mnemonic::Test | Mnemonic::Push | Mnemonic::Nop => Some(false),
        Mnemonic::Mov
        | Mnemonic::Lea
        | Mnemonic::Add
        | Mnemonic::Sub
        | Mnemonic::And
        | Mnemonic::Or
        | Mnemonic::Xor
        | Mnemonic::Movzx
        | Mnemonic::Movsx
        | Mnemonic::Movsxd
        | Mnemonic::Shl
        | Mnemonic::Shr
        | Mnemonic::Sar
        | Mnemonic::Inc
        | Mnemonic::Dec
        | Mnemonic::Neg
        | Mnemonic::Not
        | Mnemonic::Pop => Some(true),
        Mnemonic::Imul if i.op_count() >= 2 => Some(true),
        _ => None,
    }
}

/// Returns how `i`, which writes argument register `r`, sets it.
///
/// A sign extension into the whole register as the destination widens.
/// A constant (`mov esi, 5`) or a zeroing `xor` says nothing, since
/// compilers write those at 32 bits for a 64-bit formal too. Every other
/// write is [`Ext::Other`], which vetoes a widening at another call.
///
/// # Arguments
///
/// * `i` - The instruction.
/// * `r` - The argument register, as its full register.
fn arg_ext(i: &Instruction, r: Register) -> Option<Ext> {
    if i.op0_kind() != OpKind::Register || i.op0_register().full_register() != r {
        return Some(Ext::Other);
    }
    match i.mnemonic() {
        Mnemonic::Movsxd | Mnemonic::Movsx if i.op0_register().size() == 8 => Some(Ext::Widened),
        Mnemonic::Mov if !matches!(i.op1_kind(), OpKind::Register | OpKind::Memory) => None,
        Mnemonic::Xor
            if i.op1_kind() == OpKind::Register && i.op1_register().full_register() == r =>
        {
            None
        }
        _ => Some(Ext::Other),
    }
}

/// Returns, per callee, the argument slots some call sign-extends a value
/// into and no call writes any other way but a constant ([`Ext`]).
///
/// A caller widening an `int` into the register shows the formal is 64
/// bits; a caller writing the slot any other way leaves it undecided, and
/// the slot is left out. A call whose setup the window does not show
/// writing the register says nothing.
///
/// # Arguments
///
/// * `calls` - Per function, what its last walk read off its calls.
pub(super) fn widened_args(calls: &BTreeMap<u64, Called>) -> BTreeMap<u64, BTreeSet<u8>> {
    let mut seen: BTreeMap<u64, (u8, u8)> = BTreeMap::new();
    for a in calls.values().flat_map(|c| &c.exts) {
        let (widened, other) = seen.entry(a.callee).or_default();
        *widened |= a.widened;
        *other |= a.other;
    }
    seen.into_iter()
        .map(|(callee, (widened, other))| {
            let wide = widened & !other;
            (callee, (0..8u8).filter(|k| wide >> k & 1 == 1).collect())
        })
        .filter(|(_, slots): &(u64, BTreeSet<u8>)| !slots.is_empty())
        .collect()
}

/// Reads a class registration from a call site.
///
/// A registrar is handed the class's name and the four-character code that
/// identifies it on the wire, and the code is what a message's format is
/// useless without: with it, `Type::Move` is `MOVE`
/// and its encoder's `1 bit, 32 bits` is a packet a reader can find. The
/// second argument must be a readable name and the third a constant whose
/// four bytes are all printable.
///
/// # Arguments
///
/// * `program` - The loaded image, for reading the name.
/// * `bitness` - Decode width.
/// * `call_va` - The call instruction's address.
/// * `recorded` - What the instructions walked so far say, for the
///   backward chain.
///
/// # Returns
///
/// The class name and its code.
pub(super) fn class_registration(
    program: &Program,
    bitness: u32,
    call_va: u64,
    recorded: &Recorded,
) -> Option<Registration> {
    let args = crate::analysis::decompile::abi::conv(program, bitness).args;
    let (name_reg, code_reg) = (*args.get(1)?, *args.get(2)?);
    let window = straight_line_before(program, bitness, call_va, recorded);
    let (mut name_at, mut code) = (None, None);
    for i in &window {
        if i.op0_kind() != OpKind::Register {
            continue;
        }
        let r = i.op0_register().full_register();
        if r == name_reg && i.mnemonic() == Mnemonic::Lea && i.memory_base() == Register::RIP {
            name_at = Some(i.memory_displacement64());
        } else if r == code_reg
            && i.mnemonic() == Mnemonic::Mov
            && i.op_count() > 1
            && !matches!(i.op1_kind(), OpKind::Register | OpKind::Memory)
        {
            code = u32::try_from(i.immediate(1)).ok();
        }
    }
    let code = code.filter(|c| c.to_be_bytes().iter().all(|b| (0x20..0x7f).contains(b)))?;
    let (_, name) = crate::strings::cstr_at(program, name_at?, 3, CLASS_NAME_MAX)?;
    name.chars()
        .all(|c| c.is_ascii_alphanumeric() || "_:<>, ".contains(c))
        .then_some(Registration { class: name, code })
}

/// Longest class name read from a registration.
const CLASS_NAME_MAX: usize = 96;
