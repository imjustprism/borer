//! What a call site passes: the constants its straight-line setup puts in
//! the argument registers, and the class registrations it makes.

use super::*;

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

/// Reads the constants a call site puts in the argument registers.
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
/// overwrite.
pub(super) fn call_arg_consts(
    program: &Program,
    bitness: u32,
    call_va: u64,
    callee: u64,
    recorded: &Recorded,
) -> Vec<ArgConst> {
    let args = crate::analysis::decompile::abi::conv(program, bitness).args;
    let window = straight_line_before(program, bitness, call_va, recorded);
    let mut held: BTreeMap<Register, Option<u64>> = BTreeMap::new();
    for i in &window {
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
    held.into_iter()
        .filter_map(|(r, v)| {
            let slot = u8::try_from(args.iter().position(|a| *a == r)?).ok()?;
            Some(ArgConst {
                callee,
                slot,
                value: v?,
            })
        })
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
