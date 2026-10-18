//! Jump-table recovery: the bounded index, the table's base and stride, and
//! the case targets an indirect jump reads.

use std::collections::BTreeMap;

use super::{InstrRec, Recorded, decode_at};
use crate::analysis::switch_index::{
    TableBound, check_bound, flag_reader, index_bound, table_index,
};
use crate::analysis::{read_u32, read_u64};
use crate::fxmap::FxHashSet;
use crate::isa::x86::{Code, Instruction, Mnemonic, OpKind, Register};
use crate::num::from_usize;
use crate::program::Program;

/// Largest jump table accepted (bound immediate).
pub(crate) const TABLE_ENTRIES_MAX: u64 = 4096;

/// Farthest a case may lie from its jump in a table sized loosely.
///
/// A mask, or a check the index may not be tied to, only bounds the index,
/// so the table can end before it does, and the data after it reads as
/// offsets to anywhere: in one Rust binary, the entries past a ten-case
/// table's end pointed 7 MB away, into the middle of other functions'
/// instructions.
const LOOSE_REACH: u64 = 0x10_0000;
/// Most entries read from a table no check bounds, the cases an index
/// fetched as a byte can select.
const UNBOUNDED_ENTRIES_MAX: usize = 256;
/// Fewest cases a table no check bounds must yield to be taken as one.
const UNBOUNDED_ENTRIES_MIN: usize = 2;
/// Most instructions decoded after a jump through a table no check bounds,
/// looking for the code that names the table after it.
const NEXT_TABLE_SCAN: usize = 256;

/// A jump table one indirect jump reads, resolved.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct ResolvedTable {
    /// The jump's address.
    pub(super) site: u64,
    /// The case targets in table order.
    pub(super) targets: Vec<u64>,
}

/// What a jump table read produced.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct TableRead {
    /// The case targets in table order.
    pub(super) targets: Vec<u64>,
    /// The byte index table that picked them, when one did.
    pub(super) picker: Option<u64>,
}

/// Recovers the instructions immediately before `va`.
///
/// x86 has no reliable backward decode, so every start within 64 bytes is
/// tried and the longest chain that ends exactly on `va` wins.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `bitness` - Decoder bitness.
/// * `va` - The address the chain must end at.
/// * `want` - Chain length that stops the search early.
///
/// # Returns
///
/// The chain in address order, or `None` when no start decodes onto `va`.
fn prev_instructions(
    program: &Program,
    bitness: u32,
    va: u64,
    want: usize,
) -> Option<Vec<Instruction>> {
    /// How far back a chain may start, in bytes.
    const MAX_BACK: u64 = 64;
    let mut best: Option<Vec<Instruction>> = None;
    for back in 1..=MAX_BACK.min(va) {
        let start = va - back;
        if !crate::analysis::is_executable_va(program, start) {
            continue;
        }
        let mut chain = Vec::new();
        let mut cur = start;
        while cur < va {
            let Some(instr) = decode_at(program, bitness, cur) else {
                break;
            };
            if instr.code() == Code::INVALID {
                break;
            }
            cur = instr.next_ip();
            chain.push(instr);
        }
        if cur == va && !chain.is_empty() {
            if chain.len() >= want {
                return Some(chain);
            }
            if chain.len() > best.as_ref().map_or(0, Vec::len) {
                best = Some(chain);
            }
        }
    }
    best
}

/// Resolves the bounded jump table feeding the indirect jump at `jmp_va`.
///
/// The preceding instructions come from the walk's own decode chain, falling
/// back to [`prev_instructions`] when the chain is shorter than three. The
/// bound is the range check of the table's index ([`index_bound`]) or, when
/// no load names an index, the nearest check before the jump
/// ([`check_bound`]); a table sized loosely ends at its first case farther
/// than [`LOOSE_REACH`] from the jump, or at the first that `within` refuses
/// (the walk passes the function's entry and the next known function start:
/// an index that came from a byte reads up to 256 entries, and the entries
/// past a six-case table's end are the next table's, which land in the next
/// function). The table base is the nearest `lea
/// reg, [rip+X]` or `mov reg, imm` after that compare that lands in a
/// section. Every target must decode as an instruction inside the jump's
/// own section.
///
/// Three shapes are tried before that. The jump's own memory operand may
/// name the table (`jmp qword [rax * 8 + T]`, what GCC emits). A load
/// through a `lea`-filled register may name it (`lea rdx, [rip + B]; mov
/// ecx, [rdx + rax * 4 + D]`, what MSVC emits, where the entries are
/// offsets from `B`), and a byte table read the same way
/// (`movzx eax, byte [rdx + rcx + D2]`) selects among those targets when
/// several cases share one.
///
/// When nothing bounds the index, as when an interpreter jumps on an
/// opcode byte it fetched, only a table of offsets read through a `lea`
/// base is tried, and it ends at its first entry that is not code of
/// this function ([`unbounded_table`]).
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `bitness` - Decoder bitness.
/// * `jmp_va` - Address of the indirect jump.
/// * `recorded` - What the walk's records so far say.
/// * `walked` - The walk's records so far, for a table base set before a
///   loop the backward chain cannot leave ([`hoisted_base`]).
/// * `within` - Whether a target of a loosely sized table may be this
///   function's.
///
/// # Returns
///
/// The case targets in table order, with the byte index table that picked
/// them when one did, or `None` when no bound, no base, or an implausible
/// table was found.
pub(super) fn resolve_jump_table(
    program: &Program,
    bitness: u32,
    jmp_va: u64,
    recorded: &Recorded,
    walked: &[(u64, InstrRec)],
    within: &dyn Fn(u64) -> bool,
) -> Option<TableRead> {
    /// Longest backward chain examined for the range check and table base.
    const CHAIN_MAX: usize = 40;
    let mut window: Vec<Instruction> = Vec::new();
    let mut cur = jmp_va;
    while window.len() < CHAIN_MAX {
        let Some(prev) = recorded.pred_of(cur) else {
            break;
        };
        let Some(i) = decode_at(program, bitness, prev) else {
            break;
        };
        window.push(i);
        cur = prev;
    }
    window.reverse();
    if window.len() < 3 {
        window = prev_instructions(program, bitness, jmp_va, 6)?;
    }
    if let Some(lea) = hoisted_base(program, bitness, jmp_va, &window, walked) {
        window.insert(0, lea);
    }

    let bound = match table_index(&window, decode_at(program, bitness, jmp_va).as_ref()) {
        Some((at, index)) => index_bound(&window, jmp_va, at, index),
        None => window.iter().enumerate().rev().find_map(|(k, i)| {
            let jcc = flag_reader(&window, k).unwrap_or(k + 1);
            check_bound(i, window.get(jcc)).map(|entries| TableBound {
                check_at: k,
                entries,
                loose: false,
            })
        }),
    };
    let Some(TableBound {
        check_at,
        entries,
        loose,
    }) = bound
    else {
        return unbounded_table(program, bitness, jmp_va, &window, within);
    };
    let mut table = read_jump_table(program, bitness, jmp_va, &window, check_at, entries)?;
    if !loose {
        return Some(table);
    }
    let near = table
        .targets
        .iter()
        .take_while(|t| t.abs_diff(jmp_va) <= LOOSE_REACH && within(**t))
        .count();
    table.targets.truncate(near);
    (near > 0).then_some(table)
}

/// Reads the jump table a bounded index selects from, in whichever form
/// the instructions before the jump name it (see [`resolve_jump_table`]).
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `bitness` - Decoder bitness.
/// * `jmp_va` - Address of the indirect jump.
/// * `window` - The instructions before the jump, in order.
/// * `cmp_at` - Position of the range check in `window`.
/// * `entries` - How many entries it allows.
///
/// # Returns
///
/// The case targets in table order and the byte table that picked them,
/// or `None` when no table reads as plausible.
fn read_jump_table(
    program: &Program,
    bitness: u32,
    jmp_va: u64,
    window: &[Instruction],
    cmp_at: usize,
    entries: u64,
) -> Option<TableRead> {
    let entries = usize::try_from(entries).ok()?;

    if let Some(jmp) = decode_at(program, bitness, jmp_va)
        && jmp.op0_kind() == OpKind::Memory
        && jmp.memory_index() != Register::None
        && matches!(jmp.memory_base(), Register::None)
    {
        let table = jmp.memory_displacement64();
        let picker = window
            .iter()
            .skip(cmp_at)
            .rev()
            .find_map(|i| byte_index_load(program, i, jmp.memory_index()));
        let found = match picker.and_then(|n| index_bytes(program, n, entries).map(|b| (n, b))) {
            Some((picker, indices)) => {
                let count = usize::from(*indices.iter().max().unwrap_or(&0)) + 1;
                table_targets(program, table, count)
                    .map(|t| {
                        indices
                            .iter()
                            .filter_map(|i| t.get(usize::from(*i)).copied())
                            .collect::<Vec<u64>>()
                    })
                    .filter(|t| t.len() == entries)
                    .map(|targets| TableRead {
                        targets,
                        picker: Some(picker),
                    })
            }
            None => table_targets(program, table, entries).map(|targets| TableRead {
                targets,
                picker: None,
            }),
        };
        if found.is_some() {
            return found;
        }
    }

    let lea = lea_bases(window);
    let mut bases = lea.clone();
    if program.is_64 && program.format == crate::program::BinaryFormat::Pe {
        for i in window {
            let base = i.memory_base();
            if i.memory_index() != Register::None
                && base.is_gpr()
                && !matches!(base.full_register(), Register::RSP | Register::RBP)
            {
                bases.entry(base).or_insert(program.image_base);
            }
        }
    }
    let mut wide: Option<(u64, u64)> = None;
    let mut narrow: Option<u64> = None;
    for (k, i) in window.iter().enumerate().skip(cmp_at) {
        match table_load(program, &bases, i) {
            Some((table, base, 4)) => {
                let after = window.get(k + 1..).unwrap_or_default();
                wide = Some((table, added_base(after, i, &lea).unwrap_or(base)));
            }
            Some((table, _, 1)) => narrow = Some(table),
            _ => {}
        }
    }
    if let Some((table, base)) = wide {
        let expanded = match narrow.and_then(|n| index_bytes(program, n, entries)) {
            Some(indices) => {
                let count = usize::from(*indices.iter().max().unwrap_or(&0)) + 1;
                offset_targets(program, table, count, base).map(|t| {
                    indices
                        .iter()
                        .filter_map(|i| t.get(usize::from(*i)).copied())
                        .collect::<Vec<u64>>()
                })
            }
            None => offset_targets(program, table, entries, base),
        };
        if let Some(targets) = expanded.filter(|t| t.len() == entries) {
            return Some(TableRead {
                targets,
                picker: narrow,
            });
        }
    }

    let mut table: Option<u64> = None;
    for i in window.iter().skip(cmp_at).rev() {
        match i.mnemonic() {
            Mnemonic::Lea if i.memory_base() == Register::RIP => {
                let t = i.memory_displacement64();
                if program.section_at(t).is_some() {
                    table = Some(t);
                }
            }
            Mnemonic::Mov => {
                for op in 0..i.op_count() {
                    if matches!(
                        i.op_kind(op),
                        OpKind::Immediate64 | OpKind::Immediate32 | OpKind::Immediate32to64
                    ) {
                        let v = i.immediate(op);
                        if program.section_at(v).is_some() {
                            table = Some(v);
                        }
                    }
                }
            }
            _ => {}
        }
        if table.is_some() {
            break;
        }
    }
    let table = table?;

    let targets = table_targets(program, table, entries)?;
    let jmp_section = program.section_at(jmp_va)?.va.0;
    let plausible = targets.iter().all(|&t| {
        program.section_at(t).is_some_and(|s| s.va.0 == jmp_section)
            && decode_at(program, bitness, t).is_some_and(|i| i.code() != Code::INVALID)
    });
    plausible.then_some(TableRead {
        targets,
        picker: None,
    })
}

/// Reads a table of offsets that no check bounds, entry by entry.
///
/// The last load in `window` must read 32-bit entries through a register
/// a `lea` filled and the jump must go where it, plus the base added back
/// ([`added_base`]), points. Entries are read until one lands outside the
/// jump's section, off code, past what `within` allows, farther than
/// [`LOOSE_REACH`] or on bytes that do not decode, and at most
/// [`UNBOUNDED_ENTRIES_MAX`] of them: the table's end is where its
/// entries stop being this function's code. A slot past the first that
/// the window or the code after the jump names ([`rip_targets_after`])
/// starts another table and ends this one.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `bitness` - Decoder bitness.
/// * `jmp_va` - Address of the indirect jump.
/// * `window` - The instructions before the jump, in order.
/// * `within` - Whether a target may be this function's.
///
/// # Returns
///
/// The case targets in table order, or `None` when no such load feeds the
/// jump or fewer than [`UNBOUNDED_ENTRIES_MIN`] entries are code.
fn unbounded_table(
    program: &Program,
    bitness: u32,
    jmp_va: u64,
    window: &[Instruction],
    within: &dyn Fn(u64) -> bool,
) -> Option<TableRead> {
    let jmp = decode_at(program, bitness, jmp_va)?;
    if jmp.op0_kind() != OpKind::Register {
        return None;
    }
    let lea = lea_bases(window);
    let (k, load, (table, base, scale)) = window
        .iter()
        .enumerate()
        .rev()
        .find_map(|(k, i)| table_load(program, &lea, i).map(|t| (k, i, t)))?;
    if scale != 4 || load.op0_register().full_register() != jmp.op0_register().full_register() {
        return None;
    }
    let base = added_base(window.get(k + 1..).unwrap_or_default(), load, &lea).unwrap_or(base);
    let section = program.section_at(jmp_va)?.va.0;
    let named = rip_targets_after(program, bitness, &jmp, within);
    let targets: Vec<u64> = (0..UNBOUNDED_ENTRIES_MAX)
        .map_while(|i| {
            let slot = table.checked_add(from_usize(i).checked_mul(4)?)?;
            if i > 0 && (named.contains(&slot) || lea.values().any(|v| *v == slot)) {
                return None;
            }
            let t = base.wrapping_add_signed(i64::from(read_u32(program, slot)?.cast_signed()));
            (program.section_at(t).is_some_and(|s| s.va.0 == section)
                && crate::analysis::is_executable_va(program, t)
                && t.abs_diff(jmp_va) <= LOOSE_REACH
                && within(t)
                && decode_at(program, bitness, t).is_some_and(|d| d.code() != Code::INVALID))
            .then_some(t)
        })
        .collect();
    (targets.len() >= UNBOUNDED_ENTRIES_MIN).then_some(TableRead {
        targets,
        picker: None,
    })
}

/// The addresses the code after `jmp` names through `rip`, up to
/// [`NEXT_TABLE_SCAN`] instructions on while `within` holds.
///
/// Tables of offsets often lie end to end, and the entries past one table's
/// end are the next table's, which read from the first base can land on
/// code. The next table's own dispatch names its start, so a slot named
/// here is where the table before it ends.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `bitness` - Decoder bitness.
/// * `jmp` - The jump through the table.
/// * `within` - Whether an address may be this function's.
///
/// # Returns
///
/// The named addresses.
fn rip_targets_after(
    program: &Program,
    bitness: u32,
    jmp: &Instruction,
    within: &dyn Fn(u64) -> bool,
) -> FxHashSet<u64> {
    let mut named = FxHashSet::default();
    let mut at = jmp.next_ip();
    for _ in 0..NEXT_TABLE_SCAN {
        if !within(at) {
            break;
        }
        let Some(i) = decode_at(program, bitness, at).filter(|i| i.code() != Code::INVALID) else {
            break;
        };
        if i.is_ip_rel_memory_operand() {
            named.insert(i.ip_rel_memory_address());
        }
        at = i.next_ip();
    }
    named
}

/// The `lea reg, [rip + X]` that filled a table load's base register
/// before the backward chain's reach.
///
/// A compiler hoists the table's address out of the loop around a switch
/// (sqlite's `strftime` formats in a loop: `lea r14, [T]` before it,
/// `movsxd rax, [r14 + rax * 4]; add rax, r14; jmp rax` inside), and a
/// chain that follows one predecessor per instruction circles the loop
/// without reaching the `lea`. The walk has decoded it, since every path
/// to the dispatch passes it: the walked instruction nearest below the
/// jump that writes the register names the base when it is such a `lea`.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `bitness` - Decoder bitness.
/// * `jmp_va` - Address of the indirect jump.
/// * `window` - The instructions before the jump, in order.
/// * `walked` - The walk's records so far.
///
/// # Returns
///
/// The `lea`, or `None` when the window already fills every base it
/// loads through, or the nearest write is anything else.
fn hoisted_base(
    program: &Program,
    bitness: u32,
    jmp_va: u64,
    window: &[Instruction],
    walked: &[(u64, InstrRec)],
) -> Option<Instruction> {
    /// Most walked instructions decoded looking for the write.
    const DECODES_MAX: usize = 4096;
    let filled = lea_bases(window);
    let mut bases: Vec<Register> = Vec::new();
    for i in window.iter().rev() {
        let base = i.memory_base();
        if matches!(i.mnemonic(), Mnemonic::Mov | Mnemonic::Movsxd)
            && i.memory_index() != Register::None
            && base.is_gpr()
            && !matches!(base.full_register(), Register::RSP | Register::RBP)
            && !filled.contains_key(&base)
            && !bases.contains(&base)
        {
            bases.push(base);
        }
    }
    if bases.is_empty() {
        return None;
    }
    let mut below: Vec<u64> = walked
        .iter()
        .map(|&(va, _)| va)
        .filter(|&va| va < jmp_va)
        .collect();
    below.sort_unstable_by(|l, r| r.cmp(l));
    let decoded: Vec<Instruction> = below
        .into_iter()
        .take(DECODES_MAX)
        .filter_map(|va| decode_at(program, bitness, va))
        .collect();
    bases.into_iter().find_map(|base| {
        let write = decoded.iter().find(|i| {
            i.op_count() > 0
                && i.op0_kind() == OpKind::Register
                && i.op0_register().full_register() == base.full_register()
                && !matches!(
                    i.mnemonic(),
                    Mnemonic::Cmp | Mnemonic::Test | Mnemonic::Push | Mnemonic::Bt
                )
        })?;
        (write.mnemonic() == Mnemonic::Lea
            && write.memory_base() == Register::RIP
            && write.op0_register() == base)
            .then_some(*write)
    })
}

/// The registers a `lea reg, [rip + X]` in `window` filled, with the
/// address each holds.
///
/// # Arguments
///
/// * `window` - The instructions before a jump, in order.
fn lea_bases(window: &[Instruction]) -> BTreeMap<Register, u64> {
    window
        .iter()
        .filter(|i| i.mnemonic() == Mnemonic::Lea && i.memory_base() == Register::RIP)
        .map(|i| (i.op0_register(), i.memory_displacement64()))
        .collect()
}

/// The address added back to what a table load read, when the code adds
/// a `lea`-filled register other than the one the load went through.
///
/// `lea r8, [F]; lea rdx, [T]; movsxd rax, [rdx + rcx * 4]; add rax, r8`
/// holds offsets from `F`, a label other than the table.
///
/// # Arguments
///
/// * `after` - The instructions after the load, before the jump.
/// * `load` - The table load.
/// * `lea` - The `lea`-filled registers ([`lea_bases`]).
///
/// # Returns
///
/// The address in the register added to the load's destination, or `None`
/// when the first such `add` adds no `lea`-filled register.
fn added_base(
    after: &[Instruction],
    load: &Instruction,
    lea: &BTreeMap<Register, u64>,
) -> Option<u64> {
    let dest = load.op0_register().full_register();
    let add = after.iter().find(|i| {
        i.mnemonic() == Mnemonic::Add
            && i.op0_kind() == OpKind::Register
            && i.op0_register().full_register() == dest
    })?;
    if add.op1_kind() != OpKind::Register {
        return None;
    }
    lea.get(&add.op1_register()).copied()
}

/// Reads a table of signed 32-bit offsets added to `base`, the form a
/// compiler uses when the targets are near a register it already holds.
///
/// The entries are sign-extended, as the `movsxd` that reads them does:
/// a rel32 table's targets sit on both sides of its base, and a hand-built
/// interpreter's handlers (reached through `lea r11, [table]; movsxd rcx,
/// [r11+rcx*4]; add rcx, r11; jmp rcx`) are always below the read-only
/// data its program lives in.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `table` - Address of the first entry.
/// * `entries` - Number of entries.
/// * `base` - What each entry is relative to.
///
/// # Returns
///
/// The targets in table order, or `None` when an entry is unreadable or the
/// table does not pass [`accept_table`].
fn offset_targets(program: &Program, table: u64, entries: usize, base: u64) -> Option<Vec<u64>> {
    let targets: Option<Vec<u64>> = (0..entries)
        .map(|i| {
            let slot = table.checked_add(from_usize(i).checked_mul(4)?)?;
            let bytes: [u8; 4] = program.read_va(slot, 4)?.try_into().ok()?;
            Some(base.wrapping_add_signed(i64::from(u32::from_le_bytes(bytes).cast_signed())))
        })
        .collect();
    targets.filter(|t| accept_table(program, t))
}

/// Returns the byte table a load picks the jump table's slot from, when
/// `instr` is that load: `movzx eax, byte [eax + I]` (or `[I + eax]`)
/// feeding `jmp dword [eax*4 + T]`.
///
/// With the byte table in front, the bound counts cases and not slots, so
/// reading that many slots of `T` runs past its end into whatever follows,
/// the byte table included, and its bytes read as addresses.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `instr` - A candidate load.
/// * `index` - The register the jump indexes its table with.
///
/// # Returns
///
/// The byte table's address, or `None` when `instr` is not such a load.
fn byte_index_load(program: &Program, instr: &Instruction, index: Register) -> Option<u64> {
    let fills_index = instr.mnemonic() == Mnemonic::Movzx
        && instr.op0_kind() == OpKind::Register
        && instr.op0_register().full_register() == index.full_register()
        && instr.op1_kind() == OpKind::Memory
        && instr.memory_size().size() == 1;
    let one_register = match (instr.memory_base(), instr.memory_index()) {
        (Register::None, Register::None) => false,
        (_, Register::None) => true,
        (Register::None, _) => instr.memory_index_scale() == 1,
        _ => false,
    };
    let table = instr.memory_displacement64();
    (fills_index && one_register && program.section_at(table).is_some()).then_some(table)
}

/// Reads the byte index table a compiler emits when several cases share a
/// target: entry `i` selects the target-table slot for case `i`.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `table` - Address of the first byte.
/// * `entries` - Number of cases.
///
/// # Returns
///
/// The indices, or `None` when the table is unreadable or selects more
/// targets than a jump table may have.
fn index_bytes(program: &Program, table: u64, entries: usize) -> Option<Vec<u8>> {
    let bytes = program.read_va(table, entries)?.to_vec();
    let max = u64::from(*bytes.iter().max()?);
    (max < TABLE_ENTRIES_MAX).then_some(bytes)
}

/// The address a table load names, given the `lea`-loaded bases in scope.
///
/// A load of the form `mov r, [base + idx * scale + disp]` reads a table at
/// `base + disp` when `base` is a register a `lea reg, [rip + X]` filled;
/// the scale says how wide an entry is.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `bases` - Registers holding an address, from `lea`.
/// * `instr` - The candidate load.
///
/// # Returns
///
/// `(table address, base value, entry scale)`, or `None`.
pub(super) fn table_load(
    program: &Program,
    bases: &BTreeMap<Register, u64>,
    instr: &Instruction,
) -> Option<(u64, u64, u32)> {
    if !matches!(
        instr.mnemonic(),
        Mnemonic::Mov | Mnemonic::Movzx | Mnemonic::Movsxd | Mnemonic::Movsx
    ) {
        return None;
    }
    let base = *bases.get(&instr.memory_base())?;
    if instr.memory_index() == Register::None {
        return None;
    }
    let table = base.checked_add(instr.memory_displacement64())?;
    program.section_at(table)?;
    Some((table, base, instr.memory_index_scale()))
}

/// Reads a jump table's targets, trying each encoding compilers emit.
///
/// In order: absolute qword entries; dword entries relative to the table
/// base (`table + (i32)entry`, LLVM and MSVC); dword entries relative to
/// their own slot (`slot + (i32)entry`); and, for PE images, dword RVAs
/// (`image_base + entry`). The first encoding whose targets pass
/// [`accept_table`] wins.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `table` - Address of the first entry.
/// * `entries` - Number of entries from the range check.
///
/// # Returns
///
/// The targets in table order, or `None` when no encoding reads and validates.
fn table_targets(program: &Program, table: u64, entries: usize) -> Option<Vec<u64>> {
    if !program.is_64 {
        let abs32: Option<Vec<u64>> = (0..entries)
            .map(|i| read_u32(program, table + from_usize(i) * 4).map(u64::from))
            .collect();
        if let Some(t) = abs32
            && accept_table(program, &t)
        {
            return Some(t);
        }
    }
    let abs: Option<Vec<u64>> = (0..entries)
        .map(|i| read_u64(program, table + from_usize(i) * 8))
        .collect();
    if let Some(t) = abs
        && accept_table(program, &t)
    {
        return Some(t);
    }

    let base_rel: Option<Vec<u64>> = (0..entries)
        .map(|i| {
            read_u32(program, table + from_usize(i) * 4)
                .map(|e| table.wrapping_add_signed(i64::from(e.cast_signed())))
        })
        .collect();
    if let Some(t) = base_rel
        && accept_table(program, &t)
    {
        return Some(t);
    }

    let rel: Option<Vec<u64>> = (0..entries)
        .map(|i| {
            let slot = table + from_usize(i) * 4;
            read_u32(program, slot).map(|e| slot.wrapping_add_signed(i64::from(e.cast_signed())))
        })
        .collect();
    if let Some(t) = rel
        && accept_table(program, &t)
    {
        return Some(t);
    }

    if program.image_base != 0 {
        let rva: Option<Vec<u64>> = (0..entries)
            .map(|i| {
                read_u32(program, table + from_usize(i) * 4)
                    .map(|e| program.image_base + u64::from(e))
            })
            .collect();
        if let Some(t) = rva
            && accept_table(program, &t)
        {
            return Some(t);
        }
    }
    None
}

/// Judges whether decoded table targets look like code addresses.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `targets` - Candidate targets; only the first 16 are sampled.
///
/// # Returns
///
/// `true` when at least three quarters of the sample lie in executable memory.
pub(crate) fn accept_table(program: &Program, targets: &[u64]) -> bool {
    let sample = targets.len().min(16);
    if sample == 0 {
        return false;
    }
    let hits = targets
        .iter()
        .take(sample)
        .filter(|&&t| crate::analysis::is_executable_va(program, t))
        .count();
    hits * 4 >= sample * 3
}
