//! The constants each virtual method returns, read slot by slot, and the
//! rows that list them.

use std::collections::BTreeMap;
use std::fmt::Write as _;

use super::{DATA_SLOTS_MAX, SLOT_ROWS_MIN, SLOTS_MAX};
use crate::analysis::{Analysis, is_executable_va, read_word, striped_with};
use crate::isa::x86::{Decoder, DecoderOptions, Instruction, Mnemonic, OpKind, Register};
use crate::program::Program;

/// Reads a vtable's slots.
///
/// Slots are consecutive words pointing into executable memory; the table
/// ends at the first word that is not, or (after the first slot) at a word
/// something references or another class's table starts at. A non-zero
/// word that is not code once the table is under way does not end it when
/// the table visibly resumes after it — the next word is code that nothing
/// else names — and the skipped word is kept as a `0` slot, so the byte
/// offsets of the methods after it stay their slot indexes; a zero is the
/// padding between tables, never a datum, and a first word that is not
/// code ends the table before it starts, because a run of data is no
/// vtable however it continues.
///
/// # Arguments
///
/// * `program` - Bytes and sections.
/// * `analysis` - Cross-references, which mark the next table's start.
/// * `vtables` - Known table starts.
/// * `va` - The table's address.
/// * `bitness` - 32 or 64.
///
/// # Returns
///
/// The slot words, `0` for every word of data read through; empty when the
/// first word is not code.
pub(super) fn read_slots(
    program: &Program,
    analysis: &Analysis,
    vtables: &BTreeMap<u64, String>,
    va: u64,
    bitness: u32,
) -> Vec<u64> {
    let word = u64::from(bitness / 8);
    let mut slots = Vec::new();
    let mut data = 0;
    let mut at = va;
    while slots.len() < SLOTS_MAX {
        let Some(ptr) = read_word(program, at) else {
            break;
        };
        if !is_executable_va(program, ptr) {
            let next = at + word;
            let resumes = data < DATA_SLOTS_MAX
                && ptr != 0
                && !slots.is_empty()
                && !analysis.xrefs.contains_key(&at)
                && !analysis.xrefs.contains_key(&next)
                && !vtables.contains_key(&next)
                && read_word(program, next).is_some_and(|f| is_executable_va(program, f));
            if !resumes {
                break;
            }
            slots.push(0);
            data += 1;
            at = next;
            continue;
        }
        if at != va && (analysis.xrefs.contains_key(&at) || vtables.contains_key(&at)) {
            break;
        }
        slots.push(ptr);
        at += word;
    }
    slots
}

/// One class whose virtual at a slot answers with a constant.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct SlotConstant {
    /// Qualified class name.
    pub class: String,
    /// The function in the slot.
    pub entry: u64,
    /// The constant it returns.
    pub value: u64,
}

/// The constant a function returns when it is nothing but `mov eax, imm; ret`,
/// or `xor eax, eax; ret` for a zero.
///
/// A virtual that answers a class's fixed property compiles to exactly that;
/// anything longer is a computation and is not reported.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `entry` - The function's entry.
/// * `bitness` - Decoder bitness, `32` or `64`.
pub(super) fn returned_constant(program: &Program, entry: u64, bitness: u32) -> Option<u64> {
    /// Longest encoding of the two instructions: `mov rax, imm64` and `ret`.
    const MAX_BYTES: usize = 11;
    let bytes = program
        .read_va(entry, MAX_BYTES)
        .or_else(|| program.read_va(entry, 6))?;
    let mut decoder = Decoder::with_ip(bitness, bytes, entry, DecoderOptions::NONE);
    let mut first = Instruction::default();
    let mut second = Instruction::default();
    decoder.decode_out(&mut first);
    decoder.decode_out(&mut second);
    if first.is_invalid() || second.is_invalid() || second.mnemonic() != Mnemonic::Ret {
        return None;
    }
    let to_rax = first.op0_kind() == OpKind::Register
        && first.op0_register().full_register() == Register::RAX;
    if !to_rax {
        return None;
    }
    match first.mnemonic() {
        Mnemonic::Mov
            if matches!(
                first.op1_kind(),
                OpKind::Immediate8
                    | OpKind::Immediate16
                    | OpKind::Immediate32
                    | OpKind::Immediate64
                    | OpKind::Immediate32to64
            ) =>
        {
            first.try_immediate(1).ok()
        }
        Mnemonic::Xor
            if first.op1_kind() == OpKind::Register
                && first.op1_register() == first.op0_register() =>
        {
            Some(0)
        }
        _ => None,
    }
}

/// Every recovered class whose virtual at `slot` returns a constant, with it.
///
/// A registry that maps an id to a class at start-up (the wire id a command
/// answers through one virtual, the type tag a message answers) is a table
/// no static read of the registry recovers cheaply, while the class itself
/// keeps the answer in the one virtual that returns a literal. Read across
/// every recovered class, that slot is the registry's table.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Discovery results with the recovered classes.
/// * `slot` - The vtable index, zero-based.
///
/// # Returns
///
/// The classes in name order; empty when no class has such a virtual, or on
/// an architecture the decoder does not cover.
#[must_use]
pub fn slot_constants(program: &Program, analysis: &Analysis, slot: usize) -> Vec<SlotConstant> {
    let Some(bitness) = program.arch.bitness() else {
        return Vec::new();
    };
    analysis
        .classes
        .by_name
        .values()
        .filter_map(|c| {
            let entry = *c.slots.get(slot)?;
            let value = returned_constant(program, entry, bitness)?;
            Some(SlotConstant {
                class: c.name.clone(),
                entry,
                value,
            })
        })
        .collect()
}

/// One row of a protocol table: a class answering the slot with `value`,
/// and what the table's pass found for it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct SlotRow<T> {
    /// The constant the class answers the slot with.
    pub value: u64,
    /// The class.
    pub class: String,
    /// What the pass found for the class, when it found anything.
    pub found: Option<T>,
}

/// The classes answering `slot` with a constant whose name contains
/// `filter`, each with what `per` finds for it, worked out across the
/// cores and ordered by value, then class.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Discovery results with the recovered classes.
/// * `slot` - The vtable index the constant sits in, zero-based.
/// * `filter` - Case-insensitive substring of the class name; empty for all.
/// * `init` - Makes one worker's state.
/// * `per` - What the table shows for one class, over the worker's state.
pub(crate) fn slot_rows<S, T: Send>(
    program: &Program,
    analysis: &Analysis,
    slot: usize,
    filter: &str,
    init: impl Fn() -> S + Sync,
    per: impl Fn(&S, &SlotConstant) -> Option<T> + Sync,
) -> Vec<SlotRow<T>> {
    let q = filter.to_lowercase();
    let picked: Vec<SlotConstant> = slot_constants(program, analysis, slot)
        .into_iter()
        .filter(|c| q.is_empty() || c.class.to_lowercase().contains(&q))
        .collect();
    let found = striped_with(&picked, SLOT_ROWS_MIN, init, per);
    let mut rows: Vec<SlotRow<T>> = picked
        .into_iter()
        .zip(found)
        .map(|(c, found)| SlotRow {
            value: c.value,
            class: c.class,
            found: found.flatten(),
        })
        .collect();
    rows.sort_by(|a, b| a.value.cmp(&b.value).then_with(|| a.class.cmp(&b.class)));
    rows
}

/// Renders the classes answering `slot` with a constant as a `#`-headed
/// table, ordered by value, filtered by class name.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Discovery results.
/// * `slot` - The vtable index, zero-based.
/// * `filter` - Case-insensitive substring of the class name; empty for all.
/// * `limit` - Rows shown at most.
#[must_use]
pub fn slot_constants_tsv(
    program: &Program,
    analysis: &Analysis,
    slot: usize,
    filter: &str,
    limit: usize,
) -> String {
    let q = filter.to_lowercase();
    let mut rows: Vec<SlotConstant> = slot_constants(program, analysis, slot)
        .into_iter()
        .filter(|r| q.is_empty() || r.class.to_lowercase().contains(&q))
        .collect();
    rows.sort_by(|a, b| a.value.cmp(&b.value).then_with(|| a.class.cmp(&b.class)));
    let total = rows.len();
    let shown = total.min(limit);
    let mut out =
        format!("# {total} classes answer virtual {slot} with a constant, showing {shown}\n");
    out.push_str("value\tclass\tfunction\n");
    for r in rows.into_iter().take(limit) {
        let _ = writeln!(out, "{:#x}\t{}\t{:#x}", r.value, r.class, r.entry);
    }
    out
}
