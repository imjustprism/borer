//! The guarded regions of a 32-bit function whose frame registers an
//! exception handler: `_except_handler3` or `_except_handler4` for
//! `__try`, a `__CxxFrameHandler3` thunk for C++ `try`.
//!
//! A 32-bit frame keeps no table of instruction ranges. It stores the
//! index of the `__try` it is in (the C++ state) into its registration at
//! `[ebp-4]` as it enters and leaves each region, and the handler reads it
//! when something is raised. So the ranges come from the code: the index
//! is followed through the blocks from the entry, each store changing it,
//! and a region holds the instructions run while the index is its own or
//! one of the regions it encloses. A block reached with two different
//! indexes, or a store of something other than a constant, leaves the
//! function unread rather than guessed.

use std::collections::{BTreeMap, BTreeSet};

use super::guards::{Clause, ClauseKind, Dialect, Guard, merged};
use super::{Analysis, Function, read_u32};
use crate::isa::x86::{Decoder, DecoderOptions, Instruction, Mnemonic, OpKind, Register};
use crate::program::Program;

/// Most passes the index is followed through the blocks.
const PASSES_MAX: usize = 64;
/// Most try blocks read from one `FuncInfo`.
const TRY_BLOCKS_MAX: u32 = 256;
/// Most catch clauses read from one try block.
const CATCHES_MAX: u32 = 64;

/// The handler a frame registers, and the table it reads.
enum Frame {
    /// `_except_handler4` or `_except_handler3`: the scope table's
    /// records, and the outermost level.
    Seh(Vec<super::functions::ScopeRecord>, i64),
    /// A C++ frame handler: the `FuncInfo`.
    Cxx(u64),
}

/// Lists the guarded regions of a 32-bit function.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Discovery results.
/// * `f` - The function.
///
/// # Returns
///
/// The guards, empty when the function registers no handler or its index
/// cannot be followed.
pub(super) fn guards(program: &Program, analysis: &Analysis, f: &Function) -> Vec<Guard> {
    let Some(frame) = frame(program, analysis, f) else {
        return Vec::new();
    };
    let outermost = match &frame {
        Frame::Seh(_, level) => *level,
        Frame::Cxx(_) => -1,
    };
    let Some(spans) = spans(program, f, outermost) else {
        return Vec::new();
    };
    let has = |va: u64| f.blocks.iter().any(|b| b.start == va);
    match frame {
        Frame::Seh(records, outer) => records
            .iter()
            .enumerate()
            .filter_map(|(k, r)| {
                let k = i64::try_from(k).ok()?;
                let levels = enclosed(&records, k, outer);
                let ranges = in_levels(&spans, &levels);
                let handler = u64::from(r.handler);
                let clause = if r.filter == 0 {
                    Clause {
                        kind: ClauseKind::Finally,
                        funclet: Some(handler),
                        resume: None,
                        selector: None,
                    }
                } else {
                    Clause {
                        kind: ClauseKind::Except(Some(u64::from(r.filter))),
                        funclet: (!has(handler)).then_some(handler),
                        resume: has(handler).then_some(handler),
                        selector: None,
                    }
                };
                (!ranges.is_empty()).then(|| Guard {
                    dialect: Dialect::Seh,
                    ranges,
                    clauses: vec![clause],
                })
            })
            .collect(),
        Frame::Cxx(info) => cxx(program, info, &spans).unwrap_or_default(),
    }
}

/// Finds the handler a function's prologue registers.
///
/// The prologue pushes the scope table's address (and, inline, the
/// handler's), or loads a C++ handler thunk's; it is read in the entry
/// block and, when that ends calling a frame helper, the block after it.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Discovery results, for the handler's name.
/// * `f` - The function.
///
/// # Returns
///
/// The frame, or `None` when the prologue registers no handler this
/// reads.
fn frame(program: &Program, analysis: &Analysis, f: &Function) -> Option<Frame> {
    let mut values = Vec::new();
    let entry = f.blocks.iter().position(|b| b.start == f.entry)?;
    for b in f.blocks.iter().skip(entry).take(2) {
        for i in decode(program, b.start, b.end) {
            let pushed = i.mnemonic() == Mnemonic::Push && i.op0_kind() == OpKind::Immediate32;
            let loaded = i.mnemonic() == Mnemonic::Mov
                && i.op0_kind() == OpKind::Register
                && i.op1_kind() == OpKind::Immediate32;
            if pushed || loaded {
                values.push(u64::from(i.immediate32()));
            }
        }
    }
    let eh3 = values.iter().any(|&v| {
        analysis
            .function(v)
            .and_then(|h| h.name.as_deref())
            .is_some_and(|n| n.contains("except_handler3"))
    });
    for &v in &values {
        if let Some(info) = super::eh::handler_thunk(program, analysis, 32, v) {
            return Some(Frame::Cxx(info));
        }
        let records = super::functions::seh_scope_records(program, v, f.entry, !eh3);
        if !records.is_empty() {
            return Some(Frame::Seh(records, if eh3 { -1 } else { -2 }));
        }
    }
    None
}

/// Decodes the instructions of `start..end`.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `start` - First address.
/// * `end` - One past the last.
///
/// # Returns
///
/// The instructions; none when the bytes are not mapped.
fn decode(program: &Program, start: u64, end: u64) -> Vec<Instruction> {
    usize::try_from(end.saturating_sub(start))
        .ok()
        .and_then(|n| program.read_va(start, n))
        .map(|bytes| {
            Decoder::with_ip(32, bytes, start, DecoderOptions::NONE)
                .into_iter()
                .collect()
        })
        .unwrap_or_default()
}

/// Reads what a store to the registration's index writes.
///
/// # Arguments
///
/// * `i` - The instruction.
///
/// # Returns
///
/// `None` when the instruction does not write the index, `Some(None)`
/// when it writes something other than a constant, else the value.
fn stored(i: &Instruction) -> Option<Option<i64>> {
    if !(i.op0_kind() == OpKind::Memory
        && i.memory_base() == Register::EBP
        && i.memory_index() == Register::None
        && crate::disasm::displacement(i, 32) == -4
        && matches!(i.mnemonic(), Mnemonic::Mov | Mnemonic::And | Mnemonic::Or))
    {
        return None;
    }
    let imm = matches!(i.op1_kind(), OpKind::Immediate32 | OpKind::Immediate8to32)
        .then(|| i64::from(i.immediate32().cast_signed()));
    let m = i.mnemonic();
    Some(imm.filter(|&v| {
        m == Mnemonic::Mov || (m == Mnemonic::And && v == 0) || (m == Mnemonic::Or && v == -1)
    }))
}

/// Follows the registration's index through the function.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `f` - The function.
/// * `outermost` - The index before any region is entered.
///
/// # Returns
///
/// `(start, end, index)` for each instruction run from the entry, or
/// `None` when a block is reached with two indexes or an index that is
/// not a constant.
fn spans(program: &Program, f: &Function, outermost: i64) -> Option<Vec<(u64, u64, i64)>> {
    let index: BTreeMap<u64, usize> = f
        .blocks
        .iter()
        .enumerate()
        .map(|(i, b)| (b.start, i))
        .collect();
    let code: Vec<Vec<Instruction>> = f
        .blocks
        .iter()
        .map(|b| decode(program, b.start, b.end))
        .collect();
    let mut at_entry: Vec<Option<i64>> = vec![None; f.blocks.len()];
    let entry = *index.get(&f.entry)?;
    at_entry[entry] = Some(outermost);
    let mut work = vec![entry];
    let mut steps = 0;
    while let Some(b) = work.pop() {
        steps += 1;
        if steps > PASSES_MAX * f.blocks.len().max(1) {
            return None;
        }
        let mut level = at_entry[b]?;
        for i in &code[b] {
            if let Some(v) = stored(i) {
                level = v?;
            }
        }
        for s in &f.blocks[b].successors {
            let Some(&t) = index.get(s) else {
                continue;
            };
            match at_entry[t] {
                None => {
                    at_entry[t] = Some(level);
                    work.push(t);
                }
                Some(l) if l == level => {}
                Some(_) => return None,
            }
        }
    }
    let mut out = Vec::new();
    for (b, instrs) in code.iter().enumerate() {
        let Some(mut level) = at_entry[b] else {
            continue;
        };
        for i in instrs {
            if let Some(v) = stored(i) {
                level = v?;
            }
            out.push((i.ip(), i.next_ip(), level));
        }
    }
    Some(out)
}

/// Lists a region's own index and those of every region it encloses.
///
/// # Arguments
///
/// * `records` - The scope table's records.
/// * `k` - The region.
/// * `outer` - The outermost level, where every chain ends.
///
/// # Returns
///
/// The indexes.
fn enclosed(records: &[super::functions::ScopeRecord], k: i64, outer: i64) -> BTreeSet<i64> {
    let mut out = BTreeSet::from([k]);
    for (j, _) in records.iter().enumerate() {
        let Ok(mut at) = i64::try_from(j) else {
            continue;
        };
        for _ in 0..records.len() {
            if at == k {
                out.extend(i64::try_from(j));
                break;
            }
            let Some(r) = usize::try_from(at).ok().and_then(|a| records.get(a)) else {
                break;
            };
            let up = i64::from(r.enclosing.cast_signed());
            if up == outer || up < 0 {
                break;
            }
            at = up;
        }
    }
    out
}

/// Collects the instructions whose index is one of `levels` into ranges.
///
/// # Arguments
///
/// * `spans` - Each instruction's index ([`spans`]).
/// * `levels` - The indexes.
///
/// # Returns
///
/// Sorted, disjoint ranges.
fn in_levels(spans: &[(u64, u64, i64)], levels: &BTreeSet<i64>) -> Vec<(u64, u64)> {
    merged(
        spans
            .iter()
            .filter(|s| levels.contains(&s.2))
            .map(|s| (s.0, s.1))
            .collect(),
    )
}

/// Reads the try blocks of a 32-bit `FuncInfo`.
///
/// Each try block spans the states `low..=high`; its handler array holds
/// sixteen-byte entries, each the catch's adjectives, its type
/// descriptor's address, the caught object's frame offset and the catch
/// funclet's address.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `info` - The `FuncInfo` address.
/// * `spans` - Each instruction's state ([`spans`]).
///
/// # Returns
///
/// The guards, or `None` when the maps do not hold together.
fn cxx(program: &Program, info: u64, spans: &[(u64, u64, i64)]) -> Option<Vec<Guard>> {
    let blocks = read_u32(program, info.checked_add(12)?)?;
    if blocks > TRY_BLOCKS_MAX {
        return None;
    }
    let map = u64::from(read_u32(program, info.checked_add(16)?)?);
    let mut out = Vec::new();
    for block in 0..u64::from(blocks) {
        let entry = map.checked_add(block * 20)?;
        let low = i64::from(read_u32(program, entry)?.cast_signed());
        let high = i64::from(read_u32(program, entry + 4)?.cast_signed());
        let catches = read_u32(program, entry + 12)?.min(CATCHES_MAX);
        let handlers = u64::from(read_u32(program, entry + 16)?);
        let mut clauses = Vec::new();
        for clause in 0..u64::from(catches) {
            let h = handlers.checked_add(clause * 16)?;
            let adjectives = read_u32(program, h)?;
            let ty = Some(u64::from(read_u32(program, h + 4)?)).filter(|&t| t != 0);
            let funclet = u64::from(read_u32(program, h + 12)?);
            if !super::is_executable_va(program, funclet) {
                return None;
            }
            clauses.push(Clause {
                kind: ClauseKind::Catch(crate::unwind::catch_decl(program, adjectives, ty)),
                funclet: Some(funclet),
                resume: None,
                selector: None,
            });
        }
        let ranges = in_levels(spans, &(low..=high).collect());
        if !ranges.is_empty() && !clauses.is_empty() {
            out.push(Guard {
                dialect: Dialect::Cxx,
                ranges,
                clauses,
            });
        }
    }
    Some(out)
}
