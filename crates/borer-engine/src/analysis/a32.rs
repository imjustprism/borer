//! Function discovery for ARM32 (A32 and T32) code.
//!
//! [`discover()`] finds an ARM32 program's functions from the entry point,
//! the symbols and the extents the file declares, as the arm64 walk does:
//! it follows every branch, takes a `bl` or `blx` target as a new function
//! and a jump into a known start as a tail call, ends a path at a call to
//! a function named as never returning, and walks the cases of a jump
//! table it can bound ([`table`]): a `tbb` or `tbh`, and the A32 `adr`,
//! indexed load and `add pc` of a position-independent table. Each
//! instruction is decoded in the instruction set the program says its
//! address is in, an `IT` block's conditions carried along a fall-through.
//!
//! An instruction under a condition that moves control (`bxeq lr`,
//! `popne {r4, pc}`, `blne f`) is a block of its own. When the block before
//! it falls into it and nothing else jumps to it, that block ends in the
//! test of the condition, a [`BlockTerm::Cond`] whose successors are the
//! instruction after it (the condition fails) and the instruction itself
//! (it holds); the decompiler reads that test as the branch at
//! [`a32::SKIP`]. The instruction's own block then has the successors of
//! what it does. A linkage stub (a PLT entry, an import thunk) is named
//! after the import its slot holds ([`stub_slot`]).

use std::collections::{BTreeMap, BTreeSet};

use super::functions::helpers::is_noreturn_name;
use super::functions::{build_callers_and_names, fuel_for, mix, push_site};
use super::{Analysis, BasicBlock, BlockTerm, Function, NameSource, RefKind, bare_name, seeds};
use crate::isa::a32::{self, Cond, DpKind, Flow, Index, Insn, ItState, Offset, Op, Operand, PC};
use crate::program::{Program, SymbolKind};

/// Most instructions one walk decodes.
const WALK_MAX: usize = 1 << 18;
/// Most jump-table entries read for one dispatch.
const TABLE_MAX: u64 = 1024;
/// Instructions looked back over for a dispatch's bound and base.
const LOOK_BACK: usize = 16;
/// Instructions a linkage stub spends reaching its slot.
const STUB_MAX: usize = 4;
/// Where every fingerprint starts: the FNV-1a offset basis.
const HASH_SEED: u64 = 0xcbf2_9ce4_8422_2325;

/// Decodes the instruction at `va` in the instruction set the program says
/// it is in.
///
/// # Arguments
///
/// * `program` - The image.
/// * `va` - The address.
/// * `it` - The `IT` state before it; advanced past it.
///
/// # Returns
///
/// The instruction, or `None` when the address is not executable or holds
/// too few bytes.
pub(crate) fn decode(program: &Program, va: u64, it: &mut ItState) -> Option<Insn> {
    if !super::is_executable_va(program, va) {
        return None;
    }
    let bytes = program.read_va_upto(va, 4)?;
    a32::decode(bytes, va, program.modes.at(va), it)
}

/// Tells whether an instruction moves control under a condition: a
/// conditional return, call or jump that is no conditional branch.
///
/// # Arguments
///
/// * `i` - The instruction.
pub(crate) fn guarded(i: &Insn) -> bool {
    i.predicated() && i.flow() != Flow::Next
}

/// The slot a linkage stub at `va` jumps through: a PLT entry (`add ip,
/// pc, #a; add ip, ip, #b; ldr pc, [ip, #c]!`) or a Windows import thunk
/// (`movw ip, #lo; movt ip, #hi; ldr pc, [ip]`).
///
/// # Arguments
///
/// * `program` - The image.
/// * `va` - The stub's first instruction.
///
/// # Returns
///
/// The slot's address, or `None` when the code is no such stub.
pub(crate) fn stub_slot(program: &Program, va: u64) -> Option<u64> {
    let mut regs: BTreeMap<a32::Reg, u64> = BTreeMap::new();
    let mut it = ItState::default();
    let mut at = va;
    for _ in 0..STUB_MAX {
        let i = decode(program, at, &mut it)?;
        if let Op::Adr { rd, target } = i.op {
            regs.insert(rd, target);
        } else if let Op::Movw { rd, imm } = i.op {
            regs.insert(rd, u64::from(imm));
        } else if let Op::Movt { rd, imm } = i.op {
            let lo = regs.get(&rd).copied()? & 0xffff;
            regs.insert(rd, lo | (u64::from(imm) << 16));
        } else if let Op::Dp {
            kind: DpKind::Add,
            rd,
            rn,
            src: Operand::Imm { value, .. },
        } = i.op
        {
            let base = if rn == PC {
                i.pc()
            } else {
                regs.get(&rn).copied()?
            };
            regs.insert(rd, base.wrapping_add(u64::from(value)) & 0xffff_ffff);
        } else if let Op::Load {
            rt: PC,
            addr:
                a32::Addr {
                    base,
                    offset: Offset::Imm(d),
                    index: Index::Offset | Index::Pre,
                },
            ..
        } = i.op
        {
            return Some(regs.get(&base)?.wrapping_add_signed(i64::from(d)) & 0xffff_ffff);
        } else {
            return None;
        }
        at = i.next();
    }
    None
}

/// A resolved jump table: the dispatch, its cases and where the table
/// lies.
#[derive(Debug, Clone)]
struct Table {
    /// The dispatching instruction.
    site: u64,
    /// The case targets, in table order.
    targets: Vec<u64>,
}

/// The straight-line instructions before `at`, nearest first.
///
/// # Arguments
///
/// * `seen` - The walk's instructions by address.
/// * `at` - The dispatch.
fn before(seen: &BTreeMap<u64, Insn>, at: u64) -> Vec<&Insn> {
    let mut out = Vec::new();
    let mut cur = at;
    while out.len() < LOOK_BACK {
        let Some((_, p)) = seen.range(..cur).next_back() else {
            break;
        };
        if p.next() != cur {
            break;
        }
        out.push(p);
        cur = p.va;
    }
    out
}

/// Returns the number of cases a dispatch's guard admits.
///
/// The guard is a `cmp` with an immediate followed by a `bhi` to the
/// default or a return under `hi` (one more than the immediate) or the
/// same under `hs` (the immediate), or an `and` with a mask one short of a
/// power of two.
///
/// # Arguments
///
/// * `older` - The instructions before the dispatch, nearest first.
fn bound(older: &[&Insn]) -> Option<u64> {
    let mut guard: Option<Cond> = None;
    for i in older {
        if matches!(i.flow(), Flow::CondJump | Flow::Jump | Flow::Return)
            && matches!(i.cond, Cond::Hi | Cond::Hs)
        {
            guard = Some(i.cond);
        } else if let Op::Dp {
            kind: DpKind::Cmp,
            src: Operand::Imm { value, .. },
            ..
        } = i.op
        {
            let more = u64::from(guard? == Cond::Hi);
            return Some(u64::from(value) + more);
        } else if let Op::Dp {
            kind: DpKind::And,
            src: Operand::Imm { value, .. },
            ..
        } = i.op
            && value.checked_add(1).is_some_and(u32::is_power_of_two)
            && guard.is_none()
        {
            return Some(u64::from(value) + 1);
        }
    }
    None
}

/// Resolves the jump table an indirect jump dispatches through.
///
/// # Arguments
///
/// * `program` - The image.
/// * `seen` - The walk's instructions by address.
/// * `j` - The indirect jump.
///
/// # Returns
///
/// The table, or `None` when the jump is no dispatch the walk can bound.
fn table(program: &Program, seen: &BTreeMap<u64, Insn>, j: &Insn) -> Option<Table> {
    let older = before(seen, j.va);
    let count = bound(&older)?.min(TABLE_MAX);
    let word = |at: u64, n: usize| -> Option<u64> {
        let b = program.read_va(at, n)?;
        Some(
            b.iter()
                .rev()
                .fold(0u64, |acc, x| (acc << 8) | u64::from(*x)),
        )
    };
    let adr = |reg: a32::Reg| {
        older.iter().find_map(|i| {
            if let Op::Adr { rd, target } = i.op
                && rd == reg
            {
                Some(target)
            } else {
                None
            }
        })
    };
    let targets: Option<Vec<u64>> = if let Op::Tb { half, rn, .. } = j.op {
        let base = if rn == PC { j.pc() } else { adr(rn)? };
        let size = if half { 2 } else { 1 };
        (0..count)
            .map(|k| {
                let e = word(base + k * size, usize::try_from(size).ok()?)?;
                Some((j.pc() + 2 * e) & 0xffff_ffff)
            })
            .collect()
    } else if let Op::Dp {
        kind: DpKind::Add,
        rd: PC,
        rn: rb,
        src:
            Operand::Reg {
                rm: re,
                shift: a32::Shift::Lsl,
                amount: 0,
            },
    } = j.op
    {
        older.iter().find(|i| {
            matches!(i.op, Op::Load { rt, addr: a32::Addr { base, offset: Offset::Reg { amount: 2, .. }, .. }, .. } if rt == re && base == rb)
        })?;
        let base = adr(rb)?;
        (0..count)
            .map(|k| {
                let e = word(base + k * 4, 4)?;
                Some((base.wrapping_add(e) & 0xffff_ffff) & !1)
            })
            .collect()
    } else if let Op::Load {
        rt: PC,
        addr:
            a32::Addr {
                base: PC,
                offset: Offset::Reg { amount: 2, .. },
                index: Index::Offset,
            },
        ..
    } = j.op
    {
        (0..count)
            .map(|k| word(j.pc() + k * 4, 4).map(|t| t & !1))
            .collect()
    } else {
        None
    };
    let targets = targets?;
    targets
        .iter()
        .all(|t| super::is_executable_va(program, *t))
        .then_some(Table {
            site: j.va,
            targets,
        })
}

/// What one walk found.
struct Walked {
    /// The instructions by address.
    seen: BTreeMap<u64, Insn>,
    /// The functions it calls or tail-calls.
    callees: BTreeSet<u64>,
    /// Jump targets it followed.
    followed: BTreeSet<u64>,
    /// The jump tables it resolved.
    tables: Vec<Table>,
}

/// Walks one function from its entry.
///
/// # Arguments
///
/// * `program` - The image.
/// * `entry` - Where to start.
/// * `starts` - Known function starts: a jump into one is a tail call.
/// * `noreturn` - Functions that never return.
fn walk(program: &Program, entry: u64, starts: &BTreeSet<u64>, noreturn: &BTreeSet<u64>) -> Walked {
    let mut seen: BTreeMap<u64, Insn> = BTreeMap::new();
    let mut pending: Vec<(u64, ItState)> = vec![(entry, ItState::default())];
    let mut callees = BTreeSet::new();
    let mut followed = BTreeSet::new();
    let mut tables = Vec::new();
    let leaves = |t: u64| t != entry && starts.contains(&t);
    while let Some((va, mut it)) = pending.pop() {
        if seen.contains_key(&va) || seen.len() >= WALK_MAX {
            continue;
        }
        let Some(i) = decode(program, va, &mut it).filter(|i| i.op != Op::Invalid) else {
            continue;
        };
        seen.insert(va, i);
        let next = i.next();
        let falls = guarded(&i);
        match i.flow() {
            Flow::Next => pending.push((next, it)),
            Flow::CondJump => {
                if let Some(t) = i.target() {
                    if leaves(t) {
                        callees.insert(t);
                    } else {
                        followed.insert(t);
                        pending.push((t, ItState::default()));
                    }
                }
                pending.push((next, it));
            }
            Flow::Jump => {
                match i.target() {
                    Some(t) if leaves(t) => {
                        callees.insert(t);
                    }
                    Some(t) => {
                        followed.insert(t);
                        pending.push((t, ItState::default()));
                    }
                    None => {
                        if let Some(tab) = table(program, &seen, &i) {
                            for &t in &tab.targets {
                                followed.insert(t);
                                pending.push((t, ItState::default()));
                            }
                            tables.push(tab);
                        }
                    }
                }
                if falls {
                    pending.push((next, it));
                }
            }
            Flow::Call => {
                let target = i.target().filter(|t| super::is_executable_va(program, *t));
                callees.extend(target);
                if falls || !target.is_some_and(|t| noreturn.contains(&t)) {
                    pending.push((next, it));
                }
            }
            Flow::Return => {
                if falls {
                    pending.push((next, it));
                }
            }
            Flow::Invalid => {}
        }
    }
    Walked {
        seen,
        callees,
        followed,
        tables,
    }
}

/// Builds a function's record and its references from its walk.
///
/// # Arguments
///
/// * `entry` - The entry.
/// * `w` - The walk.
///
/// # Returns
///
/// The function (callers empty, name unset) and its references.
fn assemble(entry: u64, w: &Walked) -> (Function, Vec<(u64, u64, RefKind)>) {
    let insns: Vec<&Insn> = w.seen.values().collect();
    let present = |va: u64| w.seen.contains_key(&va);
    let mut targets: BTreeSet<u64> = BTreeSet::new();
    for i in &insns {
        if matches!(i.flow(), Flow::CondJump | Flow::Jump) {
            targets.extend(i.target().filter(|t| present(*t)));
        }
    }
    for t in &w.tables {
        targets.extend(t.targets.iter().copied().filter(|t| present(*t)));
    }
    let checked: BTreeSet<u64> = insns
        .iter()
        .filter(|g| guarded(g) && g.va != entry && !targets.contains(&g.va))
        .filter(|g| {
            w.seen
                .range(..g.va)
                .next_back()
                .is_some_and(|(_, p)| p.next() == g.va && p.flow() == Flow::Next)
        })
        .map(|g| g.va)
        .collect();
    let mut leaders: BTreeSet<u64> = targets;
    leaders.insert(entry);
    for i in &insns {
        if i.flow() != Flow::Next || guarded(i) {
            leaders.insert(i.next());
        }
        if guarded(i) {
            leaders.insert(i.va);
        }
    }
    let table_of: BTreeMap<u64, &Table> = w.tables.iter().map(|t| (t.site, t)).collect();
    let mut blocks: Vec<BasicBlock> = Vec::new();
    let mut current: Option<BasicBlock> = None;
    let mut last: Option<&Insn> = None;
    let close = |b: &mut BasicBlock, l: &Insn, blocks: &mut Vec<BasicBlock>| {
        let next = l.next();
        let unguarded_fall = || {
            if present(next) {
                vec![next]
            } else {
                Vec::new()
            }
        };
        let (term, mut succs) = match l.flow() {
            Flow::Next if checked.contains(&next) => {
                let after = w.seen.get(&next).map_or(next, Insn::next);
                (BlockTerm::Cond, vec![after, next])
            }
            Flow::Next => (BlockTerm::Fall, unguarded_fall()),
            Flow::CondJump => {
                let mut s: Vec<u64> = l.target().into_iter().collect();
                s.extend(unguarded_fall());
                (BlockTerm::Cond, s)
            }
            Flow::Jump => match l.target() {
                Some(t) => (BlockTerm::Jmp, vec![t]),
                None => (
                    BlockTerm::Indirect,
                    table_of
                        .get(&l.va)
                        .map(|t| t.targets.clone())
                        .unwrap_or_default(),
                ),
            },
            Flow::Call => (BlockTerm::Call, unguarded_fall()),
            Flow::Return => (BlockTerm::Ret, Vec::new()),
            Flow::Invalid => (BlockTerm::Invalid, Vec::new()),
        };
        if guarded(l) && !checked.contains(&l.va) && l.flow() != Flow::Call && present(next) {
            succs.push(next);
        }
        b.term = term;
        b.successors = succs;
        blocks.push(b.clone());
    };
    for i in &insns {
        let continues = last.is_some_and(|l| {
            l.next() == i.va && l.flow() == Flow::Next && !guarded(l) && !leaders.contains(&i.va)
        });
        if !continues {
            if let (Some(mut b), Some(l)) = (current.take(), last) {
                close(&mut b, l, &mut blocks);
            }
            current = Some(BasicBlock {
                start: i.va,
                end: i.next(),
                term: BlockTerm::Fall,
                successors: Vec::new(),
            });
        }
        if let Some(b) = current.as_mut() {
            b.end = i.next();
        }
        last = Some(i);
    }
    if let (Some(mut b), Some(l)) = (current.take(), last) {
        close(&mut b, l, &mut blocks);
    }
    let start = insns.first().map_or(entry, |i| i.va);
    let end = insns.last().map_or(entry, |i| i.next());
    let mut sites = Vec::new();
    let (mut body_hash, mut shape_hash) = (HASH_SEED, HASH_SEED);
    for i in &insns {
        let fixed = if i.target().is_some() || i.literal().is_some() {
            u64::from(i.word >> 24)
        } else {
            u64::from(i.word)
        };
        body_hash = mix(body_hash, fixed);
        shape_hash = mix(shape_hash, u64::from(i.word >> 24));
        let Some(t) = i.target() else { continue };
        body_hash = if (start..end).contains(&t) {
            mix(body_hash, t.wrapping_sub(i.va))
        } else {
            mix(body_hash, t)
        };
        let kind = match i.flow() {
            Flow::Call => RefKind::Call,
            Flow::Jump => RefKind::Jmp,
            Flow::CondJump if !present(t) => RefKind::Jmp,
            Flow::CondJump | Flow::Next | Flow::Return | Flow::Invalid => continue,
        };
        sites.push((t, i.va, kind));
    }
    let func = Function {
        entry,
        start,
        end,
        instr_count: insns.len(),
        blocks,
        callees: w.callees.iter().copied().collect(),
        callers: Vec::new(),
        name: None,
        name_inferred: false,
        name_source: NameSource::None,
        thunk: None,
        bound: None,
        funclet: None,
        signature: None,
        body_hash,
        shape_hash,
        returns_value: None,
        ret_width: None,
        ret_partial: None,
        ret_float: None,
        preserves_rax: false,
        hands_back_rdx: false,
        param_hints: BTreeMap::new(),
        ret_hint: None,
        stack_args: 0,
        stack_pop: 0,
    };
    (func, sites)
}

/// The data references of a function's instructions: a literal load's
/// address and the address the literal holds, an `adr` into data, and a
/// `movw`/`movt` pair's constant.
///
/// # Arguments
///
/// * `program` - The image.
/// * `w` - The walk.
/// * `found` - Takes each target and site.
fn data_refs(program: &Program, w: &Walked, found: &mut dyn FnMut(u64, u64)) {
    let mapped = |a: u64| program.section_at(a).is_some();
    let mut wide: BTreeMap<a32::Reg, (u64, u64)> = BTreeMap::new();
    for i in w.seen.values() {
        if let Some(lit) = i.literal() {
            found(lit, i.va);
            if let Some(v) = program
                .read_va(lit, 4)
                .and_then(|b| crate::num::u32_le(b, 0))
                .map(u64::from)
                .filter(|v| *v != 0 && mapped(*v))
            {
                found(v, i.va);
            }
        }
        if let Op::Adr { target, .. } = i.op
            && mapped(target)
            && !super::is_executable_va(program, target)
        {
            found(target, i.va);
        } else if let Op::Movw { rd, imm } = i.op {
            wide.insert(rd, (i.va, u64::from(imm)));
        } else if let Op::Movt { rd, imm } = i.op
            && let Some((_, lo)) = wide.remove(&rd)
        {
            let v = lo | (u64::from(imm) << 16);
            if mapped(v) {
                found(v, i.va);
            }
        }
    }
}

/// Discovers an ARM32 program's functions, blocks, references and jump
/// tables.
///
/// # Arguments
///
/// * `program` - The loaded image, ARM32.
///
/// # Returns
///
/// The analysis, indexed ([`Analysis::finish_index`]).
pub(crate) fn discover(program: &Program) -> Analysis {
    let seeds = seeds(program);
    let imports: BTreeMap<u64, &str> = program
        .symbols
        .iter()
        .filter(|s| s.kind == SymbolKind::Import && s.addr != 0)
        .map(|s| (s.addr, s.name.as_str()))
        .collect();
    let noreturn_name = |n: &str| is_noreturn_name(bare_name(&crate::search::demangled_name(n)));
    let mut noreturn: BTreeSet<u64> = program
        .symbols
        .iter()
        .filter(|s| s.kind != SymbolKind::Import && s.addr != 0 && noreturn_name(&s.name))
        .map(|s| s.addr)
        .collect();
    let mut starts: BTreeSet<u64> = seeds.iter().copied().collect();
    let mut walked: BTreeMap<u64, Walked> = BTreeMap::new();
    let mut fuel = fuel_for(program);
    let mut incomplete = false;
    let mut queue: Vec<u64> = seeds;
    for round in 0..2 {
        while let Some(e) = queue.pop() {
            if walked.contains_key(&e) {
                continue;
            }
            if fuel == 0 {
                incomplete = true;
                break;
            }
            if let Some(slot) = stub_slot(program, e)
                && imports.get(&slot).is_some_and(|n| noreturn_name(n))
            {
                noreturn.insert(e);
            }
            let w = walk(program, e, &starts, &noreturn);
            fuel = fuel.saturating_sub(crate::num::from_usize(w.seen.len()));
            for &c in &w.callees {
                if starts.insert(c) || !walked.contains_key(&c) {
                    queue.push(c);
                }
            }
            walked.insert(e, w);
        }
        if round == 0 {
            let redo: Vec<u64> = walked
                .iter()
                .filter(|(e, w)| w.followed.iter().any(|t| t != *e && starts.contains(t)))
                .map(|(e, _)| *e)
                .collect();
            if redo.is_empty() {
                break;
            }
            for e in &redo {
                walked.remove(e);
            }
            queue = redo;
        }
    }
    let mut analysis = Analysis {
        incomplete,
        ..Analysis::default()
    };
    let mut functions = Vec::with_capacity(walked.len());
    for (&entry, w) in &walked {
        if w.seen.is_empty() {
            continue;
        }
        let (mut f, sites) = assemble(entry, w);
        for (t, va, kind) in sites {
            push_site(&mut analysis.xrefs, t, va, kind, Some(entry));
        }
        data_refs(program, w, &mut |t, va| {
            push_site(&mut analysis.xrefs, t, va, RefKind::Data, Some(entry));
        });
        for t in &w.tables {
            analysis.jump_tables.insert(t.site, t.targets.clone());
        }
        if let Some(slot) = stub_slot(program, entry)
            && let Some(name) = imports.get(&slot)
        {
            f.name = Some(crate::search::demangled_name(name));
            f.name_source = NameSource::Symbol;
            f.thunk = Some(slot);
        }
        functions.push(f);
    }
    build_callers_and_names(program, &mut functions);
    analysis.functions = functions;
    analysis.finish_index(program);
    analysis
}
