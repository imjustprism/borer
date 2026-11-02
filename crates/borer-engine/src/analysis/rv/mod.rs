//! Function discovery for RISC-V code.
//!
//! [`discover()`] finds a RISC-V program's functions from the entry point,
//! the symbols and the extents the file declares (its `.eh_frame` among
//! them), as the arm walks do: it follows every branch and jump, takes a
//! `jal` or `jalr` that links in `ra` or `t0` as a call and its target as
//! a new function, a jump into a known start as a tail call, and ends a
//! path at a call to a function named as never returning. A `jalr` right
//! after the `auipc` that sets its base (the `call` and `tail` sequences)
//! goes to the address the two build, a jump there read as any other.
//! The data references are the addresses an `auipc` or `lui` builds with
//! the `addi`, load or store that reads the register it set. A PLT entry
//! is named after the import its GOT slot holds ([`stub_slot`]).
//!
//! Whether a function returns a value is read off its call sites
//! ([`infer_returns`]).
//!
//! Not found yet: the cases of a jump table (a `jr` through a loaded case
//! ends its path), and the functions only a pointer or nothing names.

use std::collections::{BTreeMap, BTreeSet};

mod returns;
pub(crate) use returns::infer as infer_returns;

use super::functions::helpers::is_noreturn_name;
use super::functions::{build_callers_and_names, fuel_for, mix, push_site};
use super::{Analysis, BasicBlock, BlockTerm, Function, NameSource, RefKind, bare_name, seeds};
use crate::isa::rv::{self, Alu, FOp, Flow, Insn, Op, RA, Reg, T0, Xlen, ZERO};
use crate::program::{Program, SymbolKind};

/// Most instructions one walk decodes.
const WALK_MAX: usize = 1 << 18;
/// Where every fingerprint starts: the FNV-1a offset basis.
const HASH_SEED: u64 = 0xcbf2_9ce4_8422_2325;

/// Decodes the instruction at `va` when an executable section holds it.
///
/// # Arguments
///
/// * `program` - The image.
/// * `va` - The address.
/// * `xlen` - The register width.
///
/// # Returns
///
/// The instruction, or `None` when the address is not executable or holds
/// too few bytes.
pub(crate) fn decode(program: &Program, va: u64, xlen: Xlen) -> Option<Insn> {
    if !super::is_executable_va(program, va) {
        return None;
    }
    rv::decode(program.read_va_upto(va, 4)?, va, xlen)
}

/// Returns the register an `auipc` or `lui` sets and the value it holds.
///
/// # Arguments
///
/// * `i` - The instruction.
/// * `xlen` - The register width.
fn upper(i: &Insn, xlen: Xlen) -> Option<(Reg, u64)> {
    let set = if let Op::Auipc { rd, target } = i.op {
        (rd, target)
    } else if let Op::Lui { rd, imm } = i.op {
        (rd, xlen.addr(imm.cast_unsigned()))
    } else {
        return None;
    };
    (set.0 != ZERO).then_some(set)
}

/// Returns the base register and offset an instruction adds to form an
/// address: a `jalr`, an `addi`, or an integer or float load or store.
///
/// # Arguments
///
/// * `op` - The operation.
fn base_off(op: Op) -> Option<(Reg, i64)> {
    match op {
        Op::Jalr { rs1, off, .. }
        | Op::Load { rs1, off, .. }
        | Op::Store { rs1, off, .. }
        | Op::Float(FOp::Load { rs1, off, .. } | FOp::Store { rs1, off, .. })
        | Op::Imm {
            op: Alu::Add,
            rs1,
            imm: off,
            word: false,
            ..
        } => Some((rs1, off)),
        Op::Lui { .. }
        | Op::Auipc { .. }
        | Op::Jal { .. }
        | Op::Branch { .. }
        | Op::Imm { .. }
        | Op::Reg3 { .. }
        | Op::Fence { .. }
        | Op::FenceI
        | Op::Ecall
        | Op::Ebreak
        | Op::Csr { .. }
        | Op::Lr { .. }
        | Op::Sc { .. }
        | Op::Amo { .. }
        | Op::Float(_)
        | Op::TrapRet
        | Op::System
        | Op::Unknown
        | Op::Invalid => None,
    }
}

/// Returns the address an instruction forms from a register an `auipc` or
/// `lui` set.
///
/// # Arguments
///
/// * `hi` - The registers set and their values.
/// * `i` - The instruction.
/// * `xlen` - The register width.
fn paired(hi: &BTreeMap<Reg, u64>, i: &Insn, xlen: Xlen) -> Option<u64> {
    let (base, off) = base_off(i.op)?;
    let v = xlen.addr(hi.get(&base)?.wrapping_add_signed(off));
    Some(if matches!(i.op, Op::Jalr { .. }) {
        v & !1
    } else {
        v
    })
}

/// Returns the integer register an instruction writes.
///
/// # Arguments
///
/// * `op` - The operation.
fn dest(op: Op) -> Option<Reg> {
    match op {
        Op::Lui { rd, .. }
        | Op::Auipc { rd, .. }
        | Op::Jal { rd, .. }
        | Op::Jalr { rd, .. }
        | Op::Load { rd, .. }
        | Op::Imm { rd, .. }
        | Op::Reg3 { rd, .. }
        | Op::Csr { rd, .. }
        | Op::Lr { rd, .. }
        | Op::Sc { rd, .. }
        | Op::Amo { rd, .. }
        | Op::Float(
            FOp::Cmp { rd, .. }
            | FOp::Class { rd, .. }
            | FOp::ToInt { rd, .. }
            | FOp::MvToInt { rd, .. },
        ) => Some(rd),
        Op::Branch { .. }
        | Op::Store { .. }
        | Op::Fence { .. }
        | Op::FenceI
        | Op::Ecall
        | Op::Ebreak
        | Op::Float(_)
        | Op::TrapRet
        | Op::System
        | Op::Unknown
        | Op::Invalid => None,
    }
}

/// The slot a PLT entry at `va` jumps through: `auipc t3, %hi; ld t3,
/// %lo(t3); jalr t1, t3` (`lw` on RV32).
///
/// # Arguments
///
/// * `program` - The image.
/// * `va` - The entry's first instruction.
/// * `xlen` - The register width.
///
/// # Returns
///
/// The slot's address, or `None` when the code is no such entry.
pub(crate) fn stub_slot(program: &Program, va: u64, xlen: Xlen) -> Option<u64> {
    let first = decode(program, va, xlen)?;
    let (r, hi) = upper(&first, xlen).filter(|_| matches!(first.op, Op::Auipc { .. }))?;
    let load = decode(program, first.next(), xlen)?;
    let Op::Load {
        rd,
        rs1,
        off,
        width: rv::Width::D | rv::Width::W,
    } = load.op
    else {
        return None;
    };
    let jump = decode(program, load.next(), xlen)?;
    let Op::Jalr {
        rd: link,
        rs1: target,
        off: 0,
    } = jump.op
    else {
        return None;
    };
    (rs1 == r && target == rd && link != RA && link != T0)
        .then(|| xlen.addr(hi.wrapping_add_signed(off)))
}

/// What one walk found.
struct Walked {
    /// The instructions by address.
    seen: BTreeMap<u64, Insn>,
    /// The functions it calls or tail-calls.
    callees: BTreeSet<u64>,
    /// Jump targets it followed.
    followed: BTreeSet<u64>,
    /// The `jalr` instructions an `auipc` before them resolved, with their
    /// targets.
    resolved: BTreeMap<u64, u64>,
    /// Whether the walk stopped at [`WALK_MAX`] with paths left.
    capped: bool,
}

/// What every walk shares.
struct Ctx<'a> {
    /// The image.
    program: &'a Program,
    /// The register width.
    xlen: Xlen,
    /// Known function starts: a jump into one is a tail call.
    starts: BTreeSet<u64>,
    /// Functions named as never returning.
    noreturn: BTreeSet<u64>,
    /// The imports by slot address.
    imports: BTreeMap<u64, &'a str>,
}

impl Ctx<'_> {
    /// Tells whether a call to `t` never returns: a function named so, or
    /// a PLT entry of an import named so.
    ///
    /// # Arguments
    ///
    /// * `t` - The callee.
    fn never_returns(&self, t: u64) -> bool {
        self.noreturn.contains(&t)
            || stub_slot(self.program, t, self.xlen)
                .and_then(|s| self.imports.get(&s))
                .is_some_and(|n| noreturn_name(n))
    }
}

/// Walks one function from its entry.
///
/// A call falling through to a known start never returns: no function
/// runs on into another's entry.
///
/// # Arguments
///
/// * `cx` - What the walks share.
/// * `entry` - Where to start.
fn walk(cx: &Ctx<'_>, entry: u64) -> Walked {
    let mut w = Walked {
        seen: BTreeMap::new(),
        callees: BTreeSet::new(),
        followed: BTreeSet::new(),
        resolved: BTreeMap::new(),
        capped: false,
    };
    let mut pending: Vec<(u64, Option<(Reg, u64)>)> = vec![(entry, None)];
    let executable = |t: u64| super::is_executable_va(cx.program, t);
    while let Some((va, hi)) = pending.pop() {
        if w.seen.contains_key(&va) {
            continue;
        }
        if w.seen.len() >= WALK_MAX {
            w.capped = true;
            break;
        }
        let Some(i) = decode(cx.program, va, cx.xlen).filter(|i| i.op != Op::Invalid) else {
            continue;
        };
        w.seen.insert(va, i);
        let next = i.next();
        let built = if let (Op::Jalr { rs1, off, .. }, Some((r, v))) = (i.op, hi)
            && r == rs1
        {
            Some(cx.xlen.addr(v.wrapping_add_signed(off)) & !1).filter(|t| executable(*t))
        } else {
            None
        };
        if let Some(t) = built {
            w.resolved.insert(va, t);
        }
        match (i.flow(), i.target().or(built)) {
            (Flow::Next, _) => pending.push((next, upper(&i, cx.xlen))),
            (Flow::CondJump | Flow::Jump, Some(t)) => {
                if t != entry && cx.starts.contains(&t) {
                    w.callees.insert(t);
                } else {
                    w.followed.insert(t);
                    pending.push((t, None));
                }
                if i.flow() == Flow::CondJump {
                    pending.push((next, None));
                }
            }
            (Flow::CondJump | Flow::Jump, None) | (Flow::Return | Flow::Invalid, _) => {}
            (Flow::Call, target) => {
                let target = target.filter(|t| executable(*t));
                w.callees.extend(target);
                let returns =
                    !target.is_some_and(|t| cx.never_returns(t)) && !cx.starts.contains(&next);
                if returns {
                    pending.push((next, None));
                }
            }
        }
    }
    w
}

/// Returns the bits of an encoding that name no address.
///
/// An instruction with a target or an `auipc` drops its immediate and
/// keeps its operation and registers: a branch or store its operation
/// and both registers, a `jal` or `auipc` its destination register, a
/// `jalr`, load or `addi` its operation and both registers. A compressed
/// form does the same within its own layout; `c.j` and `c.jal` keep only
/// their operation, and `c.jr` and `c.jalr`, which carry no offset, keep
/// every bit.
///
/// # Arguments
///
/// * `i` - The instruction.
/// * `addressed` - Whether it names an address.
fn fixed_bits(i: &Insn, addressed: bool) -> u32 {
    let branch = matches!(i.op, Op::Branch { .. });
    let keep = match (addressed, i.len == 2) {
        (false, _) => u32::MAX,
        (true, true) if branch => 0xe383,
        (true, true) if stores(i.op) || loads(i.op) => 0xe39f,
        (true, true) if matches!(i.op, Op::Imm { .. }) => 0xef83,
        (true, true) if matches!(i.op, Op::Jalr { .. }) => u32::MAX,
        (true, true) => 0xe003,
        (true, false) if branch || stores(i.op) => 0x01ff_f07f,
        (true, false) if matches!(i.op, Op::Auipc { .. } | Op::Jal { .. }) => 0xfff,
        (true, false) => 0x000f_ffff,
    };
    i.word & keep
}

/// Tells whether an operation is an integer or float load.
///
/// # Arguments
///
/// * `op` - The operation.
fn loads(op: Op) -> bool {
    matches!(op, Op::Load { .. } | Op::Float(FOp::Load { .. }))
}

/// Tells whether an operation is a store, whose offset is split around
/// the source register.
///
/// # Arguments
///
/// * `op` - The operation.
fn stores(op: Op) -> bool {
    matches!(op, Op::Store { .. } | Op::Float(FOp::Store { .. }))
}

/// Mixes an instruction's shape into a fingerprint: its mnemonic as the
/// listing spells it, the same for a compressed form and the one it
/// expands to.
///
/// # Arguments
///
/// * `h` - The fingerprint so far.
/// * `i` - The instruction.
fn shape(h: u64, i: &Insn) -> u64 {
    let text = rv::text(i);
    let mnemonic = text.split(' ').next().unwrap_or_default();
    mnemonic
        .bytes()
        .chain([b' '])
        .fold(h, |h, b| mix(h, u64::from(b)))
}

/// Returns how a block ending in `i` leaves and where it goes.
///
/// # Arguments
///
/// * `i` - The block's last instruction.
/// * `w` - The walk.
fn close(i: &Insn, w: &Walked) -> (BlockTerm, Vec<u64>) {
    let fall = || w.seen.contains_key(&i.next()).then_some(i.next());
    match i.flow() {
        Flow::Next => (BlockTerm::Fall, fall().into_iter().collect()),
        Flow::CondJump => (
            BlockTerm::Cond,
            i.target().into_iter().chain(fall()).collect(),
        ),
        Flow::Jump => match i.target().or_else(|| w.resolved.get(&i.va).copied()) {
            Some(t) => (BlockTerm::Jmp, vec![t]),
            None => (BlockTerm::Indirect, Vec::new()),
        },
        Flow::Call => (BlockTerm::Call, fall().into_iter().collect()),
        Flow::Return => (BlockTerm::Ret, Vec::new()),
        Flow::Invalid => (BlockTerm::Invalid, Vec::new()),
    }
}

/// Builds a walked function's blocks, fingerprints and code references.
///
/// # Arguments
///
/// * `entry` - The function's entry.
/// * `w` - Its walk.
/// * `data` - Each data address an `auipc` pair forms, keyed by the site
///   that uses it; mixed into the body fingerprint like a code target.
///
/// # Returns
///
/// The function, and each reference as its target, site and kind.
fn assemble(
    entry: u64,
    w: &Walked,
    data: &BTreeMap<u64, u64>,
) -> (Function, Vec<(u64, u64, RefKind)>) {
    let present = |va: u64| w.seen.contains_key(&va);
    let mut leaders: BTreeSet<u64> = BTreeSet::from([entry]);
    for i in w.seen.values() {
        if matches!(i.flow(), Flow::CondJump | Flow::Jump) {
            let target = i.target().or_else(|| w.resolved.get(&i.va).copied());
            leaders.extend(target.filter(|t| present(*t)));
        }
        if i.flow() != Flow::Next {
            leaders.insert(i.next());
        }
    }
    let mut blocks: Vec<BasicBlock> = Vec::new();
    let mut last: Option<&Insn> = None;
    for i in w.seen.values() {
        if !last.is_some_and(|l| l.next() == i.va && !leaders.contains(&i.va)) {
            blocks.push(BasicBlock {
                start: i.va,
                end: i.next(),
                term: BlockTerm::Fall,
                successors: smallvec::SmallVec::new(),
            });
        }
        if let Some(b) = blocks.last_mut() {
            let (term, succs) = close(i, w);
            b.end = i.next();
            b.term = term;
            b.successors = succs.into();
        }
        last = Some(i);
    }
    let start = w.seen.keys().next().copied().unwrap_or(entry);
    let end = w.seen.values().next_back().map_or(entry, Insn::next);
    let mut sites = Vec::new();
    let (mut body_hash, mut shape_hash) = (HASH_SEED, HASH_SEED);
    for i in w.seen.values() {
        let target = i.target().or_else(|| w.resolved.get(&i.va).copied());
        let formed = target.or_else(|| data.get(&i.va).copied());
        let addressed = formed.is_some() || matches!(i.op, Op::Auipc { .. });
        body_hash = mix(body_hash, u64::from(fixed_bits(i, addressed)));
        shape_hash = shape(shape_hash, i);
        if let Some(t) = formed {
            body_hash = if (start..end).contains(&t) {
                mix(body_hash, t.wrapping_sub(i.va))
            } else {
                mix(body_hash, t)
            };
        }
        let Some(t) = target else { continue };
        let kind = match i.flow() {
            Flow::Call => RefKind::Call,
            Flow::Jump => RefKind::Jmp,
            Flow::CondJump if !present(t) => RefKind::Jmp,
            Flow::CondJump | Flow::Next | Flow::Return | Flow::Invalid => continue,
        };
        sites.push((t, i.va, kind));
    }
    (
        function(entry, (start, end), w, blocks, (body_hash, shape_hash)),
        sites,
    )
}

/// Returns a discovered function with nothing inferred about it yet.
///
/// # Arguments
///
/// * `entry` - Its entry.
/// * `span` - Its lowest address and the address after its last
///   instruction.
/// * `w` - Its walk.
/// * `blocks` - Its blocks.
/// * `hashes` - Its body and shape fingerprints.
fn function(
    entry: u64,
    span: (u64, u64),
    w: &Walked,
    blocks: Vec<BasicBlock>,
    hashes: (u64, u64),
) -> Function {
    Function {
        entry,
        start: span.0,
        end: span.1,
        instr_count: w.seen.len(),
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
        body_hash: hashes.0,
        shape_hash: hashes.1,
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
    }
}

/// Reports the data references of a function's instructions.
///
/// Each is the address an `auipc` or `lui` builds with the `addi`, load or
/// store that reads its register in the same straight run of code, no call
/// between them (a callee may leave anything in the register), nor a
/// system call or an instruction the engine does not model (what they
/// write is unknown).
///
/// # Arguments
///
/// * `program` - The image.
/// * `w` - The walk.
/// * `xlen` - The register width.
/// * `found` - Takes each target and site.
fn data_refs(program: &Program, w: &Walked, xlen: Xlen, found: &mut dyn FnMut(u64, u64)) {
    let mut hi: BTreeMap<Reg, u64> = BTreeMap::new();
    let mut prev: Option<u64> = None;
    for i in w.seen.values() {
        if prev != Some(i.va) || w.followed.contains(&i.va) {
            hi.clear();
        }
        if !matches!(i.op, Op::Jalr { .. })
            && let Some(t) = paired(&hi, i, xlen)
            && program.section_at(t).is_some()
        {
            found(t, i.va);
        }
        if i.flow() == Flow::Call || matches!(i.op, Op::Ecall | Op::Unknown | Op::System) {
            hi.clear();
        } else if let Some(rd) = dest(i.op) {
            hi.remove(&rd);
        }
        if let Some((rd, v)) = upper(i, xlen) {
            hi.insert(rd, v);
        }
        prev = Some(i.next());
    }
}

/// Tells whether a function of this name never returns.
///
/// # Arguments
///
/// * `n` - The symbol's name, mangled or not.
fn noreturn_name(n: &str) -> bool {
    is_noreturn_name(bare_name(&crate::search::demangled_name(n)))
}

/// The functions walked so far.
struct Walks {
    /// Each walked function's walk, by entry.
    walked: BTreeMap<u64, Walked>,
    /// Instructions left to decode.
    fuel: u64,
    /// Whether the fuel ran out.
    incomplete: bool,
}

impl Walks {
    /// Walks every queued entry not yet walked and every function those
    /// walks call.
    ///
    /// # Arguments
    ///
    /// * `cx` - What the walks share; the callees join its starts.
    /// * `queue` - The entries.
    fn drain(&mut self, cx: &mut Ctx<'_>, mut queue: Vec<u64>) {
        while let Some(e) = queue.pop() {
            if self.walked.contains_key(&e) {
                continue;
            }
            if self.fuel == 0 {
                self.incomplete = true;
                break;
            }
            let w = walk(cx, e);
            self.incomplete |= w.capped;
            self.fuel = self
                .fuel
                .saturating_sub(crate::num::from_usize(w.seen.len()));
            for &c in &w.callees {
                if cx.starts.insert(c) || !self.walked.contains_key(&c) {
                    queue.push(c);
                }
            }
            self.walked.insert(e, w);
        }
    }
}

/// Discovers a RISC-V program's functions, blocks and references.
///
/// A function whose jumps reach a start another walk found later is
/// walked again, so the jump becomes a tail call, and so is one that ran
/// on past a call into what has since become a function's entry (a callee
/// that never returns, not known as such); when the fuel runs out
/// before that, its first walk stays.
///
/// # Arguments
///
/// * `program` - The loaded image, RISC-V.
/// * `xlen` - Its register width.
///
/// # Returns
///
/// The analysis, indexed ([`Analysis::finish_index`]).
pub(crate) fn discover(program: &Program, xlen: Xlen) -> Analysis {
    let seeds = seeds(program);
    let mut cx = Ctx {
        program,
        xlen,
        starts: seeds.iter().copied().collect(),
        noreturn: program
            .symbols
            .iter()
            .filter(|s| s.kind != SymbolKind::Import && s.addr != 0 && noreturn_name(&s.name))
            .map(|s| s.addr)
            .collect(),
        imports: program
            .symbols
            .iter()
            .filter(|s| s.kind == SymbolKind::Import && s.addr != 0)
            .map(|s| (s.addr, s.name.as_str()))
            .collect(),
    };
    let mut walks = Walks {
        walked: BTreeMap::new(),
        fuel: fuel_for(program),
        incomplete: false,
    };
    walks.drain(&mut cx, seeds);
    let redo: Vec<u64> = walks
        .walked
        .iter()
        .filter(|(e, w)| {
            let started = |t: &u64| t != *e && cx.starts.contains(t);
            w.followed.iter().any(started)
                || w.seen.values().any(|i| {
                    i.flow() == Flow::Call && w.seen.contains_key(&i.next()) && started(&i.next())
                })
        })
        .map(|(e, _)| *e)
        .collect();
    let stale: Vec<(u64, Walked)> = redo
        .iter()
        .filter_map(|e| walks.walked.remove_entry(e))
        .collect();
    walks.drain(&mut cx, redo);
    for (e, w) in stale {
        walks.walked.entry(e).or_insert(w);
    }
    let mut analysis = Analysis {
        incomplete: walks.incomplete,
        ..Analysis::default()
    };
    let kept: Vec<(u64, &Walked)> = walks
        .walked
        .iter()
        .filter(|(_, w)| !w.seen.is_empty())
        .map(|(&e, w)| (e, w))
        .collect();
    let built = super::striped(&kept, |&(entry, w)| {
        let mut data = Vec::new();
        data_refs(program, w, xlen, &mut |t, va| data.push((t, va)));
        let formed = data.iter().map(|&(t, va)| (va, t)).collect();
        let (f, sites) = assemble(entry, w, &formed);
        (f, sites, data)
    });
    let mut functions = Vec::with_capacity(kept.len());
    for ((entry, _), r) in kept.iter().zip(built) {
        let Some((f, sites, data)) = r else {
            analysis.incomplete = true;
            continue;
        };
        for (t, va, kind) in sites {
            push_site(&mut analysis.xrefs, t, va, kind, Some(*entry));
        }
        for (t, va) in data {
            push_site(&mut analysis.xrefs, t, va, RefKind::Data, Some(*entry));
        }
        functions.push(f);
    }
    build_callers_and_names(program, &mut functions);
    for f in &mut functions {
        if let Some(slot) = stub_slot(program, f.entry, xlen)
            && let Some(name) = cx.imports.get(&slot)
        {
            f.name = Some(crate::search::demangled_name(name));
            f.name_source = NameSource::Symbol;
            f.thunk = Some(slot);
        }
    }
    analysis.functions = functions;
    analysis.finish_index(program);
    analysis
}
