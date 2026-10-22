//! Whether any caller reads a function's return register after the call.
//!
//! A void function leaves whatever its last callee or scratch computation put
//! in `rax`; without this fact the decompiler has to render `return rax;` for
//! it. Each call site is scanned forward from the call, down both sides of
//! every branch: a read of `rax` on any path (any width, including as an
//! address register) means the value is used, a full write of `eax`/`rax` or
//! another call on every path means it is dead at that site, a `ret` hands
//! the value on to the caller's own callers (used exactly when the caller's
//! result is), and a path the scan cannot follow counts as used. A jump into
//! the function from another one is a tail call, which hands the value on
//! the same way. The hand-on rule runs to a fixpoint, so a chain of void
//! wrappers ending in a caller that discards the value is void through.
//!
//! The body speaks too: a function that reaches a `ret` without writing rax,
//! or whose every exit hands back what a callee that itself returns nothing
//! left there, returns nothing whatever its callers seem to do.
//!
//! A 64-bit target hands a `float` or a `double` back in `xmm0`, and such a
//! function never writes rax: it returns a value when its declaration says
//! so, when some caller reads xmm0 after the call and every exit leaves one
//! there, and also when nobody calls it and its own exits leave that float
//! ([`float_results`]).
//! A 32-bit target hands it back on the x87 stack, in `st0`, which every
//! exit of such a function leaves one value deeper than it was entered
//! ([`x87_results`]).

use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use crate::isa::x86::{
    ConditionCode, FlowControl, Instruction, InstructionInfoFactory, Mnemonic, OpAccess, OpKind,
    Register,
};

use super::functions::{decode_at, decode_block};
use super::typelib;
use super::{Analysis, BlockTerm, Function, RefKind, is_imm, striped_with, x87};
use crate::program::{Program, SymbolKind};
use exits::Scan;
use uses::{FloatUse, float_use};

mod exits;
mod uses;

/// Fewest functions worth a worker each when the call sites are classified.
const CLASSIFY_MIN: usize = 256;
/// Longest run of instructions scanned along one path after a call.
const SCAN_MAX: usize = 12;
/// Most paths a call site's scan follows through the caller's branches.
const PATHS_MAX: usize = 8;
/// Most rounds of the pass-through rule: each round lets one more link of a
/// chain of wrappers learn its callee returns nothing.
const PASS_ROUNDS_MAX: usize = 64;
/// Blocks followed backwards from a `ret` to find the last write of rax.
pub(super) const RET_LANE_DEPTH: u8 = 4;
/// Longest function checked for handing rax back untouched.
const PRESERVE_MAX: usize = 32;
/// Blocks a function's body is walked for the vector registers it takes
/// arguments in.
const VECTOR_SCAN_MAX: usize = 1024;
/// A bit for each of the vector registers a 32-bit function may take an
/// argument in, `xmm0` to `xmm5`.
const ALL_VECTORS: u8 = 0b11_1111;

/// What one call site does with the return register.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Site {
    /// Read before being overwritten, or lost in a branch: used, with the
    /// width in bits of the read (the whole register when nothing is known).
    Used(u8),
    /// Overwritten in full or clobbered by another call before any read.
    Dead,
    /// Handed on by the caller's `ret`: used exactly when the caller's result
    /// is (the caller's entry).
    Tail(u64),
    /// Lost in a branch, or the scan ran out: taken as used, but no read
    /// was seen.
    Unknown,
}

/// What one function's call sites and body say about its result.
#[derive(Debug, Clone, PartialEq, Eq)]
struct Facts {
    /// What each call site does with the return register, a tail jump into
    /// the function included.
    sites: Vec<Site>,
    /// What each caller does with `rdx` after the call, the second-result
    /// lane: a read before a write wants the callee's own value.
    sites_rdx: Vec<Site>,
    /// Width in bits of the value the function's own `ret`s hand back
    /// ([`body_lane`]).
    body_lane: u8,
    /// Width in bits the function's own `ret` paths WRITE of rax
    /// ([`body_lane`]): a byte or word partial write, not a value that
    /// merely fits one.
    body_write: u8,
    /// The function hands rax back untouched ([`preserves`]).
    preserves: bool,
    /// The function hands rdx back untouched ([`preserves`]), so a caller
    /// reading it after the call reads its own value, not a second result.
    preserves_rdx: bool,
    /// The function hands xmm0 back untouched ([`preserves`]).
    preserves_float: bool,
    /// The writes nearest the exits leave a float in xmm0 ([`float_last`]).
    float_last: bool,
}

impl Facts {
    /// What is known of a function nobody classified: no sites, the whole
    /// register returned.
    const NONE: Facts = Facts {
        sites: Vec::new(),
        sites_rdx: Vec::new(),
        body_lane: 64,
        body_write: 64,
        preserves: false,
        preserves_rdx: false,
        preserves_float: false,
        float_last: false,
    };
}

/// The register a function hands its result back in.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ResultReg {
    /// `rax`, where an integer or a pointer comes back.
    Rax,
    /// `rdx`, where a second result comes back.
    Rdx,
    /// `xmm0`, where a 64-bit target's `float` or `double` comes back.
    Xmm0,
}

/// What a function's exits hand back in rax: the last write of rax on each
/// path to a `ret`, or the callee a tail jump hands over to.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
struct Handed {
    /// Some path from the entry reaches a `ret` without writing rax, or
    /// through an idiom that says it holds no result ([`exits::scan`]).
    nothing: bool,
    /// Some path's last write of rax is the function's own instruction.
    own: bool,
    /// Some path's last write of rax is the function's own instruction and
    /// nothing after it on the way to the `ret` reads the value back: no
    /// compare, store or copy took it as scratch.
    bare: bool,
    /// The direct callees whose result some path hands back, by a call
    /// before a `ret` or by a jump into them, sorted.
    calls: Vec<u64>,
    /// Some path hands back what an indirect call or jump left, or one
    /// could not be followed.
    unknown: bool,
    /// Widths in bits the own writes of xmm0 name: 32 for a single
    /// precision instruction, 64 for a double precision one; sorted, and
    /// empty for rax or a write that names none (`xorps xmm0, xmm0`).
    float_bits: Vec<u8>,
}

impl Handed {
    /// What a function nothing was learned of hands back.
    const UNKNOWN: Handed = Handed {
        nothing: false,
        own: false,
        bare: false,
        calls: Vec::new(),
        unknown: true,
        float_bits: Vec::new(),
    };
}

/// Fills the return facts of every function.
///
/// [`Function::returns_value`](super::Function::returns_value),
/// [`Function::ret_width`](super::Function::ret_width) and
/// [`Function::ret_float`](super::Function::ret_float) come from the call
/// sites and the returning writes,
/// [`Function::preserves_rax`](super::Function::preserves_rax) from the
/// body alone.
///
/// # Arguments
///
/// * `program` - The image the callers are decoded from.
/// * `analysis` - Functions and cross-references; the flag is written in place.
pub(crate) fn infer(program: &Program, analysis: &mut Analysis) {
    let Some(bitness) = program.arch.bitness() else {
        return;
    };
    let shared: &Analysis = analysis;
    let rdx_args: Vec<bool> = striped_with(
        &shared.functions,
        CLASSIFY_MIN,
        || RefCell::new(InstructionInfoFactory::new()),
        |factory, f| reads_rdx_arg(program, &mut factory.borrow_mut(), bitness, f),
    )
    .into_iter()
    .map(|r| r.unwrap_or(false))
    .collect();
    let facts: Vec<Facts> = striped_with(
        &shared.functions,
        CLASSIFY_MIN,
        || RefCell::new(InstructionInfoFactory::new()),
        |factory, f| {
            let factory = &mut *factory.borrow_mut();
            let sites = shared
                .xrefs_to(f.entry)
                .iter()
                .filter_map(|s| match s.kind {
                    RefKind::Call => Some(classify(
                        program,
                        shared,
                        factory,
                        bitness,
                        s.va,
                        Register::RAX,
                        &rdx_args,
                    )),
                    RefKind::Jmp => match s.from_entry {
                        Some(from) if from == f.entry => None,
                        Some(from) => Some(Site::Tail(from)),
                        None => Some(Site::Unknown),
                    },
                    RefKind::Data | RefKind::Index | RefKind::Table | RefKind::Ptr => None,
                })
                .collect();
            let sites_rdx = shared
                .xrefs_to(f.entry)
                .iter()
                .filter_map(|s| match s.kind {
                    RefKind::Call => Some(classify(
                        program,
                        shared,
                        factory,
                        bitness,
                        s.va,
                        Register::RDX,
                        &rdx_args,
                    )),
                    _ => None,
                })
                .collect();
            Facts {
                sites,
                sites_rdx,
                body_lane: body_lane(program, factory, bitness, f),
                body_write: body_write(program, factory, bitness, f),
                preserves: preserves(program, factory, bitness, f, ResultReg::Rax),
                preserves_rdx: preserves(program, factory, bitness, f, ResultReg::Rdx),
                preserves_float: preserves(program, factory, bitness, f, ResultReg::Xmm0),
                float_last: bitness == 64 && float_last(program, factory, bitness, f),
            }
        },
    )
    .into_iter()
    .map(|f| f.unwrap_or(Facts::NONE))
    .collect();
    let hand_back = |reg: ResultReg| -> Vec<Handed> {
        let preserving: Vec<bool> = facts
            .iter()
            .map(|f| match reg {
                ResultReg::Rax => f.preserves,
                ResultReg::Rdx => false,
                ResultReg::Xmm0 => f.preserves_float,
            })
            .collect();
        striped_with(
            &shared.functions,
            CLASSIFY_MIN,
            || RefCell::new(InstructionInfoFactory::new()),
            |factory, f| {
                handed_back(
                    program,
                    shared,
                    &mut factory.borrow_mut(),
                    bitness,
                    f,
                    &preserving,
                    reg,
                )
            },
        )
        .into_iter()
        .map(|h| h.unwrap_or(Handed::UNKNOWN))
        .collect()
    };
    let handed = hand_back(ResultReg::Rax);
    let read: Vec<bool> = facts
        .iter()
        .map(|f| f.sites.iter().any(|site| matches!(site, Site::Used(_))))
        .collect();
    let floats = if bitness == 64 {
        let preserving: Vec<bool> = facts.iter().map(|f| f.preserves_float).collect();
        let uses: Vec<Vec<FloatUse>> = striped_with(
            &shared.functions,
            CLASSIFY_MIN,
            || RefCell::new(InstructionInfoFactory::new()),
            |factory, f| {
                let factory = &mut *factory.borrow_mut();
                shared
                    .xrefs_to(f.entry)
                    .iter()
                    .filter_map(|s| match s.kind {
                        RefKind::Call => Some(float_use(
                            program,
                            shared,
                            factory,
                            bitness,
                            s.va,
                            &preserving,
                        )),
                        RefKind::Jmp => s
                            .from_entry
                            .filter(|&from| from != f.entry)
                            .map(FloatUse::Tail),
                        RefKind::Data | RefKind::Index | RefKind::Table | RefKind::Ptr => None,
                    })
                    .collect()
            },
        )
        .into_iter()
        .map(Option::unwrap_or_default)
        .collect();
        let last: Vec<bool> = facts.iter().map(|f| f.float_last).collect();
        float_results(
            program,
            analysis,
            &uses,
            &hand_back(ResultReg::Xmm0),
            &read,
            &last,
        )
    } else {
        x87_results(program, shared, &x87_kept(program, shared))
    };
    let nothing = produces_nothing(analysis, &facts, &handed, &read, &floats);
    let mut verdicts: Vec<Option<bool>> = facts
        .iter()
        .zip(&read)
        .zip(&nothing)
        .zip(&handed)
        .zip(&floats)
        .map(|((((f, &read), &nothing), h), float)| {
            if read || float.is_some() {
                Some(true)
            } else if nothing {
                Some(false)
            } else if f.sites.is_empty() {
                None
            } else if f.sites.iter().any(|site| matches!(site, Site::Unknown)) {
                Some(true)
            } else {
                (!(h.bare && h.calls.is_empty() && !h.unknown)).then_some(false)
            }
        })
        .collect();
    let widths: Vec<Option<u8>> = facts
        .iter()
        .map(|f| {
            let callers = f
                .sites
                .iter()
                .filter_map(|site| match site {
                    Site::Used(bits) => Some(*bits),
                    Site::Unknown | Site::Tail(_) => Some(64),
                    Site::Dead => None,
                })
                .max()
                .unwrap_or(64);
            let width = callers.min(f.body_lane);
            (width <= 16).then_some(width)
        })
        .collect();
    let partials: Vec<Option<u8>> = facts
        .iter()
        .map(|f| (f.body_write <= 16).then_some(f.body_write))
        .collect();
    loop {
        let mut changed = false;
        for (i, f) in facts.iter().enumerate() {
            if verdicts[i] == Some(true) || nothing[i] {
                continue;
            }
            let handed_on = f.sites.iter().any(|site| match site {
                Site::Tail(caller) => analysis
                    .entry_index
                    .get(caller)
                    .is_none_or(|&c| verdicts[c] != Some(false) && floats[c].is_none()),
                Site::Used(_) | Site::Dead | Site::Unknown => false,
            });
            if handed_on {
                verdicts[i] = Some(true);
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    for (((((f, verdict), width), partial), facts), float) in analysis
        .functions
        .iter_mut()
        .zip(verdicts)
        .zip(widths)
        .zip(partials)
        .zip(facts)
        .zip(floats)
    {
        f.returns_value = verdict;
        f.ret_width = width;
        f.ret_partial = partial;
        f.preserves_rax = facts.preserves;
        f.hands_back_rdx = !facts.preserves_rdx
            && facts
                .sites_rdx
                .iter()
                .any(|site| matches!(site, Site::Used(_)));
        f.ret_float = float;
    }
}

/// Block start to its index in the function's blocks.
///
/// # Arguments
///
/// * `f` - The function.
fn block_index(f: &Function) -> BTreeMap<u64, usize> {
    f.blocks
        .iter()
        .enumerate()
        .map(|(i, b)| (b.start, i))
        .collect()
}

/// The predecessor indices of every block, in the order the successor
/// lists name them.
///
/// # Arguments
///
/// * `f` - The function.
/// * `idx` - Its [`block_index`].
fn predecessors(f: &Function, idx: &BTreeMap<u64, usize>) -> Vec<Vec<usize>> {
    let mut preds: Vec<Vec<usize>> = vec![Vec::new(); f.blocks.len()];
    for (i, b) in f.blocks.iter().enumerate() {
        for s in &b.successors {
            if let Some(p) = idx.get(s).and_then(|&j| preds.get_mut(j)) {
                p.push(i);
            }
        }
    }
    preds
}

/// The register an instruction writes rax through, when it writes it:
/// `al`, `ah`, `ax`, `eax` or `rax`.
///
/// The register facts name a 32-bit destination on a 64-bit target by its
/// 64-bit register, since the write clears the upper half; a destination
/// operand names the width the instruction itself writes.
///
/// # Arguments
///
/// * `factory` - Register-access facts.
/// * `i` - The instruction.
fn rax_write(factory: &mut InstructionInfoFactory, i: &Instruction) -> Option<Register> {
    let written = factory
        .info(i)
        .used_registers()
        .iter()
        .find(|ur| {
            ur.register().full_register() == Register::RAX
                && matches!(
                    ur.access(),
                    OpAccess::Write
                        | OpAccess::ReadWrite
                        | OpAccess::CondWrite
                        | OpAccess::ReadCondWrite
                )
        })
        .map(|ur| ur.register())?;
    let operand = (i.op_count() > 0 && i.op0_kind() == OpKind::Register)
        .then(|| i.op0_register())
        .filter(|r| r.full_register() == Register::RAX);
    Some(operand.unwrap_or(written))
}

/// Tells whether an instruction is a call, which writes rax with its
/// result.
///
/// # Arguments
///
/// * `i` - The instruction.
fn is_call(i: &Instruction) -> bool {
    matches!(
        i.flow_control(),
        FlowControl::Call | FlowControl::IndirectCall
    )
}

/// Tells whether an instruction writes rax, a call counting as a write.
///
/// # Arguments
///
/// * `factory` - Register-access facts.
/// * `i` - The instruction.
fn writes_rax(factory: &mut InstructionInfoFactory, i: &Instruction) -> bool {
    is_call(i) || rax_write(factory, i).is_some()
}

/// Tells whether an instruction writes `rdx` in full or calls, either of
/// which leaves the register not as it found it.
///
/// # Arguments
///
/// * `factory` - Reused instruction-info factory.
/// * `i` - The instruction.
fn writes_rdx(factory: &mut InstructionInfoFactory, i: &Instruction) -> bool {
    if is_call(i)
        || matches!(
            i.flow_control(),
            FlowControl::UnconditionalBranch | FlowControl::IndirectBranch
        )
    {
        return true;
    }
    factory.info(i).used_registers().iter().any(|ur| {
        ur.register().full_register() == Register::RDX
            && matches!(ur.access(), OpAccess::Write | OpAccess::CondWrite)
            && full_names(Register::RDX).contains(&ur.register())
    })
}

/// The last write of a result register on a path to an exit.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Writer {
    /// A call to the direct callee at this entry.
    Call(u64),
    /// An indirect call.
    Indirect,
    /// One of the function's own instructions, with the float precision
    /// it names ([`float_bits`]).
    Own(Option<u8>),
}

/// What each exit of a function hands back in a result register.
///
/// From every `ret` the blocks are walked backwards to the last write of
/// the register on each path; reaching the entry first means the path
/// writes nothing. A call writes it with its callee's result, except a call
/// to a callee that hands the register back untouched ([`preserves`]),
/// which the walk looks past. A jump out of the function hands over to its
/// target, whose result is then the function's. The frame idiom `mov rax,
/// rsp` as the first instruction, rax standing in for the entry stack
/// pointer while the callee-saved registers are stored to their home slots,
/// is no write of a result. A lone `ret` is a stub that says nothing. The
/// idioms of a path that holds no result, and the reads that make an own
/// write scratch, are [`exits::scan`]'s.
/// A float exit whose writes name no precision (`movaps xmm0, xmm1`,
/// `xorps xmm0, xmm0`) takes the copy's source precision in the block
/// ([`copied_bits`]), else the one precision every scalar instruction of
/// the function names, when they agree.
///
/// # Arguments
///
/// * `program` - The image the function is decoded from.
/// * `analysis` - The functions, for the callees' entries.
/// * `factory` - Register-access facts.
/// * `bitness` - 32 or 64.
/// * `f` - The function.
/// * `preserving` - Per function, in order, whether it hands the register
///   back untouched.
/// * `reg` - The result register followed.
fn handed_back(
    program: &Program,
    analysis: &Analysis,
    factory: &mut InstructionInfoFactory,
    bitness: u32,
    f: &Function,
    preserving: &[bool],
    reg: ResultReg,
) -> Handed {
    if f.instr_count <= 1 && f.blocks.iter().all(|b| b.term == BlockTerm::Ret) {
        return Handed::UNKNOWN;
    }
    let idx = block_index(f);
    let Some(&entry) = idx.get(&f.entry) else {
        return Handed::UNKNOWN;
    };
    let preds = predecessors(f, &idx);
    let mut out = Handed::default();
    let mut stack: Vec<(usize, bool)> = Vec::new();
    for (b, blk) in f.blocks.iter().enumerate() {
        match blk.term {
            BlockTerm::Ret => stack.push((b, false)),
            BlockTerm::Jmp | BlockTerm::Cond | BlockTerm::Fall => {
                for s in blk.successors.iter().filter(|s| !idx.contains_key(s)) {
                    if analysis.function(*s).is_some() {
                        out.calls.push(*s);
                    } else {
                        out.unknown = true;
                    }
                }
            }
            BlockTerm::Indirect => out.unknown |= blk.successors.is_empty(),
            BlockTerm::Call | BlockTerm::Invalid => {}
        }
    }
    let preserves = |target: u64| {
        analysis
            .entry_index
            .get(&target)
            .is_some_and(|&i| preserving.get(i).copied().unwrap_or(false))
    };
    let frame_idiom = |i: &Instruction| {
        i.mnemonic() == Mnemonic::Mov
            && i.op0_kind() == OpKind::Register
            && i.op1_kind() == OpKind::Register
            && i.op0_register() == Register::RAX
            && i.op1_register() == Register::RSP
    };
    let mut seen = vec![[false; 2]; f.blocks.len()];
    while let Some((b, read)) = stack.pop() {
        let Some(blk) = f.blocks.get(b) else {
            continue;
        };
        if std::mem::replace(&mut seen[b][usize::from(read)], true) {
            continue;
        }
        let instrs = decode_block(program, bitness, blk);
        let skip = usize::from(b == entry && instrs.first().is_some_and(frame_idiom));
        let rest = instrs.get(skip..).unwrap_or_default();
        match exits::scan(factory, rest, &instrs, reg, &preserves) {
            Scan::Wrote(Writer::Call(callee), _) => out.calls.push(callee),
            Scan::Wrote(Writer::Indirect, _) => out.unknown = true,
            Scan::Wrote(Writer::Own(bits), later) => {
                out.own = true;
                out.bare |= !(read || later);
                out.float_bits.extend(bits);
            }
            Scan::Idle => out.nothing = true,
            Scan::Open(later) => {
                out.nothing |= b == entry;
                let read = read || later;
                stack.extend(preds.get(b).into_iter().flatten().map(|&p| (p, read)));
            }
        }
    }
    out.calls.sort_unstable();
    out.calls.dedup();
    if reg == ResultReg::Xmm0 && out.own && out.float_bits.is_empty() {
        let mut named: Vec<u8> = f
            .blocks
            .iter()
            .flat_map(|blk| decode_block(program, bitness, blk))
            .filter_map(|i| float_bits(&i))
            .collect();
        named.sort_unstable();
        named.dedup();
        if let [only] = named[..] {
            out.float_bits.push(only);
        }
    }
    out.float_bits.sort_unstable();
    out.float_bits.dedup();
    out
}

/// Tells whether a function's exits leave a float result in xmm0 rather
/// than an integer in rax, read off the writes nearest each exit.
///
/// From every `ret` the blocks are walked backwards, at most
/// [`RET_LANE_DEPTH`] blocks along a path: a write of xmm0 that is vector
/// work rather than a float result ([`scalar_float_write`]) decides
/// against a float, any other write of xmm0 met first is a vote for one,
/// and a path that runs out of blocks first says nothing. A call met
/// first hands back what its callee leaves, which [`float_results`]
/// weighs by the callee, so it says nothing here either: the error path
/// of `ceilf` ends calling the handler that returns its float. A write of
/// rax met first decides against a float unless xmm0 still holds the
/// float argument there ([`argument_kept`]): that path hands the argument
/// back, and the write is scratch (`ceil` compares the argument's bits
/// with a constant in rax). A path the code cannot take (a loop counter
/// left in rax on the way to a test that skips the division) lies beyond
/// the nearest writes, so the depth keeps it out. A store of xmm0 met
/// first (`movss [rdi], xmm0`) is where a `void` function put the value it
/// computed, so it decides against a float too. `vzeroupper` clears only
/// the upper lanes, so the walk looks past it.
///
/// # Arguments
///
/// * `program` - The image the function is decoded from.
/// * `factory` - Register-access facts.
/// * `bitness` - 32 or 64.
/// * `f` - The function.
///
/// # Returns
///
/// True when some exit's nearest result write is to xmm0 and nothing
/// decides against a float.
fn float_last(
    program: &Program,
    factory: &mut InstructionInfoFactory,
    bitness: u32,
    f: &Function,
) -> bool {
    let idx = block_index(f);
    let preds = predecessors(f, &idx);
    let mut stack: Vec<(usize, u8)> = f
        .blocks
        .iter()
        .enumerate()
        .filter(|(_, b)| b.term == BlockTerm::Ret)
        .map(|(i, _)| (i, 1))
        .collect();
    let mut seen = vec![false; f.blocks.len()];
    let (mut votes, mut scratch) = (false, Vec::new());
    while let Some((b, depth)) = stack.pop() {
        let Some(blk) = f.blocks.get(b) else {
            return false;
        };
        if std::mem::replace(&mut seen[b], true) {
            continue;
        }
        let instrs = decode_block(program, bitness, blk);
        let nearest = instrs.iter().rev().find(|i| {
            i.mnemonic() != Mnemonic::Vzeroupper
                && (is_call(i)
                    || rax_write(factory, i).is_some()
                    || stores_xmm0(factory, i)
                    || writes_xmm0(factory, i))
        });
        match nearest {
            None if depth < RET_LANE_DEPTH => {
                stack.extend(preds.get(b).into_iter().flatten().map(|&p| (p, depth + 1)));
            }
            None => {}
            Some(i) if is_call(i) => {}
            Some(i) if rax_write(factory, i).is_some() => scratch.push(i.ip()),
            Some(i) if stores_xmm0(factory, i) || !scalar_float_write(i) => return false,
            Some(_) => votes = true,
        }
    }
    votes && (scratch.is_empty() || argument_kept(program, factory, bitness, f, &scratch))
}

/// Tells whether xmm0 still holds the float the function was handed at
/// each of the rax writes `at`.
///
/// The function takes a float in xmm0 when it reads the register before
/// any path writes it, and the register still holds that float at a write
/// when no path from the entry to it writes xmm0 or calls. Whether some
/// path wrote it runs forward from the entry to a fixpoint, each block
/// taken at most twice, and the answer reads each block's last pass.
///
/// # Arguments
///
/// * `program` - The image the function is decoded from.
/// * `factory` - Register-access facts.
/// * `bitness` - 32 or 64.
/// * `f` - The function.
/// * `at` - Addresses of writes of rax in its body.
fn argument_kept(
    program: &Program,
    factory: &mut InstructionInfoFactory,
    bitness: u32,
    f: &Function,
    at: &[u64],
) -> bool {
    let idx = block_index(f);
    let mut touched: Vec<Option<bool>> = vec![None; f.blocks.len()];
    let mut passes = vec![(false, true); f.blocks.len()];
    let mut work: Vec<(usize, bool)> = idx.get(&f.entry).map(|&e| (e, false)).into_iter().collect();
    while let Some((b, mut t)) = work.pop() {
        let Some(blk) = f.blocks.get(b).filter(|_| touched[b] < Some(t)) else {
            continue;
        };
        touched[b] = Some(t);
        let (mut read, mut kept) = (false, true);
        for i in decode_block(program, bitness, blk) {
            read |= !t && reads_vector(factory, &i, Register::ZMM0);
            kept &= !t || !at.contains(&i.ip());
            t |= is_call(&i) || writes_xmm0(factory, &i);
        }
        passes[b] = (read, kept);
        for s in &blk.successors {
            work.extend(idx.get(s).map(|&s| (s, t)));
        }
    }
    passes.iter().any(|p| p.0) && passes.iter().all(|p| p.1)
}

/// Tells whether an instruction's write of a vector register is the kind
/// a float result ends with.
///
/// A scalar operation or conversion names its precision ([`float_bits`]);
/// a register move (`movaps`, `movapd`) hands one on and a zeroing
/// `xorps` or `xorpd` is `0.0`. A packed integer operation (`psubd`) or a
/// packed float one is vector work a `void` function stores.
///
/// # Arguments
///
/// * `i` - The instruction.
fn scalar_float_write(i: &Instruction) -> bool {
    if float_bits(i).is_some() {
        return true;
    }
    let regs = (0..i.op_count()).all(|k| i.op_kind(k) == OpKind::Register);
    match i.mnemonic() {
        Mnemonic::Movaps | Mnemonic::Movapd | Mnemonic::Vmovaps | Mnemonic::Vmovapd => regs,
        Mnemonic::Xorps | Mnemonic::Xorpd | Mnemonic::Vxorps | Mnemonic::Vxorpd => {
            regs && i.op_register(0) == i.op_register(i.op_count().saturating_sub(1))
        }
        _ => false,
    }
}

/// Tells whether an instruction writes memory from xmm0.
///
/// # Arguments
///
/// * `factory` - Register-access facts.
/// * `i` - The instruction.
fn stores_xmm0(factory: &mut InstructionInfoFactory, i: &Instruction) -> bool {
    let info = factory.info(i);
    info.used_memory().iter().any(|m| {
        matches!(
            m.access(),
            OpAccess::Write | OpAccess::CondWrite | OpAccess::ReadWrite
        )
    }) && info.used_registers().iter().any(|ur| {
        ur.register().full_register() == Register::ZMM0
            && matches!(ur.access(), OpAccess::Read | OpAccess::CondRead)
    })
}

/// Tells whether an instruction writes xmm0, in any lane.
///
/// # Arguments
///
/// * `factory` - Register-access facts.
/// * `i` - The instruction.
fn writes_xmm0(factory: &mut InstructionInfoFactory, i: &Instruction) -> bool {
    factory.info(i).used_registers().iter().any(|ur| {
        ur.register().full_register() == Register::ZMM0
            && matches!(
                ur.access(),
                OpAccess::Write
                    | OpAccess::ReadWrite
                    | OpAccess::CondWrite
                    | OpAccess::ReadCondWrite
            )
    })
}

/// The precision of the value a register-to-register vector copy moves,
/// read off the last instruction before it in the block that wrote its
/// source.
///
/// `addss xmm2, xmm3; movaps xmm0, xmm2` hands back a single: the copy
/// names no precision itself ([`float_bits`]), its source's writer does.
///
/// # Arguments
///
/// * `block` - The block's instructions.
/// * `copy` - The copy, one of them.
///
/// # Returns
///
/// The source writer's precision, or `None` when `copy` is no such copy
/// or no writer in the block names one.
fn copied_bits(block: &[Instruction], copy: &Instruction) -> Option<u8> {
    let moves = matches!(
        copy.mnemonic(),
        Mnemonic::Movaps
            | Mnemonic::Movapd
            | Mnemonic::Movups
            | Mnemonic::Movupd
            | Mnemonic::Vmovaps
            | Mnemonic::Vmovapd
    );
    if !moves || copy.op_count() != 2 || copy.op1_kind() != OpKind::Register {
        return None;
    }
    let src = copy.op1_register().full_register();
    let at = block.iter().position(|i| i.ip() == copy.ip())?;
    block[..at]
        .iter()
        .rev()
        .find(|i| i.op0_kind() == OpKind::Register && i.op0_register().full_register() == src)
        .and_then(float_bits)
}

/// The precision a scalar floating-point instruction names, in bits.
///
/// The SSE mnemonics spell it as their suffix: `addsd`, `cvtsi2sd` and
/// `movsd` leave a double, `addss`, `cvtsd2ss` and `movss` a single. A
/// bit move (`movaps`, `xorps`) names none.
///
/// # Arguments
///
/// * `i` - The instruction.
fn float_bits(i: &Instruction) -> Option<u8> {
    let name = format!("{:?}", i.mnemonic());
    if name.ends_with("sd") {
        Some(64)
    } else if name.ends_with("ss") {
        Some(32)
    } else {
        None
    }
}

/// Tells whether an instruction reads the value in a vector register.
///
/// A scalar move or conversion into the register (`movsd xmm0, xmm1`,
/// `cvtsi2sd xmm0, rax`) keeps its upper lanes, so the decoder counts it as
/// read, but the value in its low lane is replaced unread; `xorps xmm0,
/// xmm0` clears it whatever it held. Any other read is a read of the value.
///
/// # Arguments
///
/// * `factory` - Register-access facts.
/// * `i` - The instruction.
/// * `full` - The register by its widest name (`zmm0` for `xmm0`).
fn reads_vector(factory: &mut InstructionInfoFactory, i: &Instruction, full: Register) -> bool {
    let xmm0 = |r: Register| r.full_register() == full;
    let clears = matches!(
        i.mnemonic(),
        Mnemonic::Xorps | Mnemonic::Xorpd | Mnemonic::Pxor
    ) && i.op_count() == 2
        && i.op0_kind() == OpKind::Register
        && i.op1_kind() == OpKind::Register
        && i.op0_register() == i.op1_register();
    let replaces = matches!(
        i.mnemonic(),
        Mnemonic::Movsd
            | Mnemonic::Movss
            | Mnemonic::Cvtsi2sd
            | Mnemonic::Cvtsi2ss
            | Mnemonic::Cvtss2sd
            | Mnemonic::Cvtsd2ss
            | Mnemonic::Sqrtsd
            | Mnemonic::Sqrtss
            | Mnemonic::Roundsd
            | Mnemonic::Roundss
    ) && i.op0_kind() == OpKind::Register
        && xmm0(i.op0_register())
        && (1..i.op_count()).all(|k| i.op_kind(k) != OpKind::Register || !xmm0(i.op_register(k)));
    !replaces
        && !clears
        && factory.info(i).used_registers().iter().any(|ur| {
            xmm0(ur.register())
                && matches!(
                    ur.access(),
                    OpAccess::Read
                        | OpAccess::CondRead
                        | OpAccess::ReadWrite
                        | OpAccess::ReadCondWrite
                )
        })
}

/// The width of the floating-point result each function hands back in
/// xmm0, for the functions that hand one back.
///
/// A function whose declaration states its result
/// ([`typelib::declared_floats`]) hands back what it states, whatever its
/// body and its callers seem to say. Any other hands one back when three
/// things hold. Its body leaves one there: every exit's last write of xmm0
/// is its own instruction, or a call or jump to a function whose body does
/// or whose declaration states a `float` or `double`, and at least one
/// exit writes it; an exit that
/// writes nothing hands back the float argument that arrived in xmm0
/// (`ceil` returns a large argument as it came). A caller takes it: some
/// call site reads xmm0 before anything writes it, or hands it on by a
/// tail call to a function a caller takes it from ([`float_use`]). A
/// function nobody calls (an export, a callback reached through a
/// pointer) has no caller to ask, so its body alone answers: it takes the
/// float when its instructions write a scalar float to xmm0 nearest its
/// exits and nothing there decides against one ([`float_last`]). An
/// export's caller is not in this image, and dropping the value in xmm0
/// is a different result; packed vector work left there is not a float.
/// And no caller reads rax instead. A function whose every exit hands back
/// what a function so found leaves there forwards that float, whoever
/// reads it. The chains run to a fixpoint, capped at [`PASS_ROUNDS_MAX`]
/// rounds. The width is 32 bits when every write that names a precision
/// names a single, 64 otherwise; a body whose writes name none (`movd
/// xmm0, ecx`, a move of bits) takes the precision its callers read it at.
///
/// # Arguments
///
/// * `program` - The image, for the declarations.
/// * `analysis` - The functions, in the order of the other arguments.
/// * `uses` - What each one's call sites do with xmm0 ([`float_use`]).
/// * `floats` - What their exits hand back in xmm0 ([`handed_back`]).
/// * `read` - Whether some caller reads each one's rax.
/// * `last` - Whether each one's exits write xmm0 after rax ([`float_last`]).
///
/// # Returns
///
/// One width per function, in order, `None` for no float result.
fn float_results(
    program: &Program,
    analysis: &Analysis,
    uses: &[Vec<FloatUse>],
    floats: &[Handed],
    read: &[bool],
    last: &[bool],
) -> Vec<Option<u8>> {
    let declared = typelib::declared_floats(program, &analysis.functions);
    let callee = |c: &u64, known: &[Option<u8>]| {
        let j = *analysis.entry_index.get(c)?;
        declared[j].unwrap_or(known[j])
    };
    let mut body: Vec<Option<u8>> = declared.iter().map(|d| d.flatten()).collect();
    for _ in 0..PASS_ROUNDS_MAX {
        let mut changed = false;
        for (i, h) in floats.iter().enumerate() {
            if declared[i].is_some()
                || body[i].is_some()
                || h.unknown
                || (!h.own && h.calls.is_empty())
            {
                continue;
            }
            let callees: Option<Vec<u8>> = h.calls.iter().map(|c| callee(c, &body)).collect();
            let Some(callees) = callees else {
                continue;
            };
            let read: Vec<u8> = uses
                .get(i)
                .into_iter()
                .flatten()
                .filter_map(|site| match site {
                    FloatUse::Read(bits) => *bits,
                    FloatUse::Tail(_) | FloatUse::Dropped => None,
                })
                .collect();
            let named = !h.float_bits.is_empty() || !callees.is_empty();
            let single = if named {
                h.float_bits.iter().chain(&callees).all(|&b| b == 32)
            } else {
                !read.is_empty() && read.iter().all(|&b| b == 32)
            };
            body[i] = Some(if single { 32 } else { 64 });
            changed = true;
        }
        if !changed {
            break;
        }
    }
    let mut taken: Vec<bool> = uses
        .iter()
        .zip(floats)
        .zip(last)
        .zip(&declared)
        .map(|(((u, h), &last), d)| match d {
            Some(d) => d.is_some(),
            None => {
                u.iter().any(|site| matches!(site, FloatUse::Read(_)))
                    || (u.is_empty() && last && h.own)
            }
        })
        .collect();
    for _ in 0..PASS_ROUNDS_MAX {
        let mut changed = false;
        for (i, u) in uses.iter().enumerate() {
            if taken[i] {
                continue;
            }
            let handed_on = u.iter().any(|site| match site {
                FloatUse::Tail(caller) => analysis
                    .entry_index
                    .get(caller)
                    .is_some_and(|&c| taken[c] && body[c].is_some()),
                FloatUse::Read(_) | FloatUse::Dropped => false,
            });
            if handed_on {
                taken[i] = true;
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    let mut found: Vec<Option<u8>> = body
        .into_iter()
        .zip(taken)
        .zip(read)
        .zip(&declared)
        .map(|(((bits, taken), &read), d)| match d {
            Some(d) => *d,
            None => bits.filter(|_| !read && taken),
        })
        .collect();
    for _ in 0..PASS_ROUNDS_MAX {
        let mut changed = false;
        for (i, h) in floats.iter().enumerate() {
            if found[i].is_some()
                || declared[i].is_some()
                || read[i]
                || h.own
                || h.nothing
                || h.unknown
                || h.calls.is_empty()
            {
                continue;
            }
            let callees: Option<Vec<u8>> = h.calls.iter().map(|c| callee(c, &found)).collect();
            if let Some(callees) = callees {
                found[i] = Some(if callees.iter().all(|&b| b == 32) {
                    32
                } else {
                    64
                });
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    found
}

/// The width of the floating-point result each 32-bit function hands back
/// in `st0`, for the functions that hand one back.
///
/// A function hands one back when every exit leaves the x87 stack one value
/// deeper than the function took it ([`x87::flow`]), an exit that hands on
/// a callee's result counting what that callee leaves: a C runtime helper
/// by its name ([`x87::helper`]) or its body ([`x87::leaf_helper`]), or a
/// function so found. The chains of such callees run to a fixpoint, capped
/// at [`PASS_ROUNDS_MAX`] rounds. A function that takes more than a helper
/// does keeps a stack the walk lost track of, and says nothing. A value
/// left on the stack is the result whatever the callers do with rax
/// (`fnstsw ax` reads the float's compare through it). The value is
/// extended precision on the stack, so the width is a `double`'s.
///
/// # Arguments
///
/// * `program` - The image the functions are decoded from.
/// * `analysis` - The functions.
/// * `kept` - The functions that leave the x87 stack alone ([`x87_kept`]).
///
/// # Returns
///
/// One width per function, in order, `None` for no float result.
fn x87_results(program: &Program, analysis: &Analysis, kept: &BTreeSet<u64>) -> Vec<Option<u8>> {
    /// Width of the value an x87 register holds, as C declares it.
    const DOUBLE: u8 = 64;
    let imports: BTreeMap<u64, &str> = program
        .symbols
        .iter()
        .filter(|s| s.kind == SymbolKind::Import && s.addr != 0)
        .map(|s| (s.addr, s.name.as_str()))
        .collect();
    let leaves: Vec<Option<x87::Effect>> = striped_with(
        &analysis.functions,
        CLASSIFY_MIN,
        || RefCell::new(InstructionInfoFactory::new()),
        |factory, f| x87::leaf_helper(program, analysis, &mut factory.borrow_mut(), f),
    )
    .into_iter()
    .map(Option::flatten)
    .collect();
    let kind = |t: u64| {
        let name = analysis
            .function(t)
            .and_then(|f| f.name.as_deref())
            .or_else(|| imports.get(&t).copied());
        let leaf = || {
            leaves
                .get(*analysis.entry_index.get(&t)?)
                .copied()
                .flatten()
        };
        match name.and_then(x87::helper).or_else(leaf) {
            Some(e) => x87::Call::Helper(e),
            None if kept.contains(&t) => x87::Call::Kept,
            None => x87::Call::Plain,
        }
    };
    let callee = |i: &Instruction| Some(x87::named_target(i).map_or(x87::Call::Plain, kind));
    let flows: Vec<Option<x87::Flow>> = striped_with(
        &analysis.functions,
        CLASSIFY_MIN,
        || RefCell::new(InstructionInfoFactory::new()),
        |factory, f| {
            x87::flow(program, 32, &mut factory.borrow_mut(), f, &callee)
                .filter(|flow| flow.takes <= x87::OPERANDS_MAX)
        },
    )
    .into_iter()
    .map(Option::flatten)
    .collect();
    let mut net: Vec<Option<i32>> = vec![None; flows.len()];
    for _ in 0..PASS_ROUNDS_MAX {
        let mut changed = false;
        for (i, flow) in flows.iter().enumerate() {
            let Some(flow) = flow.as_ref().filter(|_| net[i].is_none()) else {
                continue;
            };
            let handed_on = |c: Option<u64>| match kind(c?) {
                x87::Call::Helper(e) => Some(i32::from(e.gives) - i32::from(e.takes)),
                x87::Call::Kept => Some(0),
                x87::Call::Plain => net[*analysis.entry_index.get(&c?)?],
            };
            if let Some(g) = flow.gives(&handed_on) {
                net[i] = Some(i32::from(g) - i32::from(flow.takes));
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    flows
        .iter()
        .zip(net)
        .map(|(flow, net)| (net? + i32::from(flow.as_ref()?.takes) == 1).then_some(DOUBLE))
        .collect()
}

/// Tells, per function, whether its body returns nothing.
///
/// A function returns nothing when it reaches a `ret` without writing rax
/// ([`Handed::nothing`]), or when some exit hands back what a callee left
/// in rax and that callee leaves nothing there itself, by its declared
/// signature or by these rules without a signature saying otherwise: a
/// call or a jump to a function that produces no value, or hands a float
/// back in xmm0 ([`float_results`]), produces none in rax. A function
/// with a value hands one back on every path, so one path handing back a
/// leftover says it has none, whatever its other exits write (Rust's drop
/// glue sets `eax` to test a discriminant, then calls a drop that
/// returns nothing on the other path).
/// The second rule runs to a fixpoint over chains of wrappers, capped at
/// [`PASS_ROUNDS_MAX`] rounds. A function some caller reads the result of,
/// one that hands rax back untouched and one that hands a float back in
/// xmm0 are never taken to return nothing.
///
/// # Arguments
///
/// * `analysis` - The functions, in the order of the other arguments.
/// * `facts` - Their call-site facts.
/// * `handed` - What their exits hand back ([`handed_back`]).
/// * `read` - Whether some caller reads each one's result.
/// * `floats` - The float result each hands back ([`float_results`]).
///
/// # Returns
///
/// One flag per function, in order.
fn produces_nothing(
    analysis: &Analysis,
    facts: &[Facts],
    handed: &[Handed],
    read: &[bool],
    floats: &[Option<u8>],
) -> Vec<bool> {
    let declared = |j: usize| {
        analysis
            .functions
            .get(j)
            .and_then(|f| f.signature.as_ref())
            .map(|s| s.ret == "void")
    };
    let open: Vec<bool> = facts
        .iter()
        .zip(read)
        .zip(floats)
        .map(|((facts, &read), float)| !read && !facts.preserves && float.is_none())
        .collect();
    let mut nothing: Vec<bool> = open
        .iter()
        .zip(handed)
        .map(|(&open, h)| open && h.nothing)
        .collect();
    for _ in 0..PASS_ROUNDS_MAX {
        let mut changed = false;
        for (i, h) in handed.iter().enumerate() {
            if nothing[i] || !open[i] {
                continue;
            }
            let void = |c: &u64| {
                analysis
                    .entry_index
                    .get(c)
                    .is_some_and(|&j| match declared(j) {
                        Some(void) => void,
                        None => nothing[j] || floats[j].is_some(),
                    })
            };
            if h.calls.iter().any(void) {
                nothing[i] = true;
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    nothing
}

/// Tells whether a function hands a result register back untouched.
///
/// On every path to one of its `ret`s nothing writes the register and
/// nothing is called, so a call to it is not a result and the caller's
/// value survives it: a stack-cookie check compares `rcx` with the cookie
/// and returns, jumping to a function that never returns on a mismatch,
/// and the double a caller computed in xmm0 before checking is still
/// there. Only functions of at most [`PRESERVE_MAX`] instructions are
/// checked, and a lone `ret` is a stub that says nothing about its
/// callers, as for its arity.
///
/// # Arguments
///
/// * `program` - The image the function is decoded from.
/// * `factory` - Register-access facts.
/// * `bitness` - 32 or 64.
/// * `f` - The function.
/// * `reg` - The result register.
fn preserves(
    program: &Program,
    factory: &mut InstructionInfoFactory,
    bitness: u32,
    f: &Function,
    reg: ResultReg,
) -> bool {
    let floor = match reg {
        ResultReg::Rdx => 0,
        ResultReg::Rax | ResultReg::Xmm0 => 1,
    };
    if f.instr_count <= floor || f.instr_count > PRESERVE_MAX {
        return false;
    }
    let Some(reaching) = ret_reaching(f) else {
        return false;
    };
    f.blocks
        .iter()
        .zip(&reaching)
        .filter(|(_, r)| **r)
        .all(|(blk, _)| {
            decode_block(program, bitness, blk)
                .iter()
                .all(|i| match reg {
                    ResultReg::Rax => !writes_rax(factory, i),
                    ResultReg::Rdx => !writes_rdx(factory, i),
                    ResultReg::Xmm0 => !is_call(i) && !writes_xmm0(factory, i),
                })
        })
}

/// Tells whether a function hands xmm0 back untouched ([`preserves`]).
///
/// # Arguments
///
/// * `program` - The image the function is decoded from.
/// * `f` - The function.
pub(crate) fn preserves_float(program: &Program, f: &Function) -> bool {
    let Some(bitness) = program.arch.bitness() else {
        return false;
    };
    let mut factory = InstructionInfoFactory::new();
    preserves(program, &mut factory, bitness, f, ResultReg::Xmm0)
}

/// Marks the blocks of a function that reach one of its `ret`s.
///
/// # Arguments
///
/// * `f` - The function.
///
/// # Returns
///
/// One flag per block, in order, or `None` when the function has no `ret`.
fn ret_reaching(f: &Function) -> Option<Vec<bool>> {
    let preds = predecessors(f, &block_index(f));
    let mut reaching = vec![false; f.blocks.len()];
    let mut stack: Vec<usize> = f
        .blocks
        .iter()
        .enumerate()
        .filter(|(_, b)| matches!(b.term, BlockTerm::Ret))
        .map(|(i, _)| i)
        .collect();
    if stack.is_empty() {
        return None;
    }
    while let Some(b) = stack.pop() {
        let Some(seen) = reaching.get_mut(b) else {
            continue;
        };
        if *seen {
            continue;
        }
        *seen = true;
        stack.extend(preds.get(b).into_iter().flatten().copied());
    }
    Some(reaching)
}

/// The direct calls a function makes on its way to a `ret`, when nothing
/// there touches the x87 stack.
///
/// # Arguments
///
/// * `program` - The image the function is decoded from.
/// * `factory` - Register-access facts.
/// * `bitness` - 32 or 64.
/// * `f` - The function.
///
/// # Returns
///
/// The callees, or `None` when an x87 instruction or a call through a
/// pointer lies on a path to a `ret`, the function never returns, or it is
/// an import's thunk.
fn x87_free_calls(
    program: &Program,
    factory: &mut InstructionInfoFactory,
    bitness: u32,
    f: &Function,
) -> Option<Vec<u64>> {
    if f.thunk.is_some() {
        return None;
    }
    let reaching = ret_reaching(f)?;
    let mut calls = Vec::new();
    for (blk, _) in f.blocks.iter().zip(&reaching).filter(|(_, r)| **r) {
        for i in decode_block(program, bitness, blk) {
            if x87::touches(factory, &i) {
                return None;
            }
            match i.flow_control() {
                FlowControl::Call => calls.push(i.near_branch_target()),
                FlowControl::IndirectCall => return None,
                FlowControl::Next
                | FlowControl::UnconditionalBranch
                | FlowControl::ConditionalBranch
                | FlowControl::IndirectBranch
                | FlowControl::Return
                | FlowControl::Interrupt
                | FlowControl::Exception
                | FlowControl::XbeginXabortXend => {}
            }
        }
    }
    Some(calls)
}

/// The functions that leave the x87 stack as their caller left it.
///
/// Such a function runs no x87 instruction on its way to a `ret`, and
/// every call it makes there goes straight to a function that leaves the
/// stack alone too, so a value a caller keeps on the stack across a call
/// to it is still there afterwards: a compiler that sees the whole program
/// keeps a `0.0` on the stack across a call to a string compare. Chains of
/// such calls run to a fixpoint, capped at [`PASS_ROUNDS_MAX`] rounds.
/// Built once per analysis.
///
/// # Arguments
///
/// * `program` - The image the functions are decoded from.
/// * `analysis` - The functions.
///
/// # Returns
///
/// The entries of the functions found.
pub(crate) fn x87_kept(program: &Program, analysis: &Analysis) -> Arc<BTreeSet<u64>> {
    analysis.derived.get_or_build("x87_kept", (), || {
        let Some(bitness) = program.arch.bitness() else {
            return BTreeSet::new();
        };
        let calls: Vec<(u64, Vec<u64>)> = striped_with(
            &analysis.functions,
            CLASSIFY_MIN,
            || RefCell::new(InstructionInfoFactory::new()),
            |factory, f| {
                x87_free_calls(program, &mut factory.borrow_mut(), bitness, f)
                    .map(|calls| (f.entry, calls))
            },
        )
        .into_iter()
        .flatten()
        .flatten()
        .collect();
        let mut kept = BTreeSet::new();
        for _ in 0..PASS_ROUNDS_MAX {
            let before = kept.len();
            for (entry, callees) in &calls {
                if callees.iter().all(|c| kept.contains(c)) {
                    kept.insert(*entry);
                }
            }
            if kept.len() == before {
                break;
            }
        }
        kept
    })
}

/// What a 32-bit callee does with the vector registers across a call.
///
/// The standard 32-bit conventions pass floats on the stack and return
/// them in `st0`, and every vector register is the callee's to clobber;
/// the C runtime's SSE2 helpers, and functions a whole-program compiler
/// gives a convention of its own, take their floats in `xmm0` and up and
/// hand the result back in `xmm0`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub(crate) struct Sse {
    /// A bit per vector register the callee takes an argument in, `xmm0`
    /// the lowest.
    pub(crate) args: u8,
    /// The callee hands a float back in `xmm0`.
    pub(crate) returns: bool,
}

/// What the C runtime SSE2 helper a name names does with the vector
/// registers.
///
/// `__libm_sse2_*` take their double or float in `xmm0`, `pow` and `atan2`
/// a second in `xmm1`, and return in `xmm0`; `__ltod3` and `__ultod3` turn
/// the integer in `edx:ecx` into a double in `xmm0`; `__dtol3` and its kin
/// turn the float in `xmm0` into an integer in `edx:eax`.
///
/// # Arguments
///
/// * `name` - A function or import name, `dll!` prefix and leading
///   underscores allowed.
///
/// # Returns
///
/// The helper's use, or `None` for any other name.
pub(crate) fn sse_helper(name: &str) -> Option<Sse> {
    let bare = super::bare_name(name).trim_start_matches('_');
    if let Some(rest) = bare.strip_prefix("libm_sse2_") {
        let two = rest.starts_with("pow") || rest.starts_with("atan2");
        return Some(Sse {
            args: if two { 0b11 } else { 0b1 },
            returns: true,
        });
    }
    match bare {
        "ltod3" | "ultod3" => Some(Sse {
            args: 0,
            returns: true,
        }),
        "dtol3" | "dtoui3" | "dtoul3" | "ftol3" | "ftoui3" | "ftoul3" => Some(Sse {
            args: 0b1,
            returns: false,
        }),
        _ => None,
    }
}

/// What a 32-bit function's body does with the vector registers ([`Sse`]).
///
/// It takes an argument in each of `xmm0` to `xmm5`, as many as
/// `__vectorcall` passes, it reads on some path from its entry before
/// writing it, walking at most [`VECTOR_SCAN_MAX`] blocks: the convention
/// leaves nothing in them at a call, and after a call it makes they hold
/// what that call left. It hands a float back
/// in `xmm0` when its body leaves one there and some caller reads it right
/// after the call ([`float_use`]): a body that uses `xmm0` for scratch and
/// returns in rax leaves its last write there too, but no caller reads
/// what the call clobbered. A caller may read rax as well, since a
/// compiler that knows a helper keeps `eax` keeps its own value there
/// across the call. The body leaves one when it hands none back on the x87 stack, at least
/// one exit writes `xmm0`, and every exit's last write of it is the
/// function's own or a call to a helper that returns there
/// ([`sse_helper`]); an exit that writes nothing hands back the argument
/// it was given.
///
/// # Arguments
///
/// * `program` - The image the function is decoded from.
/// * `analysis` - The functions, for the callees' names.
/// * `f` - The function.
pub(crate) fn sse_call(program: &Program, analysis: &Analysis, f: &Function) -> Sse {
    let Some(bitness) = program.arch.bitness() else {
        return Sse::default();
    };
    let mut factory = InstructionInfoFactory::new();
    let vectors = [
        Register::ZMM0,
        Register::ZMM1,
        Register::ZMM2,
        Register::ZMM3,
        Register::ZMM4,
        Register::ZMM5,
    ];
    let idx = block_index(f);
    let mut open_at: Vec<u8> = vec![0; f.blocks.len()];
    let mut work: Vec<usize> = Vec::new();
    if let Some(&entry) = idx.get(&f.entry) {
        open_at[entry] = ALL_VECTORS;
        work.push(entry);
    }
    let (mut read, mut fuel) = (0u8, VECTOR_SCAN_MAX);
    while let Some(b) = work.pop() {
        let Some(blk) = f.blocks.get(b) else {
            continue;
        };
        if fuel == 0 {
            break;
        }
        fuel -= 1;
        let mut open = open_at[b];
        for i in decode_block(program, bitness, blk) {
            if is_call(&i) {
                open = 0;
                continue;
            }
            for (k, &full) in vectors.iter().enumerate() {
                let bit = 1u8 << k;
                if open & bit != 0 && reads_vector(&mut factory, &i, full) {
                    read |= bit;
                }
            }
            for ur in factory.info(&i).used_registers() {
                if let Some(k) = vectors
                    .iter()
                    .position(|v| *v == ur.register().full_register())
                    && matches!(ur.access(), OpAccess::Write | OpAccess::ReadWrite)
                {
                    open &= !(1u8 << k);
                }
            }
        }
        for &s in blk.successors.iter().filter_map(|s| idx.get(s)) {
            if open_at[s] | open != open_at[s] {
                open_at[s] |= open;
                work.push(s);
            }
        }
    }
    let h = handed_back(
        program,
        analysis,
        &mut factory,
        bitness,
        f,
        &[],
        ResultReg::Xmm0,
    );
    let helper = |c: &u64| {
        analysis
            .function(*c)
            .and_then(|g| g.name.as_deref())
            .and_then(sse_helper)
            .is_some_and(|s| s.returns)
    };
    let body = f.ret_float.is_none()
        && !h.unknown
        && (h.own || !h.calls.is_empty())
        && h.calls.iter().all(helper);
    let returns = body
        && analysis
            .xrefs_to(f.entry)
            .iter()
            .filter(|s| s.kind == RefKind::Call)
            .any(|s| {
                matches!(
                    float_use(program, analysis, &mut factory, bitness, s.va, &[]),
                    FloatUse::Read(_)
                )
            });
    Sse {
        args: read,
        returns,
    }
}

/// Width in bits of a read of the return register.
///
/// # Arguments
///
/// * `r` - The register read (`al`, `ah`, `ax`, `eax` or `rax`).
fn read_bits(r: Register) -> u8 {
    match r.size() {
        1 if r == Register::AH => 16,
        1 => 8,
        2 => 16,
        4 => 32,
        _ => 64,
    }
}

/// Lane in bits a write of the return register defines.
///
/// A 32-bit write zero-extends, so the register holds a 32-bit value: a
/// function whose every exit writes `eax` returns that wide.
///
/// # Arguments
///
/// * `r` - The register written (`al`, `ah`, `ax`, `eax` or `rax`).
fn write_bits(r: Register) -> u8 {
    match r.size() {
        1 if r == Register::AH => 16,
        1 => 8,
        2 => 16,
        4 => 32,
        _ => 64,
    }
}

/// Width in bits of the value a function's own `ret`s hand back through rax.
///
/// The last write of rax reaching each `ret` decides, as [`lane_before`]
/// does for the decompiled function itself: when every returning path ends
/// its rax writes with a byte (or word) write, or with a value that fits
/// one ([`value_lane`]), the function returns that lane; a returning block
/// entered only when rax is zero (`test eax, eax; je`) returns a byte along
/// that edge ([`zero_edge`]). Only the returning blocks and their
/// predecessors, up to [`RET_LANE_DEPTH`] back, are decoded.
///
/// # Arguments
///
/// * `program` - The image the function is decoded from.
/// * `factory` - Register-access facts.
/// * `bitness` - 32 or 64.
/// * `f` - The function.
///
/// # Returns
///
/// 8 or 16 for a narrow result, 64 for the whole register (a function
/// without a `ret` included).
fn body_lane(
    program: &Program,
    factory: &mut InstructionInfoFactory,
    bitness: u32,
    f: &Function,
) -> u8 {
    let preds = predecessors(f, &block_index(f));
    let mut code: BTreeMap<usize, Vec<Instruction>> = BTreeMap::new();
    let mut known = |b: usize, from: Option<usize>| -> Option<u8> {
        match from {
            None => {
                let instrs = decoded(&mut code, program, bitness, f, b);
                last_rax_write(factory, instrs).map(|(_, value)| value)
            }
            Some(p) => {
                let target = f.blocks.get(b)?.start;
                let instrs = decoded(&mut code, program, bitness, f, p);
                zero_edge(instrs, target).then_some(8)
            }
        }
    };
    let lane = f
        .blocks
        .iter()
        .enumerate()
        .filter(|(_, b)| matches!(b.term, BlockTerm::Ret))
        .map(|(b, _)| lane_before(b, &mut known, &preds, RET_LANE_DEPTH))
        .max()
        .unwrap_or(0);
    if lane == 0 { 64 } else { lane }
}

/// Width every write of rax in the function stays at or below, when that
/// is at most a byte or a word.
///
/// A partial write merges into what the caller had in `rax`, so a caller
/// reading the whole register after the call reads its own value with the
/// lane merged in; one full write anywhere (`mov eax, 0x50` zeroes the
/// upper half, `lea rax, [rsp+0xf]` puts a callee value there) or a call
/// replaces those bits with the callee's own, and no caller bit survives.
/// A function that writes rax nowhere passes it through whole, which
/// [`preserves`] states instead.
///
/// # Arguments
///
/// * `program` - The image the function is decoded from.
/// * `factory` - Register-access facts.
/// * `bitness` - 32 or 64.
/// * `f` - The function.
///
/// # Returns
///
/// The widest lane written, 8 or 16, or 64 when some write (or a call)
/// covers the register fully or nothing writes it.
fn body_write(
    program: &Program,
    factory: &mut InstructionInfoFactory,
    bitness: u32,
    f: &Function,
) -> u8 {
    let mut lane = 0u8;
    let mut code: BTreeMap<usize, Vec<Instruction>> = BTreeMap::new();
    for b in 0..f.blocks.len() {
        for i in decoded(&mut code, program, bitness, f, b) {
            if is_call(i) {
                return 64;
            }
            let Some(r) = rax_write(factory, i) else {
                continue;
            };
            lane = lane.max(write_bits(r));
            if lane > 16 {
                return 64;
            }
        }
    }
    if lane == 0 { 64 } else { lane }
}

/// Decodes block `b` of `f` once, keeping it in `code`; one decoder runs
/// over the block's bytes.
///
/// # Arguments
///
/// * `code` - Blocks decoded so far, by index.
/// * `program` - The image.
/// * `bitness` - 32 or 64.
/// * `f` - The function.
/// * `b` - Block index; one past the blocks decodes to nothing.
fn decoded<'a>(
    code: &'a mut BTreeMap<usize, Vec<Instruction>>,
    program: &Program,
    bitness: u32,
    f: &Function,
    b: usize,
) -> &'a [Instruction] {
    code.entry(b).or_insert_with(|| {
        f.blocks
            .get(b)
            .map_or_else(Vec::new, |blk| decode_block(program, bitness, blk))
    })
}

/// Tells whether the edge from a block into `target` is taken only when rax
/// is zero.
///
/// The block must end `test eax, eax` (or `cmp eax, 0`, either width)
/// followed by `je target`, or by `jne` elsewhere falling through into
/// `target`.
///
/// # Arguments
///
/// * `instrs` - The predecessor block.
/// * `target` - Start of the block the edge enters.
fn zero_edge(instrs: &[Instruction], target: u64) -> bool {
    let [.., test, jump] = instrs else {
        return false;
    };
    let whole = |r: Register| r.full_register() == Register::RAX && r.size() >= 4;
    let tests_rax = match test.mnemonic() {
        Mnemonic::Test => {
            test.op0_kind() == OpKind::Register
                && test.op1_kind() == OpKind::Register
                && test.op0_register() == test.op1_register()
                && whole(test.op0_register())
        }
        Mnemonic::Cmp => {
            test.op0_kind() == OpKind::Register
                && whole(test.op0_register())
                && is_imm(test.op1_kind())
                && test.immediate(1) == 0
        }
        _ => false,
    };
    if !tests_rax || jump.flow_control() != FlowControl::ConditionalBranch {
        return false;
    }
    match jump.condition_code() {
        ConditionCode::e => jump.near_branch_target() == target,
        ConditionCode::ne => jump.next_ip() == target,
        _ => false,
    }
}

/// Lane of the last write of rax in a block, scanning from its end.
///
/// # Arguments
///
/// * `factory` - Register-access facts.
/// * `instrs` - The block.
///
/// # Returns
///
/// The lane the last writer writes and the lane its value fits
/// ([`value_lane`]), both 64 for a call, `None` when nothing in the block
/// writes rax.
pub(super) fn last_rax_write(
    factory: &mut InstructionInfoFactory,
    instrs: &[Instruction],
) -> Option<(u8, u8)> {
    instrs.iter().rev().find_map(|i| {
        if is_call(i) {
            return Some((64, 64));
        }
        rax_write(factory, i).map(|r| {
            let written = write_bits(r);
            (written, value_lane(i, written))
        })
    })
}

/// Lane in bits the value an instruction leaves in rax fits.
///
/// A constant moved in, a zero from `xor eax, eax`, a zero-extended byte
/// or word (`movzx`), or an `and` with a small mask fits the lane its value
/// names, whatever width the instruction writes; the result of anything
/// else is as wide as the write. Reading such a value as a byte or word is
/// the value itself, so a caller may drop the mask.
///
/// # Arguments
///
/// * `i` - The instruction writing rax.
/// * `written` - The lane it writes ([`write_bits`]).
fn value_lane(i: &Instruction, written: u8) -> u8 {
    let immediate = is_imm(i.op1_kind());
    let bound = match i.mnemonic() {
        Mnemonic::Mov | Mnemonic::And if immediate => Some(i.immediate(1)),
        Mnemonic::Xor
            if i.op1_kind() == OpKind::Register && i.op0_register() == i.op1_register() =>
        {
            Some(0)
        }
        Mnemonic::Movzx => {
            let bytes = match i.op1_kind() {
                OpKind::Register => i.op1_register().size(),
                OpKind::Memory => i.memory_size().size(),
                _ => 8,
            };
            Some(match bytes {
                1 => 0xff,
                2 => 0xffff,
                _ => u64::MAX,
            })
        }
        _ => None,
    };
    match bound {
        Some(c) if c <= 0xff => written.min(8),
        Some(c) if c <= 0xffff => written.min(16),
        _ => written,
    }
}

/// Lane of the last rax write reaching the end of block `b`.
///
/// The block's own write wins; otherwise the widest among its predecessors'
/// up to `depth` blocks back, each predecessor's edge into `b` fixing the
/// lane itself when it can; a block without predecessors, or past the
/// depth, is the whole register.
///
/// # Arguments
///
/// * `b` - Block index.
/// * `known` - `known(b, None)` is the lane of block `b`'s own last rax
///   write; `known(b, Some(p))` the lane the edge from `p` into `b` fixes.
/// * `preds` - Predecessor block indices per block.
/// * `depth` - Blocks left to follow.
pub(super) fn lane_before(
    b: usize,
    known: &mut dyn FnMut(usize, Option<usize>) -> Option<u8>,
    preds: &[Vec<usize>],
    depth: u8,
) -> u8 {
    if let Some(w) = known(b, None) {
        return w;
    }
    let Some(ps) = preds.get(b).filter(|p| !p.is_empty()) else {
        return 64;
    };
    if depth == 0 {
        return 64;
    }
    let mut lane = 0;
    for &p in ps {
        let through = match known(b, Some(p)) {
            Some(w) => w,
            None => lane_before(p, known, preds, depth - 1),
        };
        lane = lane.max(through);
    }
    lane
}

/// Classifies what the code after the call at `call_va` does with `rax`.
///
/// Every path from the return address is scanned, down both sides of each
/// conditional branch and through each jump within the caller, until rax is
/// read whole, fully written, clobbered by another call, or handed on by a
/// `ret` (a narrower read goes on, so the widest read is the width);
/// a path ending in `int3` or `ud2` reads nothing. A path that leaves the
/// caller's blocks, branches indirectly, or runs past [`SCAN_MAX`]
/// instructions is not followed, and nor are more than [`PATHS_MAX`]
/// paths. An instruction is checked for a read of rax before anything
/// else, so `call [rax+0x10]` and `jmp rax` use the value.
///
/// # Arguments
///
/// * `program` - The image.
/// * `analysis` - For the caller's block bounds.
/// * `factory` - Reused instruction-info factory.
/// * `bitness` - Decoder bitness.
/// * `call_va` - Address of the call instruction.
/// * `reg` - The result register the caller's use of is classified, `rax`
///   or `rdx`.
///
/// # Returns
///
/// [`Site::Used`] when some path reads the value (with the widest read),
/// else [`Site::Unknown`] when some path could not be followed, else
/// [`Site::Tail`] when some path returns it, else [`Site::Dead`].
fn classify(
    program: &Program,
    analysis: &Analysis,
    factory: &mut InstructionInfoFactory,
    bitness: u32,
    call_va: u64,
    reg: Register,
    rdx_args: &[bool],
) -> Site {
    let Some(caller) = analysis.function_at(call_va) else {
        return Site::Unknown;
    };
    let Some(call) = decode_at(program, bitness, call_va) else {
        return Site::Unknown;
    };
    let in_caller = |va: u64| caller.blocks.iter().any(|b| b.start == va);
    let mut used: Option<u8> = None;
    let mut unknown = false;
    let mut tail = false;
    let mut work = vec![call.next_ip()];
    let mut entered: Vec<u64> = Vec::new();
    while let Some(start) = work.pop() {
        if entered.contains(&start) {
            continue;
        }
        if entered.len() == PATHS_MAX {
            unknown = true;
            break;
        }
        entered.push(start);
        let Some(mut block) = caller
            .blocks
            .iter()
            .find(|b| b.start <= start && start < b.end)
        else {
            unknown = true;
            continue;
        };
        let mut va = start;
        let mut ended = false;
        for _ in 0..SCAN_MAX {
            if va >= block.end {
                let Some(next) = caller.blocks.iter().find(|b| b.start == va) else {
                    break;
                };
                block = next;
            }
            let Some(instr) = decode_at(program, bitness, va) else {
                break;
            };
            let mut read = None;
            let mut full_write = false;
            for ur in factory.info(&instr).used_registers() {
                if ur.register().full_register() != reg {
                    continue;
                }
                match ur.access() {
                    OpAccess::Read
                    | OpAccess::CondRead
                    | OpAccess::ReadWrite
                    | OpAccess::ReadCondWrite => {
                        read = read.max(Some(read_bits(ur.register())));
                    }
                    OpAccess::Write | OpAccess::CondWrite => {
                        full_write |= full_names(reg).contains(&ur.register());
                    }
                    OpAccess::None | OpAccess::NoMemAccess => {}
                }
            }
            ended = true;
            if let Some(bits) = read {
                used = used.max(Some(bits));
                if bits >= 64 {
                    break;
                }
            }
            if full_write {
                break;
            }
            let target = instr.near_branch_target();
            match instr.flow_control() {
                FlowControl::Return => tail = true,
                FlowControl::Call | FlowControl::IndirectCall | FlowControl::Exception => {
                    if bitness == 64
                        && reg == Register::RDX
                        && target != 0
                        && let Some(&c) = analysis.entry_index.get(&target)
                        && rdx_args[c]
                    {
                        used = used.max(Some(64));
                    }
                }
                FlowControl::Interrupt => unknown |= instr.mnemonic() != Mnemonic::Int3,
                FlowControl::Next => {
                    va = instr.next_ip();
                    ended = false;
                    continue;
                }
                FlowControl::UnconditionalBranch if in_caller(target) => work.push(target),
                FlowControl::ConditionalBranch if in_caller(target) => {
                    work.push(target);
                    work.push(instr.next_ip());
                }
                FlowControl::UnconditionalBranch
                | FlowControl::ConditionalBranch
                | FlowControl::IndirectBranch
                | FlowControl::XbeginXabortXend => unknown = true,
            }
            break;
        }
        unknown |= !ended;
    }
    if let Some(bits) = used {
        Site::Used(bits)
    } else if unknown {
        Site::Unknown
    } else if tail {
        Site::Tail(caller.entry)
    } else {
        Site::Dead
    }
}

/// The names whose write covers the whole of `reg`: its own and its
/// 32-bit half's, the widths a compiler writes a full value in.
///
/// # Arguments
///
/// * `reg` - The result register.
fn full_names(reg: Register) -> [Register; 2] {
    match reg {
        Register::RDX => [Register::RDX, Register::EDX],
        _ => [Register::RAX, Register::EAX],
    }
}

/// Tells whether a function reads the argument the x64 convention passes in
/// `rdx`: something reads the register before anything writes it in full.
///
/// A callee that never reads its second argument was not handed the value
/// the lane carried to its boundary, so a call to it is no read of the
/// caller's `rdx`; one that does read it was, whether the read names a
/// value the caller set or one an earlier callee left there. A variadic
/// function's store of `rdx` with its other variable arguments
/// ([`rdx_variable`]) is no such read: a caller passes the register only
/// when it sets it.
///
/// # Arguments
///
/// * `program` - The image the body is decoded from.
/// * `factory` - Reused instruction-info factory.
/// * `bitness` - Decoder bitness.
/// * `f` - The function whose body is walked.
fn reads_rdx_arg(
    program: &Program,
    factory: &mut InstructionInfoFactory,
    bitness: u32,
    f: &Function,
) -> bool {
    /// Most instructions walked in one body, so one huge function cannot
    /// make the pass slow.
    const BODY_MAX: usize = 256;
    let mut walked = 0;
    for b in &f.blocks {
        let mut va = b.start;
        while va < b.end && walked < BODY_MAX {
            let Some(instr) = decode_at(program, bitness, va) else {
                return false;
            };
            walked += 1;
            va = instr.next_ip();
            let mut read = false;
            let mut wrote = false;
            for ur in factory.info(&instr).used_registers() {
                if ur.register().full_register() != Register::RDX {
                    continue;
                }
                match ur.access() {
                    OpAccess::Read
                    | OpAccess::CondRead
                    | OpAccess::ReadWrite
                    | OpAccess::ReadCondWrite => read = true,
                    OpAccess::Write | OpAccess::CondWrite => {
                        wrote |= full_names(Register::RDX).contains(&ur.register());
                    }
                    OpAccess::None | OpAccess::NoMemAccess => {}
                }
            }
            if read {
                return !rdx_variable(program, bitness, f);
            }
            if wrote {
                return false;
            }
            if matches!(
                instr.flow_control(),
                FlowControl::Call | FlowControl::IndirectCall
            ) {
                return false;
            }
        }
    }
    false
}

/// Tells whether `rdx` is one of a variadic function's variable arguments.
///
/// Its prologue keeps the argument registers from a fixed count on for
/// `va_arg` ([`vararg_fixed`](super::decompile::lift::vararg_fixed)), and
/// that count does not reach the slot `rdx` passes.
///
/// # Arguments
///
/// * `program` - The image the body is decoded from.
/// * `bitness` - Decoder bitness.
/// * `f` - The function.
fn rdx_variable(program: &Program, bitness: u32, f: &Function) -> bool {
    use super::decompile::{abi, lift};
    /// Most instructions of a prologue read before its first call.
    const PROLOGUE_MAX: usize = 64;
    let mut prologue = Vec::new();
    'blocks: for b in &f.blocks {
        let mut va = b.start;
        while va < b.end && prologue.len() < PROLOGUE_MAX {
            let Some(i) = decode_at(program, bitness, va).filter(|i| !is_call(i)) else {
                break 'blocks;
            };
            va = i.next_ip();
            prologue.push(i);
        }
    }
    lift::vararg_fixed(program, bitness, &prologue)
        .zip(abi::conv(program, bitness).slot(Register::RDX))
        .is_some_and(|(fixed, rdx)| fixed <= rdx)
}
