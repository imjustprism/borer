//! A counted loop that compares a few bits of a product.
//!
//! `borer://solve` tries the constants a check compares against. A check
//! that publishes the top bits of `secret * k[i]` each iteration has no
//! such constant: the expected digit is computed, and another input/output
//! sample does not add a relation. The shape is a hidden-number problem,
//! which lattice reduction solves and sampling does not. This report names
//! the loop, the bit extract, the table and the loop-invariant multiplicand
//! so that is the next step, and it does not itself reduce the lattice.

use super::*;
use crate::isa::x86::{ConditionCode, RflagsBits};
use crate::num::{lo32, sext32};
use std::collections::VecDeque;

/// Most partial checks one function's report lists.
const CHECKS_MAX: usize = 8;

/// Instructions after a shift still read as the same extract.
const EXTRACT_WINDOW: usize = 16;

/// Instructions of one callee whose stores are folded into the caller.
const CALLEE_INSTRS_MAX: usize = 800;

/// Blocks one walk will visit, past which the cycle is not worth a report.
const WALK_MAX: usize = 4096;

/// A value a straight-line read of moves and adds can name.
#[derive(Clone, Copy)]
enum Know {
    /// A concrete integer.
    Val(u64),
    /// The loop counter, not a particular iteration's value.
    Counter,
    /// The value last written to `[rsp+disp]`, whether or not that value is known.
    Slot(i64),
    /// A register the function was entered with and has not overwritten.
    Arg(Register),
}

/// One straight-line fact about the registers, the frame and the statics.
struct Facts {
    /// What each whole register holds.
    regs: BTreeMap<Register, Know>,
    /// What each `[rsp+disp]` slot holds.
    slots: BTreeMap<i64, Know>,
    /// A store to a static address, the later one winning when they overlap.
    statics: BTreeMap<u64, Static>,
    /// How many static stores have been recorded, so a later one wins.
    seq: u32,
}

/// A value written to a static address.
#[derive(Clone, Copy)]
struct Static {
    /// Bytes written.
    width: u32,
    /// The little-endian value.
    value: u64,
    /// The order the store was seen in; a higher one is later.
    seq: u32,
}

/// What the folder reads and does not change as it walks.
struct Env<'a> {
    /// The loaded image.
    p: &'a Program,
    /// The analysis, for a callee's instructions.
    a: &'a Analysis,
    /// Decoder bitness.
    bitness: u32,
    /// Registers a call destroys.
    volatile: &'a [Register],
    /// Registers a reported cycle counts with.
    counters: &'a [Register],
}

/// One back-edge cycle: the blocks reachable from the header that can
/// also get back to it.
struct Cycle {
    /// The back edge's target.
    head: u64,
    /// Block starts on the cycle, the header included.
    body: BTreeSet<u64>,
}

/// The counter a cycle compares, and what it is compared with.
struct Counter {
    /// The register that is incremented.
    reg: Register,
    /// The immediate it is compared with, when the compare names one.
    imm: Option<u64>,
    /// The compare instruction, so a register bound can be filled in later.
    cmp_at: u64,
    /// The compare's other register, when the bound is not an immediate.
    bound_reg: Option<Register>,
    /// The exiting branch is `jge` or `jae`, so a counter from zero runs
    /// `bound` times.
    ge_exit: bool,
    /// Some instruction outside the cycle writes zero to the register.
    from_zero: bool,
}

/// A shift whose result is compared to a byte of a table.
struct Extract {
    /// The shift.
    at: u64,
    /// `shr` or `shrd`.
    how: &'static str,
    /// The immediate count, when the shift names one.
    imm: Option<u32>,
    /// The register holding the count, when it does not.
    count_reg: Option<Register>,
    /// The compare.
    cmp_at: u64,
    /// The instruction at which the table base is still in its register.
    resolve_at: u64,
    /// The table's base register, or [`Register::None`] for an ip-relative table.
    base: Register,
    /// The ip-relative table address, when the operand is ip-relative.
    ip_table: Option<u64>,
    /// Displacement added to the base.
    disp: i64,
    /// The index register.
    index: Register,
}

/// What the report says about one loop.
struct Check {
    /// The cycle.
    cycle: Cycle,
    /// Its counter.
    counter: Counter,
    /// The extract.
    extract: Extract,
    /// Stack slots the cycle writes.
    stored: BTreeSet<i64>,
    /// Whole registers the cycle writes, a call's volatile registers included.
    written: BTreeSet<Register>,
    /// The bound, once the scan has folded a register.
    bound: Option<u64>,
    /// The resolved shift count, masked to the architecture's count width.
    shift: Option<u32>,
    /// The table address, when the base folded to one.
    table: Option<u64>,
    /// Whether the index register is the counter.
    index_is_counter: bool,
    /// Loop-invariant multiplicands.
    secrets: BTreeSet<String>,
}

/// What one callee returns and what it stores to static addresses.
#[derive(Clone)]
struct Callee {
    /// `rax` at its `ret`.
    ret: Option<Know>,
    /// Its static stores.
    statics: BTreeMap<u64, Static>,
}

/// Reports the partial product checks in one function.
///
/// A check is a cycle that increments a register, compares a shift or
/// `shrd` of a multiplied value to a byte loaded through an index, and
/// multiplies by something the cycle does not overwrite. The report names
/// each of those. It does not sample the function and it does not run a
/// lattice reduction: both of those are the wrong tool once the relations
/// are written down, and the reduction is not a disassembler.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `a` - The analysis.
/// * `o` - User names.
/// * `spec` - The function's address or name.
///
/// # Errors
///
/// When the architecture is not x86, the address does not resolve or is
/// in no function, or the function has no partial product check. The last
/// of those is an error rather than a `#` line, so a client cannot read
/// "nothing here" as a check it found.
///
/// # Returns
///
/// The report.
pub fn partial_tsv(p: &Program, a: &Analysis, o: &Overlay, spec: &str) -> Result<String, String> {
    x86_only(p, "partial")?;
    let start = locate(a, o, spec).ok_or_else(|| unresolved(spec))?;
    let f = a
        .function_at(start)
        .ok_or_else(|| format!("no function contains {start:#x}"))?;
    let bitness = p.arch.bitness().unwrap_or(64);
    let checks = checks_of(p, a, f, bitness);
    if checks.is_empty() {
        return Err(format!(
            "no partial product check in {}",
            short_name(a, o, f.entry)
        ));
    }
    Ok(render_checks(a, o, f, &checks))
}

/// The next step for a function whose check is a hidden-number problem.
///
/// The summary and `borer://solve` prefix it with `# next:`. `None` when
/// the function has no partial product check, or has one whose multiplicand
/// was not shown to be loop-invariant: that is not yet this shape.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `a` - The analysis.
/// * `o` - User names.
/// * `entry` - The function's entry.
///
/// # Returns
///
/// The step, or `None` when the shape is absent.
pub(super) fn partial_hint(p: &Program, a: &Analysis, o: &Overlay, entry: u64) -> Option<String> {
    let report = partial_tsv(p, a, o, &format!("{entry:#x}")).ok()?;
    report.contains("hidden number problem").then(|| {
        format!(
            "borer://partial/{entry:#x} (a counted loop compares a few bits of a product: lattice, not more samples)"
        )
    })
}

/// The checks in one function, at most [`CHECKS_MAX`].
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `a` - The analysis.
/// * `f` - The function.
/// * `bitness` - Decoder bitness.
///
/// # Returns
///
/// The checks, filled in by one forward scan.
fn checks_of(p: &Program, a: &Analysis, f: &Function, bitness: u32) -> Vec<Check> {
    let instrs = function_instructions(p, a, f.entry);
    if instrs.is_empty() {
        return Vec::new();
    }
    let mut factory = InstructionInfoFactory::new();
    let volatile = volatile_registers(p, f.entry, bitness);
    let mut pending = Vec::new();
    let mut seen_extract = BTreeSet::new();
    for cycle in cycles_of(f) {
        let Some(counter) = counter_of(p, f, &cycle, &instrs, bitness) else {
            continue;
        };
        let Some(extract) = extract_of(&cycle, f, &instrs, bitness) else {
            continue;
        };
        if !seen_extract.insert(extract.at) || muls_in(&cycle, f, &instrs, bitness).is_empty() {
            continue;
        }
        pending.push(Check {
            stored: cycle_slots(f, &cycle, &instrs, bitness, &mut factory),
            written: cycle_regs(f, &cycle, &instrs, bitness, volatile, &mut factory),
            cycle,
            counter,
            extract,
            bound: None,
            shift: None,
            table: None,
            index_is_counter: false,
            secrets: BTreeSet::new(),
        });
        if pending.len() == CHECKS_MAX {
            break;
        }
    }
    if !pending.is_empty() {
        fold(p, a, f, bitness, &instrs, &mut pending);
    }
    pending
}

/// Renders the checks as the resource's text.
///
/// # Arguments
///
/// * `a` - The analysis.
/// * `o` - User names.
/// * `f` - The function.
/// * `checks` - The checks, non-empty.
///
/// # Returns
///
/// The report.
fn render_checks(a: &Analysis, o: &Overlay, f: &Function, checks: &[Check]) -> String {
    let mut out = format!(
        "# {} partial product check{} in {}\n",
        checks.len(),
        plural(checks.len()),
        short_name(a, o, f.entry)
    );
    for c in checks {
        let _ = writeln!(out, "# {}", loop_line(c));
        let _ = writeln!(out, "# {}", extract_line(c));
        let _ = writeln!(out, "# {}", table_line(c));
        let _ = writeln!(out, "# {}", secret_line(c));
    }
    out
}

/// The loop line: the counter, the bound and, when both ends are known,
/// the iteration count.
///
/// # Arguments
///
/// * `c` - The check.
///
/// # Returns
///
/// The line, without its `#` prefix.
fn loop_line(c: &Check) -> String {
    let reg = reg_name(c.counter.reg);
    let bound = c.counter.imm.or(c.bound);
    match (bound, c.counter.from_zero && c.counter.ge_exit) {
        (Some(n), true) => format!(
            "loop at {:#x}, {n} iterations counted by {reg} from 0",
            c.cycle.head
        ),
        (Some(n), false) => format!("loop at {:#x}, counted by {reg} against {n}", c.cycle.head),
        (None, _) => format!("loop at {:#x}, counted by {reg}", c.cycle.head),
    }
}

/// The extract line: the shift, the resolved count and the compare.
///
/// # Arguments
///
/// * `c` - The check.
///
/// # Returns
///
/// The line, without its `#` prefix.
fn extract_line(c: &Check) -> String {
    let count = c.extract.imm.map(u64::from).or(c.shift.map(u64::from));
    let by = count.map_or_else(|| String::from("by a register"), |n| format!("by {n}"));
    format!(
        "extract at {:#x}: {} {by}, compared at {:#x} to a byte",
        c.extract.at, c.extract.how, c.extract.cmp_at
    )
}

/// The table line: its address when the base folded, and the index.
///
/// # Arguments
///
/// * `c` - The check.
///
/// # Returns
///
/// The line, without its `#` prefix.
fn table_line(c: &Check) -> String {
    let index = reg_name(c.extract.index);
    let index = if c.index_is_counter {
        format!("{index} (the counter)")
    } else {
        index
    };
    match c.table {
        Some(at) => format!("table at {at:#x}, indexed by {index}"),
        None => format!("table indexed by {index}; its address did not fold"),
    }
}

/// The secret line.
///
/// A loop-invariant multiplicand makes the leaked bits a hidden-number
/// problem. Without one the report stops short of that claim.
///
/// # Arguments
///
/// * `c` - The check.
///
/// # Returns
///
/// The line, without its `#` prefix.
fn secret_line(c: &Check) -> String {
    if c.secrets.is_empty() {
        return String::from(
            "the loop multiplies, but no multiplicand was shown to be loop-invariant",
        );
    }
    let names = c.secrets.iter().cloned().collect::<Vec<_>>().join(", ");
    format!(
        "secret: {names}, loop-invariant and multiplied in the loop. \
         shape: hidden number problem (known bits of a product). \
         lattice reduction, not more samples"
    )
}

/// The cycles of a function, one per back-edge target.
///
/// A node is on the cycle when the header can reach it and it can get back
/// to the header. A block that falls into the loop, or that the loop exits
/// to, fails one of those and stays out, so a store above the loop is not
/// read as a store inside it.
///
/// # Arguments
///
/// * `f` - The function.
///
/// # Returns
///
/// The cycles, one per header.
fn cycles_of(f: &Function) -> Vec<Cycle> {
    let starts: BTreeSet<u64> = f.blocks.iter().map(|b| b.start).collect();
    let succs: BTreeMap<u64, &[u64]> = f
        .blocks
        .iter()
        .map(|b| (b.start, b.successors.as_slice()))
        .collect();
    let mut preds: BTreeMap<u64, Vec<u64>> = BTreeMap::new();
    for b in &f.blocks {
        for &s in &b.successors {
            if starts.contains(&s) {
                preds.entry(s).or_default().push(b.start);
            }
        }
    }
    let mut heads = BTreeSet::new();
    for b in &f.blocks {
        for &s in &b.successors {
            if s <= b.start && starts.contains(&s) {
                heads.insert(s);
            }
        }
    }
    let mut cycles = Vec::new();
    for head in heads {
        let forward = walk(head, |n| succs.get(&n).copied().unwrap_or(&[]));
        let backward = walk(head, |n| preds.get(&n).map_or(&[], Vec::as_slice));
        let body: BTreeSet<u64> = forward.intersection(&backward).copied().collect();
        let self_loop = succs.get(&head).is_some_and(|s| s.contains(&head));
        if body.len() > 1 || self_loop {
            cycles.push(Cycle { head, body });
        }
    }
    cycles
}

/// The block starts reachable from `start` by `next`, capped at the walk.
///
/// # Arguments
///
/// * `start` - The first block.
/// * `next` - The edges out of a block. Every slice shares one lifetime,
///   the graph the walk reads.
///
/// # Returns
///
/// The reachable starts, `start` included.
fn walk<'a>(start: u64, next: impl Fn(u64) -> &'a [u64]) -> BTreeSet<u64> {
    let mut seen = BTreeSet::new();
    let mut q = VecDeque::from([start]);
    while let Some(n) = q.pop_front() {
        if seen.len() == WALK_MAX || !seen.insert(n) {
            continue;
        }
        q.extend(next(n));
    }
    seen
}

/// Whether an instruction's block is on the cycle.
///
/// # Arguments
///
/// * `f` - The function.
/// * `cycle` - The cycle.
/// * `ip` - The instruction.
///
/// # Returns
///
/// Whether the instruction is on the cycle.
fn on_cycle(f: &Function, cycle: &Cycle, ip: u64) -> bool {
    let at = f.blocks.partition_point(|b| b.start <= ip);
    at.checked_sub(1)
        .and_then(|i| f.blocks.get(i))
        .is_some_and(|b| ip < b.end && cycle.body.contains(&b.start))
}

/// The cycle's counter: a register incremented on the cycle and compared
/// there, with a conditional branch leaving the cycle.
///
/// The taken edge has to leave. A branch back to the header is the latch,
/// not the exit, and the fall-through of this shape stays in the body.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `f` - The function.
/// * `cycle` - The cycle.
/// * `instrs` - The function's instructions.
/// * `bitness` - Decoder bitness.
///
/// # Returns
///
/// The counter, or `None` when the cycle has none.
fn counter_of(
    p: &Program,
    f: &Function,
    cycle: &Cycle,
    instrs: &[Instruction],
    bitness: u32,
) -> Option<Counter> {
    let inc: BTreeSet<Register> = instrs
        .iter()
        .filter(|i| on_cycle(f, cycle, i.ip()) && increments(i, bitness))
        .filter_map(|i| reg_op(i, 0, bitness))
        .collect();
    if inc.is_empty() {
        return None;
    }
    for b in &f.blocks {
        if !cycle.body.contains(&b.start) {
            continue;
        }
        let block = crate::analysis::functions::decode_block(p, bitness, b);
        let Some(term) = block.last() else {
            continue;
        };
        if term.flow_control() != FlowControl::ConditionalBranch {
            continue;
        }
        if cycle.body.contains(&term.near_branch64()) {
            continue;
        }
        let Some(cmp) = block
            .iter()
            .rev()
            .skip(1)
            .find(|i| i.mnemonic() == Mnemonic::Cmp)
        else {
            continue;
        };
        if block
            .iter()
            .skip_while(|i| i.ip() != cmp.ip())
            .skip(1)
            .any(|i| i.ip() != term.ip() && i.rflags_modified() != RflagsBits::NONE)
        {
            continue;
        }
        let (left, right) = (reg_op(cmp, 0, bitness), reg_op(cmp, 1, bitness));
        let Some(reg) = [left, right]
            .into_iter()
            .flatten()
            .find(|r| inc.contains(r))
        else {
            continue;
        };
        let other = [left, right].into_iter().flatten().find(|r| *r != reg);
        let imm = imm_op(cmp);
        if other.is_none() && imm.is_none() {
            continue;
        }
        let ge = matches!(term.condition_code(), ConditionCode::ge | ConditionCode::ae);
        let from_zero = instrs
            .iter()
            .any(|i| !on_cycle(f, cycle, i.ip()) && zeros(i, reg, bitness));
        return Some(Counter {
            reg,
            imm,
            cmp_at: cmp.ip(),
            bound_reg: other.filter(|_| imm.is_none()),
            ge_exit: ge,
            from_zero,
        });
    }
    None
}

/// Whether the instruction adds one to a whole register.
///
/// # Arguments
///
/// * `i` - The instruction.
/// * `bitness` - Decoder bitness.
///
/// # Returns
///
/// Whether it increments a register.
fn increments(i: &Instruction, bitness: u32) -> bool {
    if !full_reg(i) {
        return false;
    }
    if i.mnemonic() == Mnemonic::Inc {
        return reg_op(i, 0, bitness).is_some();
    }
    i.mnemonic() == Mnemonic::Add && reg_op(i, 0, bitness).is_some() && imm_op(i) == Some(1)
}

/// Whether the destination is a 32-bit or 64-bit register.
///
/// An 8-bit or 16-bit write does not replace the whole register, so the
/// folder drops the register instead of keeping a value it only partly saw.
///
/// # Arguments
///
/// * `i` - The instruction.
///
/// # Returns
///
/// Whether operand 0 is a register of at least 32 bits.
fn full_reg(i: &Instruction) -> bool {
    i.op0_kind() == OpKind::Register && i.op0_register().size() >= 4
}

/// Whether the instruction writes zero to the whole of `reg`.
///
/// # Arguments
///
/// * `i` - The instruction.
/// * `reg` - The register.
/// * `bitness` - Decoder bitness.
///
/// # Returns
///
/// Whether it is `xor reg, reg` or `mov reg, 0` of the whole register.
fn zeros(i: &Instruction, reg: Register, bitness: u32) -> bool {
    if !full_reg(i) {
        return false;
    }
    let Some(dest) = reg_op(i, 0, bitness) else {
        return false;
    };
    if dest != reg {
        return false;
    }
    if i.mnemonic() == Mnemonic::Xor && reg_op(i, 1, bitness) == Some(reg) {
        return true;
    }
    i.mnemonic() == Mnemonic::Mov && imm_op(i) == Some(0)
}

/// The cycle's extract: a `shr` by at least 16, or any `shrd`, compared
/// within [`EXTRACT_WINDOW`] instructions to a byte loaded through an index.
///
/// # Arguments
///
/// * `cycle` - The cycle.
/// * `f` - The function.
/// * `instrs` - The function's instructions.
/// * `bitness` - Decoder bitness.
///
/// # Returns
///
/// The extract, or `None` when the cycle has none.
fn extract_of(
    cycle: &Cycle,
    f: &Function,
    instrs: &[Instruction],
    bitness: u32,
) -> Option<Extract> {
    for (n, i) in instrs.iter().enumerate() {
        if !on_cycle(f, cycle, i.ip()) {
            continue;
        }
        let Some((how, count_reg, imm)) = shift_of(i, bitness) else {
            continue;
        };
        let Some(dest) = reg_op(i, 0, bitness) else {
            continue;
        };
        let mut loaded: Option<(Register, &Instruction)> = None;
        for w in instrs.iter().skip(n + 1).take(EXTRACT_WINDOW) {
            if !on_cycle(f, cycle, w.ip()) {
                break;
            }
            if matches!(
                w.flow_control(),
                FlowControl::Call | FlowControl::IndirectCall
            ) {
                break;
            }
            if writes_reg(w, dest, bitness) {
                break;
            }
            if is_byte_index_load(w, bitness)
                && let Some(reg) = reg_op(w, 0, bitness)
            {
                loaded = Some((reg, w));
            }
            if w.mnemonic() != Mnemonic::Cmp {
                continue;
            }
            let Some(mem) = cmp_table(w, dest, loaded, bitness) else {
                continue;
            };
            let Some((base, disp, index, ip_table)) = mem_index(mem, bitness) else {
                continue;
            };
            return Some(Extract {
                at: i.ip(),
                how,
                imm,
                count_reg,
                cmp_at: w.ip(),
                resolve_at: loaded.map_or(w.ip(), |(_, load)| load.ip()),
                base,
                ip_table,
                disp,
                index,
            });
        }
    }
    None
}

/// A `shr` by at least 16, or any `shrd`: mnemonic, count register, immediate.
///
/// A shift of a few bits compared with a byte is an ordinary mask. Sixteen
/// is the smallest count that is taking the top of a word rather than a
/// field out of a byte. Any `shrd` counts: its count is often in `cl`.
///
/// # Arguments
///
/// * `i` - The instruction.
/// * `bitness` - Decoder bitness.
///
/// # Returns
///
/// The shift, or `None` when the instruction is not this extract.
fn shift_of(
    i: &Instruction,
    bitness: u32,
) -> Option<(&'static str, Option<Register>, Option<u32>)> {
    match i.mnemonic() {
        Mnemonic::Shr => {
            let imm = imm_op(i)
                .and_then(|n| u32::try_from(n).ok())
                .filter(|n| *n >= 16)?;
            Some(("shr", None, Some(imm)))
        }
        Mnemonic::Shrd => {
            let reg = reg_op(i, 2, bitness);
            let imm = imm_op(i).and_then(|n| u32::try_from(n).ok());
            (reg.is_some() || imm.is_some()).then_some(("shrd", reg, imm))
        }
        _ => None,
    }
}

/// Whether `w` writes the whole register `reg` stands for.
///
/// # Arguments
///
/// * `w` - The instruction.
/// * `reg` - The register, already canonical.
/// * `bitness` - Decoder bitness.
///
/// # Returns
///
/// Whether the instruction writes it.
fn writes_reg(w: &Instruction, reg: Register, bitness: u32) -> bool {
    let mut factory = InstructionInfoFactory::new();
    factory.info(w).used_registers().iter().any(|u| {
        matches!(
            u.access(),
            OpAccess::Write | OpAccess::ReadWrite | OpAccess::CondWrite
        ) && canonical(u.register(), bitness) == reg
    })
}

/// Whether `w` zero-extends a byte loaded through an index into a register.
///
/// # Arguments
///
/// * `w` - The instruction.
/// * `bitness` - Decoder bitness.
///
/// # Returns
///
/// Whether it is that load.
fn is_byte_index_load(w: &Instruction, bitness: u32) -> bool {
    w.mnemonic() == Mnemonic::Movzx
        && reg_op(w, 0, bitness).is_some()
        && w.op1_kind() == OpKind::Memory
        && w.memory_size().size() == 1
        && w.memory_index() != Register::None
}

/// The memory operand a compare checks against the extract.
///
/// Either the compare names the byte memory itself, or it names the
/// register a zero-extending byte load in this window just wrote.
///
/// # Arguments
///
/// * `cmp` - The compare.
/// * `dest` - The shifted register.
/// * `loaded` - The zero-extending load in the window, and its destination.
/// * `bitness` - Decoder bitness.
///
/// # Returns
///
/// The instruction whose memory operand is the table byte, or `None`.
fn cmp_table<'a>(
    cmp: &'a Instruction,
    dest: Register,
    loaded: Option<(Register, &'a Instruction)>,
    bitness: u32,
) -> Option<&'a Instruction> {
    let regs: Vec<Register> = (0..cmp.op_count())
        .filter_map(|n| reg_op(cmp, n, bitness))
        .collect();
    if !regs.contains(&dest) {
        return None;
    }
    if cmp.op_count() == 2
        && (cmp.op0_kind() == OpKind::Memory || cmp.op1_kind() == OpKind::Memory)
        && is_byte_mem(cmp)
    {
        return Some(cmp);
    }
    let (reg, load) = loaded?;
    regs.contains(&reg).then_some(load)
}

/// Whether a memory operand is one byte addressed through an index.
///
/// # Arguments
///
/// * `i` - The instruction.
///
/// # Returns
///
/// Whether the memory operand is that byte.
fn is_byte_mem(i: &Instruction) -> bool {
    i.memory_size().size() == 1 && i.memory_index() != Register::None
}

/// The base, displacement, index and ip-relative address of a byte load.
///
/// A scale other than one is not the byte table this report names.
///
/// # Arguments
///
/// * `i` - The load or the compare that names the memory.
/// * `bitness` - Decoder bitness.
///
/// # Returns
///
/// Base, displacement, index and the ip-relative address, or `None`.
fn mem_index(i: &Instruction, bitness: u32) -> Option<(Register, i64, Register, Option<u64>)> {
    let index = canonical(i.memory_index(), bitness);
    if index == Register::None || i.memory_index_scale() != 1 {
        return None;
    }
    let disp = disasm::displacement(i, bitness);
    if i.is_ip_rel_memory_operand() {
        return Some((Register::None, 0, index, Some(i.ip_rel_memory_address())));
    }
    let base = canonical(i.memory_base(), bitness);
    (base != Register::None).then_some((base, disp, index, None))
}

/// Whether the cycle contains a multiply the report can name a source of.
///
/// # Arguments
///
/// * `cycle` - The cycle.
/// * `f` - The function.
/// * `instrs` - The function's instructions.
/// * `bitness` - Decoder bitness.
///
/// # Returns
///
/// Whether there is at least one.
fn muls_in(cycle: &Cycle, f: &Function, instrs: &[Instruction], bitness: u32) -> Vec<Know> {
    instrs
        .iter()
        .filter(|i| on_cycle(f, cycle, i.ip()))
        .filter(|i| matches!(i.mnemonic(), Mnemonic::Mul | Mnemonic::Imul))
        .find_map(|i| {
            let sources = mul_sources(i, bitness);
            (!sources.is_empty()).then_some(sources)
        })
        .unwrap_or_default()
}

/// The multiplicands a multiply reads.
///
/// A one-operand multiply also reads `rax`. A memory operand with an index
/// is the per-iteration table, not a secret, and is left out. The register
/// is recorded as [`Know::Arg`] only so the scan can chase whatever that
/// register holds when the multiply runs.
///
/// # Arguments
///
/// * `i` - The multiply.
/// * `bitness` - Decoder bitness.
///
/// # Returns
///
/// The sources.
fn mul_sources(i: &Instruction, bitness: u32) -> Vec<Know> {
    let mut sources = Vec::new();
    if i.op_count() == 1 {
        sources.push(Know::Arg(canonical(Register::RAX, bitness)));
    }
    for n in 0..i.op_count() {
        if i.mnemonic() == Mnemonic::Imul && i.op_count() == 3 && n != 1 {
            continue;
        }
        match i.op_kind(n) {
            OpKind::Register => {
                if let Some(r) = reg_op(i, n, bitness) {
                    sources.push(Know::Arg(r));
                }
            }
            OpKind::Memory if i.memory_index() == Register::None => {
                if let Some(slot) = stack_disp(i, bitness) {
                    sources.push(Know::Slot(slot));
                }
            }
            _ => {}
        }
    }
    sources
}

/// Stack slots the cycle writes.
///
/// # Arguments
///
/// * `f` - The function.
/// * `cycle` - The cycle.
/// * `instrs` - The function's instructions.
/// * `bitness` - Decoder bitness.
/// * `factory` - Register- and memory-access info.
///
/// # Returns
///
/// The displacements.
fn cycle_slots(
    f: &Function,
    cycle: &Cycle,
    instrs: &[Instruction],
    bitness: u32,
    factory: &mut InstructionInfoFactory,
) -> BTreeSet<i64> {
    let mut slots = BTreeSet::new();
    for i in instrs {
        if !on_cycle(f, cycle, i.ip()) || !writes_memory(i, factory) {
            continue;
        }
        if let Some(d) = stack_disp(i, bitness) {
            slots.insert(d);
        }
    }
    slots
}

/// Whole registers the cycle writes, plus the registers a call on it destroys.
///
/// # Arguments
///
/// * `f` - The function.
/// * `cycle` - The cycle.
/// * `instrs` - The function's instructions.
/// * `bitness` - Decoder bitness.
/// * `volatile` - Registers a call destroys.
/// * `factory` - Register-access info.
///
/// # Returns
///
/// The registers.
fn cycle_regs(
    f: &Function,
    cycle: &Cycle,
    instrs: &[Instruction],
    bitness: u32,
    volatile: &[Register],
    factory: &mut InstructionInfoFactory,
) -> BTreeSet<Register> {
    let mut regs = BTreeSet::new();
    for i in instrs {
        if !on_cycle(f, cycle, i.ip()) {
            continue;
        }
        if matches!(
            i.flow_control(),
            FlowControl::Call | FlowControl::IndirectCall
        ) {
            for r in volatile {
                regs.insert(canonical(*r, bitness));
            }
        }
        for u in factory.info(i).used_registers() {
            if matches!(
                u.access(),
                OpAccess::Write | OpAccess::ReadWrite | OpAccess::CondWrite
            ) {
                regs.insert(canonical(u.register(), bitness));
            }
        }
    }
    regs
}

/// Whether an instruction writes memory.
///
/// # Arguments
///
/// * `i` - The instruction.
/// * `factory` - Memory-access info.
///
/// # Returns
///
/// Whether it writes.
fn writes_memory(i: &Instruction, factory: &mut InstructionInfoFactory) -> bool {
    factory.info(i).used_memory().iter().any(|m| {
        matches!(
            m.access(),
            OpAccess::Write | OpAccess::ReadWrite | OpAccess::CondWrite
        )
    })
}

/// Fills each check's bound, shift, table and secrets from one forward scan.
///
/// The scan is address order, which is not execution order. It is enough
/// for a value that is stored before it is used and then only copied: the
/// store is at a lower address than the use in both the rotated loop this
/// was written for and a loop whose compare sits below its multiply.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `a` - The analysis.
/// * `f` - The function.
/// * `bitness` - Decoder bitness.
/// * `instrs` - The function's instructions.
/// * `checks` - The checks to fill.
fn fold(
    p: &Program,
    a: &Analysis,
    f: &Function,
    bitness: u32,
    instrs: &[Instruction],
    checks: &mut [Check],
) {
    let counters: Vec<Register> = checks.iter().map(|c| c.counter.reg).collect();
    let volatile = volatile_registers(p, f.entry, bitness);
    let env = Env {
        p,
        a,
        bitness,
        volatile,
        counters: &counters,
    };
    let mut facts = Facts::new();
    for r in argument_registers(p, f.entry, bitness) {
        let r = canonical(*r, bitness);
        facts.regs.insert(r, Know::Arg(r));
    }
    let mut callees = BTreeMap::new();
    for i in instrs {
        snapshot(f, i, &facts, checks, bitness);
        apply(&env, i, &mut facts, &mut callees, true);
    }
}

/// Records what a check needs from the state before `i` runs.
///
/// A multiply's sources are resolved only for a check whose cycle contains
/// that multiply. One function can hold two such loops, and a product in
/// one is not a secret of the other.
///
/// # Arguments
///
/// * `f` - The function.
/// * `i` - The instruction about to run.
/// * `facts` - The state before it.
/// * `checks` - The checks.
/// * `bitness` - Decoder bitness.
fn snapshot(f: &Function, i: &Instruction, facts: &Facts, checks: &mut [Check], bitness: u32) {
    let count_mask = if bitness == 64 { 63 } else { 31 };
    for c in checks.iter_mut() {
        if i.ip() == c.counter.cmp_at
            && let Some(r) = c.counter.bound_reg
        {
            c.bound = facts.concrete(r);
        }
        if i.ip() == c.extract.at {
            c.shift = c.extract.imm.or_else(|| {
                c.extract
                    .count_reg
                    .and_then(|r| facts.concrete(r))
                    .map(|n| lo32(n) & count_mask)
            });
        }
        if i.ip() == c.extract.resolve_at {
            c.table = c.extract.ip_table.or_else(|| {
                facts
                    .concrete(c.extract.base)
                    .map(|b| b.wrapping_add(c.extract.disp.cast_unsigned()))
            });
            c.index_is_counter = match facts.regs.get(&c.extract.index) {
                Some(Know::Counter) => true,
                Some(Know::Val(_)) => c.extract.index == c.counter.reg,
                _ => false,
            };
        }
    }
    if !matches!(i.mnemonic(), Mnemonic::Mul | Mnemonic::Imul) {
        return;
    }
    let sources = mul_sources(i, bitness);
    for c in checks.iter_mut() {
        if !on_cycle(f, &c.cycle, i.ip()) {
            continue;
        }
        for k in &sources {
            if let Some(name) = secret_name(facts, *k, &c.stored, &c.written) {
                c.secrets.insert(name);
            }
        }
    }
}

/// The name of a multiplicand the cycle does not overwrite.
///
/// A register source stands for whatever that register holds now: `mov rax,
/// rcx` then `mul rax` is a multiply by the argument, and `mov r10,
/// [rsp+0x2f8]` then `mul r10` is a multiply by the slot.
///
/// # Arguments
///
/// * `facts` - The state at the multiply.
/// * `know` - The source as the multiply names it.
/// * `stored` - Stack slots this cycle writes.
/// * `written` - Registers this cycle writes.
///
/// # Returns
///
/// The name, or `None` when the cycle overwrites it or it is not a slot or
/// an entry register.
fn secret_name(
    facts: &Facts,
    know: Know,
    stored: &BTreeSet<i64>,
    written: &BTreeSet<Register>,
) -> Option<String> {
    let live = match know {
        Know::Arg(r) => facts.regs.get(&r).copied().unwrap_or(Know::Arg(r)),
        other => other,
    };
    match live {
        Know::Slot(d) if !stored.contains(&d) => Some(format!("[rsp+{d:#x}]")),
        Know::Arg(r) if !written.contains(&r) => Some(reg_name(r)),
        _ => None,
    }
}

impl Facts {
    /// An empty scan state.
    fn new() -> Self {
        Self {
            regs: BTreeMap::new(),
            slots: BTreeMap::new(),
            statics: BTreeMap::new(),
            seq: 0,
        }
    }

    /// The concrete integer in a register, if it holds one.
    ///
    /// # Arguments
    ///
    /// * `reg` - The register.
    ///
    /// # Returns
    ///
    /// The integer, or `None` when the register holds anything else.
    fn concrete(&self, reg: Register) -> Option<u64> {
        match self.regs.get(&reg) {
            Some(Know::Val(v)) => Some(*v),
            _ => None,
        }
    }

    /// The integer at a static address.
    ///
    /// A store the scan has seen wins. Otherwise the bytes in the image,
    /// unless they are all zero: a zero in a writable image is the value
    /// before the initializer runs, which is not the value the program
    /// reads. An explicit store of zero is kept, because the scan saw it
    /// written.
    ///
    /// # Arguments
    ///
    /// * `p` - The loaded image.
    /// * `addr` - The address.
    /// * `size` - The bytes to read, 1 to 8.
    ///
    /// # Returns
    ///
    /// The little-endian integer, or `None` when nothing known is there.
    fn load_static(&self, p: &Program, addr: u64, size: u32) -> Option<u64> {
        let end = addr.saturating_add(u64::from(size));
        let covering = self
            .statics
            .iter()
            .filter(|(at, s)| addr >= **at && end <= at.saturating_add(u64::from(s.width)));
        if let Some((at, s)) = covering.max_by_key(|(_, s)| s.seq) {
            let shift = u32::try_from(addr.saturating_sub(*at).saturating_mul(8)).unwrap_or(64);
            if shift >= 64 {
                return None;
            }
            return Some(low_bits(s.value >> shift, size));
        }
        let n = usize::try_from(size).unwrap_or(0);
        let bytes = p.read_va(addr, n)?;
        if bytes.iter().all(|b| *b == 0) {
            return None;
        }
        let mut buf = [0u8; 8];
        let take = n.min(buf.len());
        buf[..take].copy_from_slice(&bytes[..take]);
        Some(u64::from_le_bytes(buf))
    }
}

/// Applies one instruction to the scan state.
///
/// # Arguments
///
/// * `env` - The image, the bitness and which registers count.
/// * `i` - The instruction.
/// * `facts` - The state.
/// * `callees` - Callees already scanned.
/// * `follow` - Whether a direct call is scanned. A callee does not follow
///   its own calls, so the walk stays one deep.
fn apply(
    env: &Env<'_>,
    i: &Instruction,
    facts: &mut Facts,
    callees: &mut BTreeMap<u64, Callee>,
    follow: bool,
) {
    if follow
        && matches!(
            i.flow_control(),
            FlowControl::Call | FlowControl::IndirectCall
        )
    {
        for r in env.volatile {
            facts.regs.remove(&canonical(*r, env.bitness));
        }
        if is_near_call(i) {
            absorb_call(env, i.near_branch_target(), facts, callees);
        }
        return;
    }
    if let Some(produced) = produced(env, i, facts) {
        for (r, k) in produced {
            facts.regs.insert(r, k);
        }
    } else {
        clear_written(env, i, facts);
    }
    note_store(env, i, facts);
}

/// Copies a direct callee's static stores and its return value into the caller.
///
/// # Arguments
///
/// * `env` - The image and the bitness.
/// * `target` - The callee's entry.
/// * `facts` - The caller's state.
/// * `callees` - Callees already scanned.
fn absorb_call(env: &Env<'_>, target: u64, facts: &mut Facts, callees: &mut BTreeMap<u64, Callee>) {
    let Some(callee) = callee_facts(env.p, env.a, target, env.bitness, callees) else {
        return;
    };
    for (at, s) in &callee.statics {
        facts.seq = facts.seq.saturating_add(1);
        facts.statics.insert(
            *at,
            Static {
                width: s.width,
                value: s.value,
                seq: facts.seq,
            },
        );
    }
    if let Some(ret) = callee.ret {
        facts
            .regs
            .insert(canonical(Register::RAX, env.bitness), ret);
    }
}

/// Values an instruction produces that the folder can name.
///
/// `None` when the instruction is not one of the forms the folder follows
/// or writes only part of a register, in which case the caller clears what
/// it writes. A store to memory is recorded separately, including for an
/// instruction that also writes a register.
///
/// # Arguments
///
/// * `env` - The image, the bitness and which registers count.
/// * `i` - The instruction.
/// * `facts` - The state before the instruction.
///
/// # Returns
///
/// The registers it writes and what they hold, or `None`.
fn produced(env: &Env<'_>, i: &Instruction, facts: &Facts) -> Option<Vec<(Register, Know)>> {
    let bitness = env.bitness;
    if zeros(i, reg_op(i, 0, bitness).unwrap_or(Register::None), bitness) {
        let dest = reg_op(i, 0, bitness)?;
        return Some(vec![(dest, Know::Val(0))]);
    }
    if increments(i, bitness) {
        let dest = reg_op(i, 0, bitness)?;
        if env.counters.contains(&dest) {
            return Some(vec![(dest, Know::Counter)]);
        }
        let value = facts.concrete(dest)?.wrapping_add(1);
        return Some(vec![(dest, Know::Val(masked(i, bitness, value)))]);
    }
    match i.mnemonic() {
        Mnemonic::Mov | Mnemonic::Movzx | Mnemonic::Movsx | Mnemonic::Movsxd if full_reg(i) => {
            let dest = reg_op(i, 0, bitness)?;
            let know = widen(i, move_source(env, i, facts)?)?;
            Some(vec![(dest, know)])
        }
        Mnemonic::Lea if full_reg(i) => {
            let dest = reg_op(i, 0, bitness)?;
            Some(vec![(dest, lea_source(env, i, facts)?)])
        }
        Mnemonic::Add | Mnemonic::Sub if full_reg(i) => {
            let dest = reg_op(i, 0, bitness)?;
            let left = facts.concrete(dest)?;
            let right = imm_op(i).or_else(|| mem_concrete(env, i, facts))?;
            let value = if i.mnemonic() == Mnemonic::Add {
                left.wrapping_add(right)
            } else {
                left.wrapping_sub(right)
            };
            Some(vec![(dest, Know::Val(masked(i, bitness, value)))])
        }
        _ => None,
    }
}

/// Keeps the low half of a 32-bit result and the whole of a 64-bit one.
///
/// # Arguments
///
/// * `i` - The instruction.
/// * `bitness` - Decoder bitness.
/// * `value` - The computed result.
///
/// # Returns
///
/// The value the register holds.
fn masked(i: &Instruction, bitness: u32, value: u64) -> u64 {
    if bitness == 64 && i.op0_kind() == OpKind::Register && i.op0_register().size() == 4 {
        u64::from(lo32(value))
    } else {
        value
    }
}

/// Sign- or zero-extends a moved value the way the mnemonic does.
///
/// A 32-bit move into a 64-bit register clears the top half. `movsxd`
/// sign-extends. Anything already a counter, a slot or an argument is left
/// as it is. A partial extension the folder cannot name is `None`, so the
/// caller drops the register.
///
/// # Arguments
///
/// * `i` - The move.
/// * `know` - The source value.
///
/// # Returns
///
/// The value the destination holds, or `None` when a `movsx` is not from a
/// dword the folder can sign-extend.
fn widen(i: &Instruction, know: Know) -> Option<Know> {
    let Know::Val(v) = know else {
        return Some(know);
    };
    Some(match i.mnemonic() {
        Mnemonic::Movsxd => Know::Val(sext32(v)),
        Mnemonic::Movsx => return None,
        Mnemonic::Mov | Mnemonic::Movzx if i.op0_register().size() == 4 => {
            Know::Val(u64::from(lo32(v)))
        }
        _ => Know::Val(v),
    })
}

/// What a move reads.
///
/// A stack slot is returned as whatever the scan stored there, so a saved
/// counter reloads as the counter and a saved integer reloads as that
/// integer. A slot nothing has written is the slot itself, which is how a
/// multiplicand is named.
///
/// # Arguments
///
/// * `env` - The image and the bitness.
/// * `i` - The move.
/// * `facts` - The state.
///
/// # Returns
///
/// The source, or `None` when the folder cannot name it.
fn move_source(env: &Env<'_>, i: &Instruction, facts: &Facts) -> Option<Know> {
    if let Some(v) = imm_op(i) {
        return Some(Know::Val(v));
    }
    if let Some(r) = reg_op(i, 1, env.bitness) {
        return facts.regs.get(&r).copied();
    }
    if i.op_count() > 1 && i.op_kind(1) == OpKind::Memory {
        if let Some(d) = stack_disp(i, env.bitness) {
            return Some(facts.slots.get(&d).copied().unwrap_or(Know::Slot(d)));
        }
        return mem_concrete(env, i, facts).map(Know::Val);
    }
    None
}

/// What a `lea` computes, when that is a static address or a known base.
///
/// # Arguments
///
/// * `env` - The bitness.
/// * `i` - The lea.
/// * `facts` - The state.
///
/// # Returns
///
/// The address, or `None` when an index or an unknown base takes part.
fn lea_source(env: &Env<'_>, i: &Instruction, facts: &Facts) -> Option<Know> {
    if i.memory_index() != Register::None {
        return None;
    }
    let disp = disasm::displacement(i, env.bitness);
    if i.is_ip_rel_memory_operand() {
        return Some(Know::Val(i.ip_rel_memory_address()));
    }
    let base = canonical(i.memory_base(), env.bitness);
    let b = facts.concrete(base)?;
    Some(Know::Val(b.wrapping_add(disp.cast_unsigned())))
}

/// The integer a memory operand names, when its address is known.
///
/// # Arguments
///
/// * `env` - The image and the bitness.
/// * `i` - The instruction.
/// * `facts` - The state.
///
/// # Returns
///
/// The integer, or `None` when the address or the bytes are not known.
fn mem_concrete(env: &Env<'_>, i: &Instruction, facts: &Facts) -> Option<u64> {
    let addr = mem_addr(env, i, facts)?;
    let size = u32::try_from(i.memory_size().size()).unwrap_or(0);
    if size == 0 || size > 8 {
        return None;
    }
    facts.load_static(env.p, addr, size)
}

/// The address of a memory operand with no index.
///
/// # Arguments
///
/// * `env` - The bitness.
/// * `i` - The instruction.
/// * `facts` - The state.
///
/// # Returns
///
/// The address, or `None` when the base is not a known integer.
fn mem_addr(env: &Env<'_>, i: &Instruction, facts: &Facts) -> Option<u64> {
    if i.memory_index() != Register::None {
        return None;
    }
    let disp = disasm::displacement(i, env.bitness);
    if i.is_ip_rel_memory_operand() {
        return Some(i.ip_rel_memory_address());
    }
    let base = facts.concrete(canonical(i.memory_base(), env.bitness))?;
    Some(base.wrapping_add(disp.cast_unsigned()))
}

/// Records a store, so a later load of that static or slot still sees it.
///
/// A `mov` of a known register or immediate records the value. Any other
/// write drops what the scan thought was there: an `and` or an `or` of a
/// slot is not the value it had. A memory operand with an index is a table,
/// not a slot, and is left alone.
///
/// # Arguments
///
/// * `env` - The image and the bitness.
/// * `i` - The instruction.
/// * `facts` - The state.
fn note_store(env: &Env<'_>, i: &Instruction, facts: &mut Facts) {
    if i.op0_kind() != OpKind::Memory || i.memory_index() != Register::None {
        return;
    }
    let mut factory = InstructionInfoFactory::new();
    if !writes_memory(i, &mut factory) {
        return;
    }
    let size = u32::try_from(i.memory_size().size()).unwrap_or(0);
    if size == 0 || size > 8 {
        return;
    }
    let know = (i.mnemonic() == Mnemonic::Mov)
        .then(|| stored_know(env, i, facts))
        .flatten();
    if let Some(d) = stack_disp(i, env.bitness) {
        match know {
            Some(k) => {
                facts.slots.insert(d, k);
            }
            None => {
                facts.slots.remove(&d);
            }
        }
        return;
    }
    let Some(addr) = mem_addr(env, i, facts) else {
        return;
    };
    match know {
        Some(Know::Val(v)) => {
            facts.seq = facts.seq.saturating_add(1);
            facts.statics.insert(
                addr,
                Static {
                    width: size,
                    value: low_bits(v, size),
                    seq: facts.seq,
                },
            );
        }
        _ => forget_static(facts, addr, size),
    }
}

/// What a `mov` to memory writes, when the folder can name it.
///
/// # Arguments
///
/// * `env` - The bitness.
/// * `i` - The move.
/// * `facts` - The state.
///
/// # Returns
///
/// The value, or `None` when the source register is not known.
fn stored_know(env: &Env<'_>, i: &Instruction, facts: &Facts) -> Option<Know> {
    if let Some(r) = reg_op(i, 1, env.bitness) {
        return facts.regs.get(&r).copied();
    }
    imm_op(i).map(Know::Val)
}

/// Drops static stores that overlap a write the folder cannot name.
///
/// # Arguments
///
/// * `facts` - The state.
/// * `addr` - The first byte written.
/// * `size` - How many bytes.
fn forget_static(facts: &mut Facts, addr: u64, size: u32) {
    let end = addr.saturating_add(u64::from(size));
    facts.statics.retain(|at, s| {
        let s_end = at.saturating_add(u64::from(s.width));
        end <= *at || s_end <= addr
    });
}

/// The low `size` bytes of `v`.
///
/// # Arguments
///
/// * `v` - The value.
/// * `size` - How many bytes, 1 to 8.
///
/// # Returns
///
/// Those bytes, zero-extended.
fn low_bits(v: u64, size: u32) -> u64 {
    let bits = size.saturating_mul(8);
    if bits >= 64 {
        v
    } else {
        v & ((1u64 << bits) - 1)
    }
}

/// Clears registers an unmodelled instruction writes.
///
/// A write of `al` clears `rax` and leaves `rcx` alone, so `shr al, 6`
/// after `mov ecx, imm` does not destroy the shift count in `cl`.
///
/// # Arguments
///
/// * `env` - The bitness.
/// * `i` - The instruction.
/// * `facts` - The state.
fn clear_written(env: &Env<'_>, i: &Instruction, facts: &mut Facts) {
    let mut factory = InstructionInfoFactory::new();
    for u in factory.info(i).used_registers() {
        if matches!(
            u.access(),
            OpAccess::Write | OpAccess::ReadWrite | OpAccess::CondWrite
        ) {
            facts.regs.remove(&canonical(u.register(), env.bitness));
        }
    }
}

/// The displacement of an `[rsp+disp]` operand with no index.
///
/// # Arguments
///
/// * `i` - The instruction.
/// * `bitness` - Decoder bitness.
///
/// # Returns
///
/// The displacement, or `None` when the operand is not that slot.
fn stack_disp(i: &Instruction, bitness: u32) -> Option<i64> {
    if i.memory_index() != Register::None {
        return None;
    }
    let base = canonical(i.memory_base(), bitness);
    if base != canonical(Register::RSP, bitness) {
        return None;
    }
    Some(disasm::displacement(i, bitness))
}

/// Scans one callee, once, for its return value and its static stores.
///
/// The last `ret` in address order supplies `rax`. A callee that is itself
/// one straight line of stores, which an initializer is, has one.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `a` - The analysis.
/// * `entry` - The callee's entry.
/// * `bitness` - Decoder bitness.
/// * `callees` - The cache.
///
/// # Returns
///
/// The callee, or `None` when discovery did not find it.
fn callee_facts(
    p: &Program,
    a: &Analysis,
    entry: u64,
    bitness: u32,
    callees: &mut BTreeMap<u64, Callee>,
) -> Option<Callee> {
    if callees.contains_key(&entry) {
        return callees.get(&entry).cloned();
    }
    let instrs = function_instructions(p, a, entry);
    let volatile = volatile_registers(p, entry, bitness);
    let env = Env {
        p,
        a,
        bitness,
        volatile,
        counters: &[],
    };
    let mut facts = Facts::new();
    let mut ret = None;
    let mut nested = BTreeMap::new();
    for i in instrs.iter().take(CALLEE_INSTRS_MAX) {
        if i.mnemonic() == Mnemonic::Ret {
            ret = facts.regs.get(&canonical(Register::RAX, bitness)).copied();
        }
        apply(&env, i, &mut facts, &mut nested, false);
    }
    let callee = Callee {
        ret,
        statics: facts.statics,
    };
    callees.insert(entry, callee.clone());
    Some(callee)
}

/// The whole register an operand names.
///
/// An operand index past the instruction's operands is not asked of the
/// decoder: its check for that fires while tests run.
///
/// # Arguments
///
/// * `i` - The instruction.
/// * `n` - The operand index.
/// * `bitness` - Decoder bitness.
///
/// # Returns
///
/// The register, or `None` when the operand is not one.
fn reg_op(i: &Instruction, n: u32, bitness: u32) -> Option<Register> {
    (n < i.op_count() && i.op_kind(n) == OpKind::Register)
        .then(|| canonical(i.op_register(n), bitness))
}

/// An immediate operand, sign-extended as the decoder reports it.
///
/// # Arguments
///
/// * `i` - The instruction.
///
/// # Returns
///
/// The immediate, or `None` when the instruction has none.
fn imm_op(i: &Instruction) -> Option<u64> {
    (0..i.op_count()).find_map(|n| match i.op_kind(n) {
        OpKind::Immediate8 => Some(u64::from(i.immediate8())),
        OpKind::Immediate8to16
        | OpKind::Immediate8to32
        | OpKind::Immediate8to64
        | OpKind::Immediate16
        | OpKind::Immediate32
        | OpKind::Immediate32to64
        | OpKind::Immediate64 => Some(i.immediate(n)),
        _ => None,
    })
}

/// A register's name in the listing, lowercase.
///
/// # Arguments
///
/// * `reg` - The register.
///
/// # Returns
///
/// The name.
fn reg_name(reg: Register) -> String {
    format!("{reg:?}").to_lowercase()
}
