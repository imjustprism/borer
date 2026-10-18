//! The register and stack scan of one function that follows `this` and the
//! tables it is given: inputs, locals, calls and the stores they make.

use std::collections::{BTreeMap, BTreeSet};

use super::hints::param_class;
use super::{
    ANCESTORS_MAX, ClassInfo, Conv, MS_ARGS, MS_VOLATILE, PROLOGUE_MAX, READ_LINKS_MAX, SYSV_ARGS,
    SYSV_VOLATILE, Scan, Tracked, X86_ARGS, X86_VOLATILE,
};
use crate::analysis::classes::class_of;
use crate::analysis::functions::decode_block;
use crate::analysis::naming::in_data;
use crate::analysis::{Analysis, Function, striped};
use crate::isa::x86::{
    FlowControl, Instruction, InstructionInfoFactory, Mnemonic, OpAccess, OpKind, Register,
};
use crate::program::{BinaryFormat, Program};

/// Splits a template instantiation into its template and its argument
/// text: `A::B<C,D>` gives `A::B` and `C,D`.
///
/// # Arguments
///
/// * `name` - The type's name.
pub(super) fn template_args(name: &str) -> Option<(&str, &str)> {
    let open = name.find('<')?;
    let inner = name.strip_suffix('>')?;
    Some((name.get(..open)?, inner.get(open + 1..)?))
}

/// A parameter: its function's entry and its argument position.
pub(super) type ParamKey = (u64, u8);

/// Where a parameter's votes and bounds come from, gathered once before
/// the rounds of [`infer`](super::infer) type the parameters, by function entry and
/// argument position.
#[derive(Default)]
pub(super) struct Inputs {
    /// First-hand votes: the tables holding a function, a named member
    /// handing on its `this`, a singleton's slot.
    pub(super) firsthand: BTreeMap<ParamKey, BTreeSet<String>>,
    /// Second-hand votes of a fixed class: a caller handing on a parameter
    /// its signature declares, with the caller.
    pub(super) relayed: BTreeMap<ParamKey, Vec<(u64, String)>>,
    /// Second-hand votes of whatever class a caller's own parameter has,
    /// with the caller and that parameter.
    pub(super) hinted: BTreeMap<ParamKey, Vec<(u64, ParamKey)>>,
    /// Bounds from the callees a parameter is handed to.
    pub(super) bounds: BTreeMap<ParamKey, Vec<Bounded>>,
    /// The parameters whose class each parameter's class goes into.
    pub(super) readers: BTreeMap<ParamKey, BTreeSet<ParamKey>>,
}

impl Inputs {
    /// Adds what `f` hands its callees: its `this`, first-hand when its name
    /// makes it a member of a class, else the class it has itself; and the
    /// parameters it passes on untouched.
    ///
    /// # Arguments
    ///
    /// * `f` - The caller.
    /// * `scan` - Its scan.
    /// * `named` - The class its name gives, and whether it is a member of
    ///   it ([`member_class`]); `None` for a function its name gives none.
    pub(super) fn add_caller(&mut self, f: &Function, scan: &Scan, named: Option<(&str, bool)>) {
        match named {
            Some((class, true)) => {
                for &(target, p) in &scan.this_calls {
                    self.firsthand
                        .entry((target, p))
                        .or_default()
                        .insert(class.to_owned());
                }
            }
            Some((_, false)) => {}
            None => {
                for &(target, p) in &scan.this_calls {
                    self.hinted
                        .entry((target, p))
                        .or_default()
                        .push((f.entry, (f.entry, 0)));
                    self.readers
                        .entry((f.entry, 0))
                        .or_default()
                        .insert((target, p));
                }
            }
        }
        for (target, p, val) in &scan.calls {
            let Tracked::Param(n) = val else {
                continue;
            };
            if f.signature.is_some() {
                if let Some(class) = param_class(f, &BTreeMap::new(), *n) {
                    self.relayed
                        .entry((*target, *p))
                        .or_default()
                        .push((f.entry, class));
                }
            } else {
                self.hinted
                    .entry((*target, *p))
                    .or_default()
                    .push((f.entry, (f.entry, *n)));
                self.readers
                    .entry((f.entry, *n))
                    .or_default()
                    .insert((*target, *p));
            }
        }
    }

    /// Adds the votes of the singletons whose slots a scan hands its callees.
    ///
    /// # Arguments
    ///
    /// * `scan` - The caller's scan.
    /// * `tls_slots` - Singleton classes by TLS slot.
    pub(super) fn add_slots(&mut self, scan: &Scan, tls_slots: &BTreeMap<u64, String>) {
        for (target, p, val) in &scan.calls {
            if let Tracked::TlsSlot(off) = val
                && let Some(class) = tls_slots.get(off)
            {
                self.firsthand
                    .entry((*target, *p))
                    .or_default()
                    .insert(class.clone());
            }
        }
    }

    /// Returns every parameter something votes for or bounds.
    pub(super) fn params(&self) -> BTreeSet<ParamKey> {
        self.firsthand
            .keys()
            .chain(self.relayed.keys())
            .chain(self.hinted.keys())
            .chain(self.bounds.keys())
            .copied()
            .collect()
    }
}

/// A caller's local: its entry, the block it is filled and handed on in,
/// and its offset in the frame.
pub(super) type Local = (u64, u64, u64);

/// The locals callers hand their callees, gathered once before the rounds
/// of [`infer`](super::infer).
#[derive(Default)]
pub(super) struct Locals {
    /// The locals handed to each parameter.
    pub(super) args: BTreeMap<ParamKey, Vec<Local>>,
    /// The classes a local holds a copy of: the classes the caller's own
    /// signature declares for the parameters it copied from.
    pub(super) copies: BTreeMap<Local, BTreeSet<String>>,
}

impl Locals {
    /// Gathers the locals every scanned caller hands its callees, and the
    /// parameters each holds a copy of.
    ///
    /// # Arguments
    ///
    /// * `analysis` - The functions.
    /// * `scans` - Scans, with the locals each hands on and fills.
    pub(super) fn gather(analysis: &Analysis, scans: &BTreeMap<u64, Scan>) -> Self {
        let mut out = Self::default();
        for (&entry, scan) in scans {
            for &(target, p, at, block) in &scan.frame_args {
                out.args
                    .entry((target, p))
                    .or_default()
                    .push((entry, block, at));
            }
            let Some(f) = analysis.function(entry) else {
                continue;
            };
            for &(at, n, block) in &scan.frame_copies {
                if let Some(class) = param_class(f, &BTreeMap::new(), n) {
                    out.copies
                        .entry((entry, block, at))
                        .or_default()
                        .insert(class);
                }
            }
        }
        out
    }
}

/// A callee's bound on a parameter handed to it.
pub(super) enum Bounded {
    /// The class the callee's name or declared signature gives.
    Used(String),
    /// Whatever class the callee's parameter has.
    Given(ParamKey),
}

/// Returns the class a function's name gives and whether it is a member of
/// it, taking `this` first: not a static, and a declared signature leaves an
/// argument it reads undeclared, or is `const`.
///
/// PERF: the class is borrowed from the name; the rounds ask it of every
/// scan, and cloning each whole qualified name was a pass of its own.
///
/// # Arguments
///
/// * `f` - The function.
/// * `renames` - Names chosen by this pass.
/// * `statics` - Class-named functions whose first argument is not `this`.
/// * `scan` - Its scan.
///
/// # Returns
///
/// The class name and the member verdict, or `None` when the name gives no
/// class.
pub(super) fn member_class<'a>(
    f: &'a Function,
    renames: &'a BTreeMap<u64, String>,
    statics: &'a BTreeSet<u64>,
    scan: &Scan,
) -> Option<(&'a str, bool)> {
    let name = match renames.get(&f.entry) {
        Some(renamed) => renamed.as_str(),
        None => f.name.as_deref()?,
    };
    let class = class_of(name)?;
    let member = !statics.contains(&f.entry)
        && match &f.signature {
            Some(sig) => {
                sig.is_const || scan.args_read > sig.params.len() + usize::from(sig.by_pointer)
            }
            None => true,
        };
    Some((class, member))
}

/// Returns a class and its ancestors, nearest first, up to
/// [`ANCESTORS_MAX`] parent links.
///
/// # Arguments
///
/// * `classes` - Classes with their parents.
/// * `class` - The class to start from.
pub(super) fn ancestry(classes: &BTreeMap<String, ClassInfo>, class: &str) -> Vec<String> {
    let mut out = vec![class.to_owned()];
    let mut at = classes.get(class).and_then(|i| i.parent.clone());
    for _ in 0..ANCESTORS_MAX {
        let Some(p) = at else {
            break;
        };
        out.push(p.clone());
        at = classes.get(&p).and_then(|i| i.parent.clone());
    }
    out
}

/// Picks the calling convention's registers: where `this` arrives, what a
/// call may change and where the arguments travel.
///
/// # Arguments
///
/// * `program` - Its format selects the convention.
/// * `bitness` - 32 or 64.
pub(super) fn conv_of(program: &Program, bitness: u32) -> Conv {
    if bitness == 32 {
        return Conv {
            this: Register::ECX,
            volatile: &X86_VOLATILE,
            args: &X86_ARGS,
        };
    }
    match program.format {
        BinaryFormat::Elf | BinaryFormat::MachO => Conv {
            this: Register::RDI,
            volatile: &SYSV_VOLATILE,
            args: &SYSV_ARGS,
        },
        BinaryFormat::Pe | BinaryFormat::Raw | BinaryFormat::Archive => Conv {
            this: Register::RCX,
            volatile: &MS_VOLATILE,
            args: &MS_ARGS,
        },
    }
}

/// Splits a constructor or destructor name into its class and kind.
///
/// `A::B::B` and `A::B<T>::B` are constructors (a `_2` disambiguation
/// suffix from naming allowed), `A::B::~B` a destructor.
///
/// # Arguments
///
/// * `name` - A qualified function name.
///
/// # Returns
///
/// `(class, is_destructor)`, or `None` for any other method.
pub(super) fn ctor_class(name: &str) -> Option<(&str, bool)> {
    let class = class_of(name)?;
    let method = name.get(class.len() + 2..)?;
    let last = last_component(class);
    let base = last.split('<').next().unwrap_or(last);
    if base.is_empty() {
        return None;
    }
    if let Some(rest) = method.strip_prefix('~') {
        return (rest == base).then_some((class, true));
    }
    let plain = method
        .rsplit_once('_')
        .filter(|(_, n)| !n.is_empty() && n.chars().all(|c| c.is_ascii_digit()))
        .map_or(method, |(m, _)| m);
    (method == base || plain == base).then_some((class, false))
}

/// Returns the last `::`-separated component of a qualified name, template
/// arguments kept with their component.
///
/// # Arguments
///
/// * `name` - The qualified name.
fn last_component(name: &str) -> &str {
    let mut depth = 0i32;
    let mut start = 0;
    let bytes = name.as_bytes();
    for (i, &c) in bytes.iter().enumerate() {
        match c {
            b'<' => depth += 1,
            b'>' if bytes.get(i.wrapping_sub(1)) != Some(&b'-') => depth -= 1,
            b':' if depth == 0 && i > 0 && bytes.get(i - 1) == Some(&b':') => start = i + 1,
            _ => {}
        }
    }
    name.get(start..).unwrap_or(name)
}

/// Scans functions across the cores ([`striped`]), each with
/// [`scan_function`]; the results are keyed by entry, so the order they
/// come in changes nothing.
///
/// # Arguments
///
/// * `program` - Bytes and sections.
/// * `functions` - The functions to scan.
/// * `bitness` - 32 or 64.
/// * `conv` - The calling convention's registers.
pub(super) fn scan_all(
    program: &Program,
    functions: &[&Function],
    bitness: u32,
    conv: &Conv,
) -> Vec<(u64, Scan)> {
    striped(functions, |f| {
        (f.entry, scan_function(program, f, bitness, conv))
    })
    .into_iter()
    .flatten()
    .collect()
}

/// The register `r` stands for at `bitness`: its 64-bit self on 64-bit
/// code, the 32-bit one it aliases on 32-bit code.
///
/// # Arguments
///
/// * `r` - Any register.
/// * `bitness` - 32 or 64.
pub(super) fn full_reg(r: Register, bitness: u32) -> Register {
    if bitness == 64 {
        r.full_register()
    } else {
        r.full_register32()
    }
}

/// Follows `this`, the incoming arguments and the table addresses loaded
/// into registers through a function's instructions in address order.
///
/// Each argument register starts as the parameter it carries, so a call
/// that passes a parameter straight on records which one, and a class
/// known for that parameter reaches the callee. The register `this` arrives
/// in is left to the `this` tracking, and a class that arrives by flow votes
/// beside the classes `this` carries.
/// A tail jump ([`tail_target`]) hands the argument registers to its target
/// as they stand, so it records them as a call does, apart until
/// [`settle_tails`] knows which ones the target reads.
///
/// # Arguments
///
/// * `program` - Bytes and sections.
/// * `f` - The function.
/// * `bitness` - 32 or 64.
/// * `conv` - The calling convention's registers.
pub(super) fn scan_function(program: &Program, f: &Function, bitness: u32, conv: &Conv) -> Scan {
    let mut this: BTreeSet<Register> = BTreeSet::from([conv.this]);
    let mut vals: BTreeMap<Register, Tracked> = conv
        .args
        .iter()
        .enumerate()
        .filter(|(_, r)| **r != conv.this)
        .filter_map(|(i, r)| u8::try_from(i).ok().map(|n| (*r, Tracked::Param(n))))
        .collect();
    let blocks: Vec<Vec<Instruction>> = f
        .blocks
        .iter()
        .map(|b| decode_block(program, bitness, b))
        .collect();
    let mut scan = Scan {
        vararg_fixed: crate::analysis::decompile::lift::vararg_fixed(
            program,
            bitness,
            blocks
                .iter()
                .flatten()
                .take(PROLOGUE_MAX)
                .take_while(|i| !matches!(i.flow_control(), FlowControl::Call)),
        ),
        ..Scan::default()
    };
    let mut info = InstructionInfoFactory::new();
    scan.args_read = entry_reads(f, &blocks, bitness, conv, &mut info);
    for (start, block) in f.blocks.iter().map(|b| b.start).zip(blocks) {
        let early = start < f.entry;
        let marks = (
            scan.this_calls.len(),
            scan.calls.len(),
            scan.tail_this_calls.len(),
            scan.tail_calls.len(),
            scan.data_args.len(),
            scan.frame_args.len(),
            scan.frame_copies.len(),
        );
        let mut loaded: BTreeSet<Register> = BTreeSet::new();
        for instr in block {
            let before = scan.data_args.len();
            if let Some(target) = tail_target(f, &instr) {
                pass_args(target, conv.args, (&this, &vals), &mut scan, true);
            }
            step(
                program, &instr, bitness, conv, &mut this, &mut vals, &mut scan, &mut info,
            );
            let passed = scan.data_args.split_off(before);
            scan.data_args
                .extend(passed.into_iter().filter(|&(_, p, _)| {
                    conv.args
                        .get(usize::from(p))
                        .is_some_and(|r| loaded.contains(r))
                }));
            if instr.op0_kind() == OpKind::Register {
                let dst = full_reg(instr.op0_register(), bitness);
                let loads = match (instr.mnemonic(), instr.op1_kind()) {
                    (Mnemonic::Lea, OpKind::Memory) => instr.memory_base() == Register::RIP,
                    (Mnemonic::Mov, OpKind::Register) => {
                        loaded.contains(&full_reg(instr.op1_register(), bitness))
                    }
                    (
                        Mnemonic::Mov,
                        OpKind::Immediate64 | OpKind::Immediate32to64 | OpKind::Immediate32,
                    ) => true,
                    _ => false,
                };
                if loads {
                    loaded.insert(dst);
                } else {
                    loaded.remove(&dst);
                }
            }
        }
        if early {
            scan.this_calls.truncate(marks.0);
            scan.calls.truncate(marks.1);
            scan.tail_this_calls.truncate(marks.2);
            scan.tail_calls.truncate(marks.3);
            scan.data_args.truncate(marks.4);
            scan.frame_args.truncate(marks.5);
            scan.frame_copies.truncate(marks.6);
        }
        for arg in &mut scan.frame_args[marks.5..] {
            arg.3 = start;
        }
        for copy in &mut scan.frame_copies[marks.6..] {
            copy.2 = start;
        }
    }
    scan
}

/// Returns one past the highest argument position a function reads before
/// writing it, on some path from its entry.
///
/// The paths follow the blocks' successors from the entry block, so a block
/// laid out before the entry (code the function shares with another, which
/// it reaches after setting the register itself) is read in its place on
/// the path, and an instruction that reads a register it also writes
/// (`mov rcx, [rcx+10h]`) reads it first.
///
/// # Arguments
///
/// * `f` - The function.
/// * `blocks` - Its blocks' instructions, in the order of `f.blocks`.
/// * `bitness` - 32 or 64.
/// * `conv` - The calling convention's registers.
/// * `info` - Register-access facts.
pub(super) fn entry_reads(
    f: &Function,
    blocks: &[Vec<Instruction>],
    bitness: u32,
    conv: &Conv,
    info: &mut InstructionInfoFactory,
) -> usize {
    let index: BTreeMap<u64, usize> = f
        .blocks
        .iter()
        .enumerate()
        .map(|(i, b)| (b.start, i))
        .collect();
    let Some(&first) = index.get(&f.entry) else {
        return 0;
    };
    let bit = |r: Register| {
        conv.args
            .iter()
            .position(|a| *a == r)
            .map(|pos| (pos, 1u32 << pos))
    };
    let mut read = 0;
    let mut seen: BTreeSet<(usize, u32)> = BTreeSet::new();
    let mut work = vec![(first, 0u32)];
    while let Some((b, mut written)) = work.pop() {
        if !seen.insert((b, written)) {
            continue;
        }
        for instr in blocks.get(b).into_iter().flatten() {
            let makes_room = bitness == 32
                && instr.mnemonic() == Mnemonic::Push
                && instr.op0_kind() == OpKind::Register;
            let mut writes = 0u32;
            for ur in info.info(instr).used_registers() {
                let Some((pos, b)) = bit(full_reg(ur.register(), bitness)) else {
                    continue;
                };
                if matches!(
                    ur.access(),
                    OpAccess::Read
                        | OpAccess::CondRead
                        | OpAccess::ReadWrite
                        | OpAccess::ReadCondWrite
                ) && written & b == 0
                    && !makes_room
                {
                    read = read.max(pos + 1);
                }
                if matches!(
                    ur.access(),
                    OpAccess::Write
                        | OpAccess::ReadWrite
                        | OpAccess::CondWrite
                        | OpAccess::ReadCondWrite
                ) {
                    writes |= b;
                }
            }
            written |= writes;
        }
        let succs = f.blocks.get(b).map(|blk| blk.successors.as_slice());
        for s in succs.unwrap_or_default() {
            if let Some(&i) = index.get(s) {
                work.push((i, written));
            }
        }
    }
    read
}

/// Returns the function a jump leaves `f` for: a direct `jmp` or `jcc` to
/// one of its callees that starts none of its own blocks (a tail call,
/// which discovery records as a callee and does not follow).
///
/// # Arguments
///
/// * `f` - The function the jump belongs to.
/// * `instr` - The instruction.
///
/// # Returns
///
/// The target's entry, or `None` for any other instruction.
fn tail_target(f: &Function, instr: &Instruction) -> Option<u64> {
    if !matches!(
        instr.flow_control(),
        FlowControl::UnconditionalBranch | FlowControl::ConditionalBranch
    ) || !matches!(
        instr.op0_kind(),
        OpKind::NearBranch16 | OpKind::NearBranch32 | OpKind::NearBranch64
    ) {
        return None;
    }
    let target = instr.near_branch_target();
    (f.callees.binary_search(&target).is_ok()
        && f.blocks.binary_search_by_key(&target, |b| b.start).is_err())
    .then_some(target)
}

/// Records what the argument registers hold as a call or a tail jump to
/// `target` passes them.
///
/// `this` is recorded by position, a data address with its position
/// ([`Scan::data_args`]), a local a call hands on with its position
/// ([`Scan::frame_args`]; a tail jump leaves the frame), and any other
/// tracked value but part of a parameter's object with its position.
///
/// # Arguments
///
/// * `target` - The callee's entry.
/// * `args` - The argument registers, in order.
/// * `(this, vals)` - Registers holding `this`, and registers holding a
///   tracked value.
/// * `scan` - The facts collected so far.
/// * `tail` - A tail jump passes them, kept apart until [`settle_tails`].
fn pass_args(
    target: u64,
    args: &[Register],
    (this, vals): (&BTreeSet<Register>, &BTreeMap<Register, Tracked>),
    scan: &mut Scan,
    tail: bool,
) {
    for (p, r) in args.iter().enumerate() {
        let Ok(p) = u8::try_from(p) else {
            continue;
        };
        if this.contains(r) {
            let this_calls = if tail {
                &mut scan.tail_this_calls
            } else {
                &mut scan.this_calls
            };
            this_calls.push((target, p));
            continue;
        }
        match vals.get(r) {
            Some(Tracked::Table(addr)) => scan.data_args.push((target, p, *addr)),
            Some(Tracked::Frame(at)) => {
                if !tail {
                    scan.frame_args.push((target, p, *at, 0));
                }
            }
            Some(Tracked::Copied(..)) => {}
            Some(v) => {
                let calls = if tail {
                    &mut scan.tail_calls
                } else {
                    &mut scan.calls
                };
                calls.push((target, p, *v));
            }
            None => {}
        }
    }
}

/// Returns how many argument positions each scanned function reads.
///
/// They are the ones it reads itself before writing them
/// ([`Scan::args_read`]), and the ones it hands on untouched, by a call or
/// a tail jump, to a position its callee reads, over [`READ_LINKS_MAX`]
/// links.
///
/// A function that hands an argument on to a base method reads it as
/// surely as one that dereferences it; one that only leaves it in its
/// register while it calls something else does not.
///
/// # Arguments
///
/// * `scans` - Every scan, tail arguments not yet settled.
///
/// # Returns
///
/// One past the highest position read, by entry.
pub(super) fn read_counts(scans: &BTreeMap<u64, Scan>) -> BTreeMap<u64, usize> {
    let mut reads: BTreeMap<u64, usize> = scans.iter().map(|(e, s)| (*e, s.args_read)).collect();
    for _ in 0..READ_LINKS_MAX {
        let mut grew = false;
        for (entry, scan) in scans {
            let passed = scan
                .this_calls
                .iter()
                .chain(&scan.tail_this_calls)
                .map(|&(t, p)| (t, p, 0u8))
                .chain(scan.calls.iter().chain(&scan.tail_calls).filter_map(
                    |&(t, p, ref v)| match v {
                        Tracked::Param(n) => Some((t, p, *n)),
                        _ => None,
                    },
                ));
            let mut count = reads.get(entry).copied().unwrap_or(0);
            for (target, p, n) in passed {
                if reads.get(&target).is_some_and(|&k| usize::from(p) < k) {
                    count = count.max(usize::from(n) + 1);
                }
            }
            if reads.get(entry).is_some_and(|&k| count > k) {
                reads.insert(*entry, count);
                grew = true;
            }
        }
        if !grew {
            break;
        }
    }
    reads
}

/// Keeps the arguments a tail jump passes where its target reads them,
/// moving them in with the calls.
///
/// A call sets the registers it passes, but a tail jump hands on whatever
/// they hold, `this` included when the caller never wrote over it, so a
/// register the target never reads ([`read_counts`]) passes nothing: a
/// class's static factory reached through a `jmp` thunk would otherwise
/// take the class of whoever jumped there. A target without a scan reads
/// nothing known and keeps nothing.
///
/// # Arguments
///
/// * `scans` - Every scan so far; each one's tail arguments are settled.
/// * `reads` - How many argument positions each function reads.
pub(super) fn settle_tails(scans: &mut BTreeMap<u64, Scan>, reads: &BTreeMap<u64, usize>) {
    let reads = |target: u64, p: u8| reads.get(&target).is_some_and(|&n| usize::from(p) < n);
    for scan in scans.values_mut() {
        let this_calls = std::mem::take(&mut scan.tail_this_calls);
        scan.this_calls
            .extend(this_calls.into_iter().filter(|&(t, p)| reads(t, p)));
        let calls = std::mem::take(&mut scan.tail_calls);
        scan.calls
            .extend(calls.into_iter().filter(|&(t, p, _)| reads(t, p)));
    }
}

/// Advances the scan over one instruction.
///
/// A register copy carries `this` or a tracked value along; `lea` from
/// `rip` and a 64-bit immediate load a table address; `lea` from `this`
/// tracks the address of a field (an alias of `this` at offset 0); a word
/// load from a field of `this` tracks the field; a word store of a table register
/// through `this` with no displacement records the table; the stack pointer
/// and `lea` from it track a local, and a load through a parameter stored
/// into the frame records the local as a copy of what the parameter points
/// at; a call records the base constructor, the arguments holding `this`,
/// a call result, a field or a local, forgets the volatile registers and
/// tracks its own result in rax; any other write to a register forgets what
/// it held.
///
/// # Arguments
///
/// * `program` - Sections, to tell data addresses.
/// * `instr` - The instruction.
/// * `bitness` - 32 or 64.
/// * `conv` - The calling convention's registers.
/// * `this` - Registers holding `this`.
/// * `vals` - Registers holding a tracked value: a table address, a call
///   result, a word loaded from a field of `this`, a local or part of a
///   parameter's object.
/// * `scan` - The facts collected so far.
/// * `info` - Register-access facts.
#[expect(
    clippy::too_many_arguments,
    reason = "one scan state split into its parts"
)]
pub(super) fn step(
    program: &Program,
    instr: &Instruction,
    bitness: u32,
    conv: &Conv,
    this: &mut BTreeSet<Register>,
    vals: &mut BTreeMap<Register, Tracked>,
    scan: &mut Scan,
    info: &mut InstructionInfoFactory,
) {
    let Conv {
        this: this_reg,
        volatile,
        args,
    } = *conv;
    let word = if bitness == 64 { 8 } else { 4 };
    if matches!(instr.flow_control(), FlowControl::Return) {
        let rax = full_reg(Register::RAX, bitness);
        match vals.get(&rax) {
            Some(Tracked::TlsSlot(off)) => scan.returns_tls = Some(*off),
            Some(Tracked::Result(callee)) => scan.returns_result = Some(*callee),
            Some(Tracked::Global(addr)) => scan.returns_global = Some(*addr),
            Some(Tracked::Field(off)) => scan.returns_field = Some(*off),
            _ => {}
        }
        return;
    }
    if matches!(
        instr.flow_control(),
        FlowControl::Call | FlowControl::IndirectCall
    ) {
        let direct = matches!(
            instr.op0_kind(),
            OpKind::NearBranch16 | OpKind::NearBranch32 | OpKind::NearBranch64
        );
        if scan.stores.is_empty()
            && scan.first_this_call.is_none()
            && this.contains(&this_reg)
            && direct
        {
            scan.first_this_call = Some(instr.near_branch_target());
        }
        if direct {
            pass_args(instr.near_branch_target(), args, (this, vals), scan, false);
        }
        for r in volatile {
            this.remove(r);
            vals.remove(r);
        }
        if direct {
            let rax = full_reg(Register::RAX, bitness);
            vals.insert(rax, Tracked::Result(instr.near_branch_target()));
        }
        return;
    }
    let is_mov = instr.mnemonic() == Mnemonic::Mov;
    if is_mov
        && instr.op0_kind() == OpKind::Register
        && instr.op1_kind() == OpKind::Memory
        && instr.op0_register().size() == word
        && instr.segment_prefix() == Register::GS
        && instr.memory_base() == Register::None
        && instr.memory_index() == Register::None
        && instr.memory_displacement64() == 0x58
    {
        let dst = instr.op0_register();
        this.remove(&dst);
        vals.insert(dst, Tracked::TlsArray);
        return;
    }
    if is_mov
        && instr.op0_kind() == OpKind::Register
        && instr.op1_kind() == OpKind::Memory
        && instr.op0_register().size() == word
        && vals.get(&instr.memory_base()) == Some(&Tracked::TlsArray)
        && instr.memory_index() != Register::None
    {
        let dst = instr.op0_register();
        this.remove(&dst);
        vals.insert(dst, Tracked::TlsBlock);
        return;
    }
    if is_mov
        && instr.op0_kind() == OpKind::Register
        && instr.op1_kind() == OpKind::Memory
        && instr.op0_register().size() == word
        && vals.get(&instr.memory_base()) == Some(&Tracked::TlsBlock)
        && let Some(off) = memory_offset(instr, vals)
    {
        let dst = instr.op0_register();
        this.remove(&dst);
        vals.insert(dst, Tracked::TlsSlot(off));
        return;
    }
    if is_mov
        && instr.op0_kind() == OpKind::Memory
        && instr.op1_kind() == OpKind::Register
        && vals.get(&instr.memory_base()) == Some(&Tracked::TlsBlock)
        && let Some(off) = memory_offset(instr, vals)
    {
        if this.contains(&instr.op1_register()) {
            scan.tls_stores.push(off);
        }
        return;
    }
    if is_mov
        && instr.op0_kind() == OpKind::Memory
        && instr.op1_kind() == OpKind::Register
        && matches!(instr.memory_base(), Register::RIP | Register::None)
        && instr.memory_index() == Register::None
    {
        let target = global_target(instr);
        let src = instr.op1_register();
        if in_data(program, target) {
            if this.contains(&src) {
                scan.global_stores.push(target);
            } else if let Some(Tracked::Result(callee)) = vals.get(&src) {
                scan.global_result_stores.push((target, *callee));
            }
        }
        return;
    }
    if is_mov
        && instr.op0_kind() == OpKind::Register
        && instr.op1_kind() == OpKind::Memory
        && instr.op0_register().size() == word
        && matches!(instr.memory_base(), Register::RIP | Register::None)
        && instr.memory_index() == Register::None
        && in_data(program, global_target(instr))
    {
        let dst = instr.op0_register();
        this.remove(&dst);
        vals.insert(dst, Tracked::Global(global_target(instr)));
        return;
    }
    if is_mov
        && instr.op0_kind() == OpKind::Register
        && instr.op1_kind() == OpKind::Register
        && instr.op0_register().size() == word
    {
        let (dst, src) = (instr.op0_register(), instr.op1_register());
        if this.contains(&src) {
            this.insert(dst);
        } else {
            this.remove(&dst);
        }
        if matches!(src, Register::RSP | Register::ESP) {
            vals.insert(dst, Tracked::Frame(0));
            return;
        }
        match vals.get(&src).copied() {
            Some(v) => {
                vals.insert(dst, v);
            }
            None => {
                vals.remove(&dst);
            }
        }
        return;
    }
    if instr.mnemonic() == Mnemonic::Lea
        && instr.op0_kind() == OpKind::Register
        && instr.memory_index() == Register::None
    {
        let dst = instr.op0_register();
        let base = instr.memory_base();
        let tracked = if base == Register::RIP {
            let target = instr.ip_rel_memory_address();
            in_data(program, target).then_some(Tracked::Table(target))
        } else if this.contains(&base) {
            Some(Tracked::FieldAddr(instr.memory_displacement64()))
        } else if matches!(base, Register::RSP | Register::ESP) {
            Some(Tracked::Frame(instr.memory_displacement64()))
        } else if let Some(Tracked::Frame(at)) = vals.get(&base) {
            Some(Tracked::Frame(
                at.wrapping_add(instr.memory_displacement64()),
            ))
        } else {
            None
        };
        this.remove(&dst);
        match tracked {
            Some(Tracked::FieldAddr(0)) => {
                this.insert(dst);
                vals.remove(&dst);
            }
            Some(v) => {
                vals.insert(dst, v);
            }
            None => {
                vals.remove(&dst);
            }
        }
        return;
    }
    if is_mov
        && instr.op0_kind() == OpKind::Register
        && matches!(
            instr.op1_kind(),
            OpKind::Immediate64 | OpKind::Immediate32to64 | OpKind::Immediate32
        )
    {
        let dst = full_reg(instr.op0_register(), bitness);
        this.remove(&dst);
        let imm = instr.immediate64();
        if in_data(program, imm) {
            vals.insert(dst, Tracked::Table(imm));
        } else {
            vals.insert(dst, Tracked::Const(imm));
        }
        return;
    }
    if is_mov
        && instr.op0_kind() == OpKind::Register
        && instr.op1_kind() == OpKind::Memory
        && instr.op0_register().size() == word
        && instr.memory_index() == Register::None
        && instr.memory_base() != Register::RIP
        && this.contains(&instr.memory_base())
    {
        let dst = instr.op0_register();
        this.remove(&dst);
        vals.insert(dst, Tracked::Field(instr.memory_displacement64()));
        return;
    }
    if is_mov
        && instr.op0_kind() == OpKind::Memory
        && instr.op1_kind() == OpKind::Register
        && instr.memory_index() == Register::None
        && instr.memory_displacement64() == 0
        && this.contains(&instr.memory_base())
    {
        if let Some(Tracked::Table(p)) = vals.get(&instr.op1_register()) {
            scan.stores.push(*p);
        }
        return;
    }
    if is_mov
        && instr.op0_kind() == OpKind::Memory
        && instr.op1_kind() == OpKind::Register
        && instr.memory_index() == Register::None
        && instr.memory_displacement64() != 0
        && this.contains(&instr.memory_base())
        && let Some(Tracked::Table(p)) = vals.get(&instr.op1_register())
    {
        scan.field_stores.push((instr.memory_displacement64(), *p));
        return;
    }
    if is_mov
        && instr.op0_kind() == OpKind::Memory
        && matches!(
            instr.op1_kind(),
            OpKind::Immediate32 | OpKind::Immediate32to64
        )
        && instr.memory_index() == Register::None
        && instr.memory_displacement64() == 0
        && this.contains(&instr.memory_base())
    {
        let imm = instr.immediate64();
        if in_data(program, imm) {
            scan.stores.push(imm);
        }
        return;
    }
    if is_mov
        && instr.op0_kind() == OpKind::Memory
        && matches!(
            instr.op1_kind(),
            OpKind::Immediate32 | OpKind::Immediate32to64
        )
        && instr.memory_index() == Register::None
        && instr.memory_displacement64() != 0
        && this.contains(&instr.memory_base())
    {
        let imm = instr.immediate(1);
        if in_data(program, imm) {
            scan.field_stores.push((instr.memory_displacement64(), imm));
        }
        return;
    }
    if is_mov
        && instr.op0_kind() == OpKind::Memory
        && instr.op1_kind() == OpKind::Register
        && instr.memory_index() == Register::None
        && instr.memory_displacement64() == 0
        && matches!(vals.get(&instr.memory_base()), Some(Tracked::Result(_)))
    {
        if let Some(Tracked::Table(p)) = vals.get(&instr.op1_register()) {
            scan.result_stores.push(*p);
        }
        return;
    }
    let moves = matches!(
        instr.mnemonic(),
        Mnemonic::Mov | Mnemonic::Movaps | Mnemonic::Movups | Mnemonic::Movdqa | Mnemonic::Movdqu
    );
    if moves
        && instr.op0_kind() == OpKind::Register
        && instr.op1_kind() == OpKind::Memory
        && instr.memory_index() == Register::None
        && let Some(Tracked::Param(n)) = vals.get(&instr.memory_base()).copied()
    {
        let dst = full_reg(instr.op0_register(), bitness);
        this.remove(&dst);
        vals.insert(dst, Tracked::Copied(n, instr.memory_displacement64()));
        return;
    }
    if moves
        && instr.op0_kind() == OpKind::Memory
        && instr.op1_kind() == OpKind::Register
        && instr.memory_index() == Register::None
        && let Some(Tracked::Copied(n, from)) =
            vals.get(&full_reg(instr.op1_register(), bitness)).copied()
        && let Some(at) = match instr.memory_base() {
            Register::RSP | Register::ESP => Some(0),
            base => match vals.get(&base) {
                Some(Tracked::Frame(at)) => Some(*at),
                _ => None,
            },
        }
    {
        let local = at
            .wrapping_add(instr.memory_displacement64())
            .wrapping_sub(from);
        scan.frame_copies.push((local, n, 0));
        return;
    }
    if is_mov
        && instr.op0_kind() == OpKind::Memory
        && instr.memory_index() == Register::None
        && matches!(
            instr.memory_base().full_register(),
            Register::RSP | Register::RBP
        )
        && !this.contains(&instr.memory_base())
    {
        let table = match instr.op1_kind() {
            OpKind::Register => match vals.get(&instr.op1_register()) {
                Some(Tracked::Table(p)) => Some(*p),
                _ => None,
            },
            OpKind::Immediate32 | OpKind::Immediate32to64 => {
                Some(instr.immediate64()).filter(|&imm| in_data(program, imm))
            }
            _ => None,
        };
        if let Some(p) = table {
            scan.local_stores.push(p);
        }
        return;
    }
    if is_mov
        && instr.op0_kind() == OpKind::Memory
        && instr.op1_kind() == OpKind::Register
        && instr.memory_index() == Register::None
        && this.contains(&instr.memory_base())
        && let Some(Tracked::Result(callee)) = vals.get(&instr.op1_register())
    {
        scan.field_result_stores
            .push((instr.memory_displacement64(), *callee));
        return;
    }
    for ur in info.info(instr).used_registers() {
        if matches!(
            ur.access(),
            OpAccess::Write | OpAccess::ReadWrite | OpAccess::CondWrite | OpAccess::ReadCondWrite
        ) {
            let r = full_reg(ur.register(), bitness);
            this.remove(&r);
            vals.remove(&r);
        }
    }
}

/// Returns the constant offset of a memory operand from its base: the
/// displacement plus an index register holding a tracked constant with
/// scale 1, or the displacement alone without an index.
///
/// # Arguments
///
/// * `instr` - The instruction with the memory operand.
/// * `vals` - Registers holding tracked values.
fn memory_offset(instr: &Instruction, vals: &BTreeMap<Register, Tracked>) -> Option<u64> {
    let disp = instr.memory_displacement64();
    let index = instr.memory_index();
    if index == Register::None {
        return Some(disp);
    }
    if instr.memory_index_scale() != 1 {
        return None;
    }
    match vals.get(&index) {
        Some(Tracked::Const(c)) => Some(disp.wrapping_add(*c)),
        _ => None,
    }
}

/// Returns the address a global-addressing memory operand names.
///
/// INVARIANT: with neither a base nor an index, the displacement is the
/// whole address, the only global-addressing form 32-bit code has
/// (`mov [0x403000], ecx`); 64-bit code addresses globals rip-relative.
///
/// # Arguments
///
/// * `instr` - The instruction with the memory operand.
fn global_target(instr: &Instruction) -> u64 {
    if instr.memory_base() == Register::RIP {
        instr.ip_rel_memory_address()
    } else {
        instr.memory_displacement64()
    }
}
