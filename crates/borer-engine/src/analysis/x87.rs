//! The x87 register stack across calls and returns.
//!
//! A 32-bit target hands a `float` or a `double` back in `st0`, and a call
//! is made with the x87 stack empty: the callee may use all eight
//! registers, and it returns with the stack empty but for that result. The
//! C runtime's x87 helpers break the rule on purpose: `_ftol` converts the
//! value in `st0` to an integer and pops it, `_CIpow` takes its two
//! operands off the stack and leaves the result in their place. What a call
//! does is read from a helper's name ([`helper`]), from the callee's body,
//! which reads what it was handed before pushing anything and leaves a
//! depth at every exit ([`flow`]), and from the code after the call, which
//! reads the result below anything it pushes itself ([`after_call`]).

use std::collections::BTreeMap;

use crate::isa::{
    FlowControl, Instruction, InstructionInfoFactory, Mnemonic, OpAccess, OpKind, Register,
    st_depth,
};

use super::functions::decode_block;
use super::{Analysis, Function};
use crate::program::Program;

/// Longest run of instructions read after a call for a use of what it left.
const AFTER_MAX: usize = 24;
/// Most operands a helper takes off the stack: `_CIpow` takes two.
pub(crate) const OPERANDS_MAX: u8 = 2;

/// The C runtime's x87 helpers by name, leading underscores dropped: the
/// operands each takes off the stack, and the floats it leaves in their
/// place.
const HELPERS: [(&str, u8, u8); 21] = [
    ("CIacos", 1, 1),
    ("CIasin", 1, 1),
    ("CIatan", 1, 1),
    ("CIatan2", 2, 1),
    ("CIcos", 1, 1),
    ("CIcosh", 1, 1),
    ("CIexp", 1, 1),
    ("CIfmod", 2, 1),
    ("CIlog", 1, 1),
    ("CIlog10", 1, 1),
    ("CIpow", 2, 1),
    ("CIsin", 1, 1),
    ("CIsinh", 1, 1),
    ("CIsqrt", 1, 1),
    ("CItan", 1, 1),
    ("CItanh", 1, 1),
    ("ftol", 1, 0),
    ("ftol2", 1, 0),
    ("ftol2_pentium4", 1, 0),
    ("ftol2_sse", 1, 0),
    ("ftol2_sse_excpt", 1, 0),
];

/// What a call does to the x87 stack.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct Effect {
    /// Values the callee takes off the top: a helper's operands, pushed
    /// first to last.
    pub(crate) takes: u8,
    /// Floats it leaves on top in their place: one for a float result.
    pub(crate) gives: u8,
}

/// Returns what the C runtime x87 helper a name names does to the stack.
///
/// # Arguments
///
/// * `name` - A function or import name, `dll!` prefix and leading
///   underscores allowed (`msvcrt.dll!_CIpow`, `__ftol2`).
///
/// # Returns
///
/// The helper's effect, or `None` for any other name.
pub(crate) fn helper(name: &str) -> Option<Effect> {
    let bare = super::bare_name(name).trim_start_matches('_');
    HELPERS
        .iter()
        .find(|(n, ..)| *n == bare)
        .map(|&(_, takes, gives)| Effect { takes, gives })
}

/// How a call met in a function's body moves the x87 stack.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Call {
    /// A helper: it takes its operands off the top and leaves its result.
    Helper(Effect),
    /// The callee runs no x87 instruction on its way to a `ret`, nor do the
    /// callees it calls there (a stack-cookie check): the stack is as the
    /// caller left it.
    Kept,
    /// Any other callee: called with the stack empty, it leaves a float or
    /// nothing, as the code after it shows ([`after_call`]).
    Plain,
}

/// The address a call or jump names outright: a near branch's target, or
/// the slot of an absolute memory operand (`call [__imp__CIpow]`).
///
/// # Arguments
///
/// * `i` - The call or jump.
pub(crate) fn named_target(i: &Instruction) -> Option<u64> {
    match i.op0_kind() {
        OpKind::NearBranch16 | OpKind::NearBranch32 | OpKind::NearBranch64 => {
            Some(i.near_branch_target())
        }
        OpKind::Memory
            if matches!(i.memory_base(), Register::None | Register::RIP)
                && i.memory_index() == Register::None =>
        {
            Some(i.memory_displacement64())
        }
        _ => None,
    }
}

/// The depth of an x87 register, `0` for `st0`.
///
/// # Arguments
///
/// * `r` - Any register.
fn depth_of(r: Register) -> Option<i32> {
    st_depth(r).and_then(|d| i32::try_from(d).ok())
}

/// The deepest x87 register an instruction reads, `0` for `st0`.
///
/// A compare that pops one value reads only `st0` here: it is how a
/// compiler drops the last value it holds, against an empty `st1`, and the
/// value it pops is all it certainly reads.
///
/// # Arguments
///
/// * `factory` - Register-access facts.
/// * `i` - The instruction.
fn deepest_read(factory: &mut InstructionInfoFactory, i: &Instruction) -> Option<i32> {
    let compare = matches!(
        i.mnemonic(),
        Mnemonic::Fcomp | Mnemonic::Fucomp | Mnemonic::Fcomip | Mnemonic::Fucomip
    );
    factory
        .info(i)
        .used_registers()
        .iter()
        .filter(|u| {
            matches!(
                u.access(),
                OpAccess::Read | OpAccess::CondRead | OpAccess::ReadWrite | OpAccess::ReadCondWrite
            )
        })
        .filter_map(|u| depth_of(u.register()))
        .filter(|k| !compare || *k == 0)
        .max()
}

/// How an instruction moves the x87 stack's top.
///
/// # Arguments
///
/// * `i` - The instruction.
///
/// # Returns
///
/// The values it pops, negative for those it pushes, or `None` for one
/// that loads a stack anew (`fninit`, `frstor`, `fldenv`) or empties it
/// (`emms`), which leaves nothing a caller handed over.
fn moves(i: &Instruction) -> Option<i32> {
    if matches!(i.mnemonic(), Mnemonic::Emms | Mnemonic::Femms) {
        return None;
    }
    let info = i.fpu_stack_increment_info();
    (!info.writes_top() || info.increment() != 0).then(|| info.increment())
}

/// Tells whether an instruction reads, writes or moves the x87 stack.
///
/// # Arguments
///
/// * `factory` - Register-access facts.
/// * `i` - The instruction.
pub(crate) fn touches(factory: &mut InstructionInfoFactory, i: &Instruction) -> bool {
    moves(i) != Some(0)
        || factory
            .info(i)
            .used_registers()
            .iter()
            .any(|u| depth_of(u.register()).is_some())
}

/// What the code after a call does with what the call left on the x87
/// stack.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum After {
    /// It reads a register below everything it pushed itself: the call
    /// left a float in `st0`.
    Reads,
    /// It pops that float unread first thing (`fstp st0`): the call left
    /// one, and the caller drops it.
    Drops,
    /// It returns straight, through jumps and instructions that leave the
    /// stack alone: whatever the call left is the function's result.
    Returns,
    /// Neither, within [`AFTER_MAX`] instructions: another call, a jump
    /// out, or a stack loaded anew comes first.
    Neither,
}

/// Reads the code after a call for a use of what the call left on the x87
/// stack.
///
/// The code is followed from the return address through jumps within the
/// caller and the fall-through of conditional branches, counting the
/// values it pushes; a read or a pop of a register below them, or a helper
/// taking more than them, reads the call's result. A call to a callee that
/// leaves the stack alone is stepped over. Reaching a `ret` with nothing
/// pushed and no conditional branch passed hands the result on.
///
/// # Arguments
///
/// * `decode` - Decodes the instruction at an address.
/// * `factory` - Register-access facts.
/// * `call` - The call.
/// * `inside` - Whether an address starts a block of the caller.
/// * `callee` - What a call met on the way does to the stack.
pub(crate) fn after_call(
    decode: &dyn Fn(u64) -> Option<Instruction>,
    factory: &mut InstructionInfoFactory,
    call: &Instruction,
    inside: &dyn Fn(u64) -> bool,
    callee: &dyn Fn(&Instruction) -> Call,
) -> After {
    let mut pushed = 0i32;
    let mut straight = true;
    let mut va = call.next_ip();
    for _ in 0..AFTER_MAX {
        let Some(i) = decode(va) else {
            return After::Neither;
        };
        if deepest_read(factory, &i).is_some_and(|k| k >= pushed) {
            let drop = i.mnemonic() == Mnemonic::Fstp
                && i.op0_kind() == OpKind::Register
                && i.op0_register() == Register::ST0;
            return if drop { After::Drops } else { After::Reads };
        }
        match moves(&i) {
            Some(m) if pushed < m => return After::Reads,
            Some(m) => pushed -= m,
            None => return After::Neither,
        }
        va = i.next_ip();
        match i.flow_control() {
            FlowControl::Next => {}
            FlowControl::ConditionalBranch => straight = false,
            FlowControl::UnconditionalBranch => match named_target(&i) {
                Some(t) if inside(t) => va = t,
                Some(_) | None => return After::Neither,
            },
            FlowControl::Call | FlowControl::IndirectCall => match callee(&i) {
                Call::Kept => {}
                Call::Helper(e) if i32::from(e.takes) > pushed => return After::Reads,
                Call::Helper(_) | Call::Plain => return After::Neither,
            },
            FlowControl::Return if straight && pushed == 0 => return After::Returns,
            FlowControl::Return
            | FlowControl::IndirectBranch
            | FlowControl::Interrupt
            | FlowControl::Exception
            | FlowControl::XbeginXabortXend => return After::Neither,
        }
    }
    After::Neither
}

/// How one exit of a function leaves the x87 stack, counted from the
/// stack it was entered with.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Exit {
    /// This many values above the entry's stack.
    Depth(i32),
    /// This many plus what a callee leaves whose result the exit hands on
    /// untouched: a call right before a `ret`, or a jump out of the
    /// function. The callee when the call or jump names it.
    After(i32, Option<u64>),
}

/// What a function does to the x87 stack it is entered with.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Flow {
    /// Values it takes off the stack it was entered with: one past the
    /// deepest register it reads, or pops, before pushing anything there.
    pub(crate) takes: u8,
    /// How each exit leaves the stack.
    pub(crate) exits: Vec<Exit>,
}

impl Flow {
    /// The floats the function leaves on the stack in place of what it
    /// takes, when every exit agrees.
    ///
    /// # Arguments
    ///
    /// * `net` - What a callee an exit hands on leaves, less what it takes;
    ///   `None` when that is not known.
    ///
    /// # Returns
    ///
    /// The count, or `None` when an exit is not known, the exits disagree
    /// or there are none.
    pub(crate) fn gives(&self, net: &dyn Fn(Option<u64>) -> Option<i32>) -> Option<u8> {
        let mut out = None;
        for e in &self.exits {
            let depth = match *e {
                Exit::Depth(d) => d,
                Exit::After(d, c) => d + net(c)?,
            };
            let g = u8::try_from(i32::from(self.takes) + depth).ok()?;
            if out.is_some_and(|o| o != g) {
                return None;
            }
            out = Some(g);
        }
        out
    }
}

/// Walks a function's blocks for what it does to the x87 stack.
///
/// Every block is entered at one depth, counted from the entry's; a block
/// entered at two is a stack the function does not keep straight, and the
/// walk gives up. A push adds one, a pop takes one, and a read or a pop of
/// a register below what the function pushed takes it from the caller
/// ([`Flow::takes`]); a helper takes its operands and leaves its result. A
/// plain call is made with the stack empty and leaves a float when the
/// code after it reads one ([`after_call`]); one handing its result
/// straight to a `ret` is an exit of its own. A `ret` is an exit, and so is
/// a jump out of the function, which hands the stack on.
///
/// # Arguments
///
/// * `program` - The image the function is decoded from.
/// * `bitness` - 32 or 64.
/// * `factory` - Register-access facts.
/// * `f` - The function.
/// * `callee` - What a call does to the stack, `None` to give up at it.
///
/// # Returns
///
/// The flow, or `None` when the depths disagree at a join or `callee`
/// gives up.
pub(crate) fn flow(
    program: &Program,
    bitness: u32,
    factory: &mut InstructionInfoFactory,
    f: &Function,
    callee: &dyn Fn(&Instruction) -> Option<Call>,
) -> Option<Flow> {
    let idx: BTreeMap<u64, usize> = f
        .blocks
        .iter()
        .enumerate()
        .map(|(i, b)| (b.start, i))
        .collect();
    let decode = |va: u64| super::functions::decode_at(program, bitness, va);
    let inside = |va: u64| idx.contains_key(&va);
    let mut entered: Vec<Option<i32>> = vec![None; f.blocks.len()];
    let mut takes = 0i32;
    let mut exits = Vec::new();
    let mut work = vec![(*idx.get(&f.entry)?, 0i32)];
    while let Some((b, at)) = work.pop() {
        match entered.get(b).copied().flatten() {
            Some(d) if d == at => continue,
            Some(_) => return None,
            None => *entered.get_mut(b)? = Some(at),
        }
        let blk = f.blocks.get(b)?;
        let mut d = at;
        let mut ended = false;
        for i in decode_block(program, bitness, blk) {
            if let Some(k) = deepest_read(factory, &i) {
                takes = takes.max(k - d + 1);
            }
            match moves(&i) {
                Some(m) => {
                    d -= m;
                    takes = takes.max(-d);
                }
                None => d = -takes,
            }
            let out = named_target(&i).filter(|t| !inside(*t));
            match i.flow_control() {
                FlowControl::Call | FlowControl::IndirectCall => match callee(&i)? {
                    Call::Kept => {}
                    Call::Helper(e) => {
                        takes = takes.max(i32::from(e.takes) - d);
                        d += i32::from(e.gives) - i32::from(e.takes);
                    }
                    Call::Plain => {
                        d = -takes;
                        let after = |c: &Instruction| callee(c).unwrap_or(Call::Plain);
                        match after_call(&decode, factory, &i, &inside, &after) {
                            After::Reads | After::Drops => d += 1,
                            After::Returns => {
                                exits.push(Exit::After(d, named_target(&i)));
                                ended = true;
                                break;
                            }
                            After::Neither => {}
                        }
                    }
                },
                FlowControl::Return => exits.push(Exit::Depth(d)),
                FlowControl::UnconditionalBranch | FlowControl::ConditionalBranch
                    if out.is_some() =>
                {
                    exits.push(Exit::After(d, out));
                }
                FlowControl::IndirectBranch if blk.successors.is_empty() => {
                    exits.push(Exit::After(d, None));
                }
                FlowControl::Next
                | FlowControl::UnconditionalBranch
                | FlowControl::ConditionalBranch
                | FlowControl::IndirectBranch
                | FlowControl::Interrupt
                | FlowControl::Exception
                | FlowControl::XbeginXabortXend => {}
            }
        }
        if !ended {
            work.extend(
                blk.successors
                    .iter()
                    .filter_map(|s| idx.get(s))
                    .map(|&s| (s, d)),
            );
        }
    }
    Some(Flow {
        takes: u8::try_from(takes).ok()?,
        exits,
    })
}

/// What a function that calls nothing takes off the x87 stack it is
/// handed, and leaves there, when it takes something.
///
/// Such a function is a C runtime helper linked in without a name
/// (`_ftol2` in a stripped image), which pops on every path. Only a leaf
/// is read: a body that calls on is no helper, and a walk past a call to a
/// helper not known yet would count the stack it keeps as taken. A jump
/// out of it hands the stack to the leaf it jumps to, read the same way
/// one jump deep: `_ftol2_sse` picks `_ftol2` or its SSE2 twin and jumps
/// there, taking what they take.
///
/// # Arguments
///
/// * `program` - The image the function is decoded from.
/// * `analysis` - The functions, for the leaves it jumps to.
/// * `factory` - Register-access facts.
/// * `f` - The function.
///
/// # Returns
///
/// The effect, or `None` when the function or a leaf it jumps to calls
/// something, it takes nothing or more than [`OPERANDS_MAX`], or its exits
/// disagree on what they leave.
pub(crate) fn leaf_helper(
    program: &Program,
    analysis: &Analysis,
    factory: &mut InstructionInfoFactory,
    f: &Function,
) -> Option<Effect> {
    let bitness = program.arch.bitness()?;
    let own = flow(program, bitness, factory, f, &|_| None)?;
    let mut takes = i32::from(own.takes);
    let mut exits = Vec::with_capacity(own.exits.len());
    for exit in own.exits {
        exits.push(match exit {
            Exit::Depth(d) => (d, 0),
            Exit::After(d, to) => {
                let to = analysis.function(to?)?;
                let theirs = flow(program, bitness, factory, to, &|_| None)?;
                let gives = theirs.gives(&|_| None)?;
                takes = takes.max(i32::from(theirs.takes) - d);
                (d, i32::from(gives) - i32::from(theirs.takes))
            }
        });
    }
    let takes = u8::try_from(takes)
        .ok()
        .filter(|t| (1..=OPERANDS_MAX).contains(t))?;
    let mut gives = None;
    for (d, net) in exits {
        let g = u8::try_from(i32::from(takes) + d + net).ok()?;
        if gives.is_some_and(|o| o != g) {
            return None;
        }
        gives = Some(g);
    }
    Some(Effect {
        takes,
        gives: gives?,
    })
}
