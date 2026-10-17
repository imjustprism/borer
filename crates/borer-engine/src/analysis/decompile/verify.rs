//! Verification: the lifter checked against the emulator, block by block.
//!
//! A decompiler's output is only as true as its lifting, and a lifting bug
//! reads as plausible C. This module runs each basic block twice from the
//! same seeded state: once on the emulator, which executes the real
//! instructions, and once through the lifter, whose symbolic results are
//! then evaluated under that state. Seven kinds of fact ([`Fact`]) must
//! agree: every general register the lifter wrote (in the lane it says it
//! wrote) or left alone, and the stack pointer; every x87 stack register;
//! the low lane of every xmm register; every segment register's selector;
//! every stack slot the lifter holds a value for; every store, `rep` region
//! and byte the block writes off the frame; and whether the block's
//! conditional branch is taken. A
//! disagreement names one block, the fact, both values and the lifted
//! expression: a lifter bug found and located without a reader.
//!
//! Each block is checked up to its first control transfer, the branch
//! included. Memory nothing backs reads a hash of its address on both
//! sides ([`fill_byte`]), so a load at a wrong offset reads a wrong value
//! rather than the same zero. The registers are random, except that a
//! register the block compares with a constant, or with another register,
//! mostly starts next to it, so a branch on equality or a boundary is
//! taken both ways across seeds. A value read from memory the block itself
//! wrote is set aside, since the lifter reads memory where the load sits
//! and the evaluator only knows it as it was. What the evaluator cannot
//! read (a width-dependent intrinsic, a vector operation) is counted, not
//! compared; so is an xmm lane whose lifted variable reads a 32-bit
//! source whole where the machine wrote only the 32 bits, the lane
//! known roughness. A TLS slot read compares as memory at the
//! address the run's entry state walks the thread's TLS array to
//! ([`State::resolve_tls`]); the walk's own registers name the segment
//! selector, no value the entry state holds, and stay counted. A pass
//! says the lifting agreed on the seeds tried, not that it is right.

use std::collections::BTreeMap;
use std::fmt::Write as _;

use crate::isa::x86::{
    FlowControl, Instruction, InstructionInfoFactory, Mnemonic, OpAccess, OpKind, Register,
    st_register,
};

use super::expr::{
    Cond, Expr, Flags, Key, Op, RoundToInt, TLS_BASE, Ty, UnOp, abs_bits, align_up_bits, cls_bits,
    either_width, extremum_bits, fcvt_float_width, fold, midpoint_bits, rbit_bits, rev16_bits,
    rev32_bits, rint_bits, sub_sat_bits, tls_slot, unary,
};
use super::lift::{BlockFacts, Env, Pass, exec_block};
use super::{Ctx, new_ctx};
use crate::analysis::{Analysis, BasicBlock, Function, Overlay};
use crate::emulate::{Emulator, Run, Stop, fill_byte};
use crate::fxmap::FxHashSet;
use crate::num::{from_usize, lo8, lo32};
use crate::program::Program;

/// The general registers compared, as the emulator names them.
pub(super) const REGS: [(&str, Register); 15] = [
    ("rax", Register::RAX),
    ("rbx", Register::RBX),
    ("rcx", Register::RCX),
    ("rdx", Register::RDX),
    ("rsi", Register::RSI),
    ("rdi", Register::RDI),
    ("rbp", Register::RBP),
    ("r8", Register::R8),
    ("r9", Register::R9),
    ("r10", Register::R10),
    ("r11", Register::R11),
    ("r12", Register::R12),
    ("r13", Register::R13),
    ("r14", Register::R14),
    ("r15", Register::R15),
];
/// The general registers compared in 32-bit code, named as the emulator
/// names them and keyed as the lifter keys them there (`eax`, not `rax`).
pub(super) const REGS_32: [(&str, Register); 7] = [
    ("eax", Register::EAX),
    ("ebx", Register::EBX),
    ("ecx", Register::ECX),
    ("edx", Register::EDX),
    ("esi", Register::ESI),
    ("edi", Register::EDI),
    ("ebp", Register::EBP),
];
/// The xmm registers compared, keyed as the lifter keys them: each by its
/// low lane, the half a scalar float or integer occupies.
pub(super) const XMMS: [Register; 16] = [
    Register::XMM0,
    Register::XMM1,
    Register::XMM2,
    Register::XMM3,
    Register::XMM4,
    Register::XMM5,
    Register::XMM6,
    Register::XMM7,
    Register::XMM8,
    Register::XMM9,
    Register::XMM10,
    Register::XMM11,
    Register::XMM12,
    Register::XMM13,
    Register::XMM14,
    Register::XMM15,
];
/// The segment registers compared, named as the report spells them and
/// keyed as the lifter keys them.
///
/// INVARIANT: the registers are in [`crate::emulate::SEG_ORDER`]'s order,
/// so index `n` of [`Emulator::segments`] is the emulated value of the
/// register at index `n` here.
pub(super) const SEGS: [(&str, Register); 6] = [
    ("es", Register::ES),
    ("cs", Register::CS),
    ("ss", Register::SS),
    ("ds", Register::DS),
    ("fs", Register::FS),
    ("gs", Register::GS),
];
/// Stack words seeded on each side of the starting stack pointer.
pub(super) const STACK_WORDS: i64 = 64;
/// Deepest expression evaluated.
pub(super) const EVAL_DEPTH: u8 = 48;
/// Fewest functions worth a thread of their own.
const PAR_MIN: usize = 64;
/// Mismatches a report lists.
pub const LISTED_MAX: usize = 200;
/// Instructions the emulator lacks that a report lists, most frequent first.
const UNMODELED_LISTED: usize = 20;
/// Longest `rep` region compared in bytes, and the iterations a block's
/// string instruction may run: a longer repeat leaves the block unchecked.
pub(super) const REGION_MAX: usize = 0x1000;
/// Bytes either side of the stack pointer, at a block's start or end, whose
/// writes belong to the frame (a saved register, a push), not to stores.
pub(super) const FRAME_SPAN: u64 = 0x1_0000;
/// Stirs a block's address into the seed.
pub(super) const GOLDEN: u64 = 0x9e37_79b9_7f4a_7c15;

/// The kind of fact a lifted block and the emulator are compared on.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Fact {
    /// A general register or the stack pointer, at the block's end.
    Register,
    /// An x87 stack register, at the block's end.
    X87,
    /// The low lane of an xmm register, at the block's end.
    Xmm,
    /// A segment register's selector, at the block's end.
    Segment,
    /// A stack slot the lifter holds a value for at the block's end.
    Slot,
    /// Memory off the frame: a store through a pointer, a byte of a `rep`
    /// region, or bytes the emulator changed that no lifted store writes.
    Store,
    /// Whether the block's conditional branch is taken.
    Branch,
    /// The low 64 bits of an arm64 `v` register, at the block's end.
    Vector,
}

impl Fact {
    /// Every kind, in report order.
    const ALL: [Self; 7] = [
        Self::Register,
        Self::X87,
        Self::Xmm,
        Self::Segment,
        Self::Slot,
        Self::Store,
        Self::Branch,
    ];
}

impl std::fmt::Display for Fact {
    /// Writes the kind's name as a report row spells it.
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            Self::Register => "register",
            Self::X87 => "x87",
            Self::Xmm => "xmm",
            Self::Segment => "segment",
            Self::Slot => "slot",
            Self::Store => "store",
            Self::Branch => "branch",
            Self::Vector => "vector",
        })
    }
}

/// One fact the lifter and the emulator disagree on.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Mismatch {
    /// The function's entry.
    pub function: u64,
    /// The block's start.
    pub block: u64,
    /// What kind of fact disagrees.
    pub fact: Fact,
    /// Which one: the register as the emulator names it, the x87 register
    /// as `st(n)`, the xmm register as `xmm0`, the segment register as
    /// `es`, the slot as an offset from
    /// the block's starting stack pointer (`rsp-0x18`), the address stored
    /// to, or the branch's address.
    pub place: String,
    /// What the emulator left: the value, or 1 for a branch taken.
    pub emulated: u64,
    /// What the lifted expression evaluates to, in the same terms; for
    /// bytes no lifted store writes, what they held before the block.
    pub lifted: u64,
    /// The width compared, in bits.
    pub bits: u8,
    /// The lifted expression, `(unchanged)` for a register the lifter wrote
    /// nothing to, or what the emulator wrote that no lifted store writes.
    pub expr: String,
}

/// What a verification found.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Verified {
    /// Functions visited.
    pub functions: usize,
    /// Blocks visited.
    pub blocks: usize,
    /// Blocks compared against the emulator.
    pub checked: usize,
    /// Blocks not compared, by reason.
    pub skipped: BTreeMap<&'static str, usize>,
    /// Blocks the emulator stopped in for an instruction it does not model,
    /// by what it named: the measure of its coverage, and the order to
    /// widen it in.
    pub unmodeled: BTreeMap<String, usize>,
    /// Facts compared, of every kind.
    pub compared: usize,
    /// Facts whose lifted value the evaluator cannot read, of every kind.
    pub unreadable: usize,
    /// Facts set aside because their lifted value reads memory the block
    /// wrote, of every kind.
    pub store_loads: usize,
    /// Facts set aside as the lane known roughness, of every
    /// kind.
    pub lane: usize,
    /// The same counts, by kind of fact.
    pub facts: BTreeMap<Fact, Tally>,
    /// Branches the emulator could not decide: a signed jump on an overflow
    /// flag the instruction before it does not compute in the emulator.
    pub undecided: usize,
    /// The disagreements.
    pub mismatches: Vec<Mismatch>,
}

/// What was compared of one kind of fact.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct Tally {
    /// Facts compared.
    pub compared: usize,
    /// Facts whose lifted value the evaluator cannot read; for a store,
    /// also one whose bytes a later write of unreadable address may
    /// overwrite.
    pub unreadable: usize,
    /// Facts set aside because their lifted value reads memory the block
    /// wrote.
    pub store_loads: usize,
    /// Facts set aside as the lane known roughness: an xmm
    /// lane whose lifted variable, a 32-bit source read whole, differs
    /// from the machine only above the 32 bits it wrote.
    pub lane: usize,
}

impl Verified {
    /// Counts one fact by how its lifted value read.
    ///
    /// # Arguments
    ///
    /// * `fact` - The fact's kind.
    /// * `read` - How it read.
    ///
    /// # Returns
    ///
    /// The value to compare, or `None` when there is none.
    pub(super) fn count(&mut self, fact: Fact, read: Read) -> Option<u64> {
        let tally = self.facts.entry(fact).or_default();
        match read {
            Read::Value(v) => {
                tally.compared += 1;
                self.compared += 1;
                Some(v)
            }
            Read::Unreadable => {
                tally.unreadable += 1;
                self.unreadable += 1;
                None
            }
            Read::Stale => {
                tally.store_loads += 1;
                self.store_loads += 1;
                None
            }
            Read::Rough => {
                tally.lane += 1;
                self.lane += 1;
                None
            }
        }
    }

    /// Adds another part's findings to these, after them.
    ///
    /// # Arguments
    ///
    /// * `part` - What one thread found.
    fn merge(&mut self, part: Self) {
        self.functions += part.functions;
        self.blocks += part.blocks;
        self.checked += part.checked;
        self.compared += part.compared;
        self.unreadable += part.unreadable;
        self.store_loads += part.store_loads;
        self.lane += part.lane;
        self.undecided += part.undecided;
        for (fact, t) in part.facts {
            let into = self.facts.entry(fact).or_default();
            into.compared += t.compared;
            into.unreadable += t.unreadable;
            into.store_loads += t.store_loads;
            into.lane += t.lane;
        }
        for (reason, n) in part.skipped {
            *self.skipped.entry(reason).or_default() += n;
        }
        for (what, n) in part.unmodeled {
            *self.unmodeled.entry(what).or_default() += n;
        }
        self.mismatches.extend(part.mismatches);
    }
}

/// How a lifted value read under a block's starting state.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum Read {
    /// It evaluated to this.
    Value(u64),
    /// The evaluator cannot read it.
    Unreadable,
    /// It reads memory the block wrote, which the evaluator only knows as
    /// it was.
    Stale,
    /// It differs from the machine only above the low 32 bits of a 64-bit
    /// xmm lane: the lane known roughness, counted apart and
    /// not compared.
    Rough,
}

/// What the lifter did beyond the environment a block leaves.
///
/// The memory it wrote, in program order, and the temporaries it made:
/// the lifter records them only while `Ctx::probe` is set, which only
/// [`verify`] does.
#[derive(Debug, Default)]
pub(super) struct Probe {
    /// The memory writes, in program order.
    pub(super) effects: Vec<Effect>,
    /// Each temporary the lifter made, by id, with the value it copied.
    pub(super) temps: BTreeMap<u32, Expr>,
}

impl Probe {
    /// Records a store through a pointer (a stack slot's store is in the
    /// environment instead).
    ///
    /// # Arguments
    ///
    /// * `addr` - The address stored to.
    /// * `ty` - The type stored.
    /// * `value` - The value stored.
    pub(super) fn store(&mut self, addr: &Expr, ty: Ty, value: &Expr) {
        self.effects.push(Effect::Store {
            addr: addr.clone(),
            ty,
            value: value.clone(),
        });
    }

    /// Records a `rep movs` or `rep stos` as the region it writes.
    ///
    /// # Arguments
    ///
    /// * `dst` - The region's lowest address.
    /// * `src` - The copied region's lowest address; `None` for a fill.
    /// * `value` - The fill's element value.
    /// * `bits` - The element width.
    /// * `len` - The region's length in bytes.
    pub(super) fn rep(&mut self, dst: Expr, src: Option<Expr>, value: Expr, bits: u8, len: Expr) {
        self.effects.push(Effect::Rep {
            dst,
            src: src.ok_or((value, bits)),
            len,
        });
    }

    /// Records an instruction left as asm that writes memory.
    pub(super) fn asm(&mut self) {
        self.effects.push(Effect::Asm);
    }

    /// Records a temporary.
    ///
    /// # Arguments
    ///
    /// * `id` - The temporary's id.
    /// * `value` - The value it copied.
    pub(super) fn temp(&mut self, id: u32, value: &Expr) {
        self.temps.insert(id, value.clone());
    }
}

/// One memory write of the lifter's.
#[derive(Debug)]
pub(super) enum Effect {
    /// A store through a pointer.
    Store {
        /// The address stored to.
        addr: Expr,
        /// The type stored.
        ty: Ty,
        /// The value stored.
        value: Expr,
    },
    /// A `rep movs` or `rep stos`.
    Rep {
        /// The region's lowest address.
        dst: Expr,
        /// The copied region's lowest address, or the fill's element value
        /// and width in bits.
        src: Result<Expr, (Expr, u8)>,
        /// The region's length in bytes.
        len: Expr,
    },
    /// An instruction left as asm that writes memory.
    Asm,
}

/// A small, seeded generator, so a run is the same each time.
pub(super) struct Rng(pub(super) u64);

impl Rng {
    /// The next value.
    pub(super) fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
}

/// A machine a block runs on for the check: the x86 [`Emulator`], or the
/// arm64 [`crate::emulate::a64::Machine`], which share these methods.
pub(super) trait Bench: Clone {
    /// The name the machine reads its stack pointer by, as a report names
    /// a slot from it.
    const SP: &'static str;

    /// Reads a byte as a load reads it, or `None` where a load faults.
    ///
    /// # Arguments
    ///
    /// * `at` - The address.
    fn byte_at(&self, at: u64) -> Option<u8>;

    /// Reads a register named as text, or `None` for a name that is no
    /// register.
    ///
    /// # Arguments
    ///
    /// * `name` - The register's name.
    fn register(&self, name: &str) -> Option<u64>;

    /// Sets the step budget of the next run.
    ///
    /// # Arguments
    ///
    /// * `budget` - The most instructions to run.
    fn set_budget(&mut self, budget: usize);

    /// Sets the address the next run halts at before executing it.
    ///
    /// # Arguments
    ///
    /// * `at` - The address, or `None` to run to the end.
    fn stop_at(&mut self, at: Option<u64>);

    /// Runs from `entry` until it stops.
    ///
    /// # Arguments
    ///
    /// * `entry` - The first instruction.
    ///
    /// # Returns
    ///
    /// Why it stopped, and the bytes it wrote in order.
    fn run(&mut self, entry: u64) -> Run;
}

impl Bench for Emulator<'_> {
    const SP: &'static str = "rsp";

    fn byte_at(&self, at: u64) -> Option<u8> {
        Emulator::byte_at(self, at)
    }

    fn register(&self, name: &str) -> Option<u64> {
        Emulator::register(self, name)
    }

    fn set_budget(&mut self, budget: usize) {
        Emulator::set_budget(self, budget);
    }

    fn stop_at(&mut self, at: Option<u64>) {
        Emulator::stop_at(self, at);
    }

    fn run(&mut self, entry: u64) -> Run {
        Emulator::run(self, entry)
    }
}

/// The state a block starts from, shared by the machine and the
/// evaluator.
pub(super) struct State<'p, M> {
    /// The memory before any run: the image and what the machine plants.
    pub(super) pristine: &'p M,
    /// The seed of the bytes nothing backs ([`fill_byte`]).
    pub(super) fill: u64,
    /// Each register's starting value, keyed as the lifter keys it.
    pub(super) regs: BTreeMap<Key, u64>,
    /// The starting stack pointer.
    pub(super) rsp: u64,
    /// The seeded stack bytes.
    pub(super) stack: BTreeMap<u64, u8>,
    /// The register width: an address and every operator is computed at
    /// this width, as the emulator computes it, so `eax * 4` past four
    /// gigabytes wraps.
    pub(super) width: u8,
    /// The temporaries the lifter made, by id, with the value each copied.
    pub(super) temps: BTreeMap<u32, Expr>,
    /// The address the entry state walks the TLS block to, resolved once
    /// per run ([`State::resolve_tls`]); zero where no walk applies.
    pub(super) tls_block: u64,
}

impl<M: Bench> State<'_, M> {
    /// A byte of memory before the block ran.
    ///
    /// # Arguments
    ///
    /// * `at` - The address.
    pub(super) fn byte(&self, at: u64) -> u8 {
        self.stack
            .get(&at)
            .copied()
            .or_else(|| self.pristine.byte_at(at))
            .unwrap_or_else(|| fill_byte(self.fill, at))
    }

    /// `n` bytes of memory before the block ran, little-endian.
    ///
    /// # Arguments
    ///
    /// * `at` - The address.
    /// * `n` - Bytes, at most 8.
    fn read(&self, at: u64, n: u64) -> Option<u64> {
        (1..=8)
            .contains(&n)
            .then(|| word(n, |i| self.byte(at.wrapping_add(i))))
    }
}

impl State<'_, Emulator<'_>> {
    /// Resolves the address a TLS slot read stands for, from the entry
    /// state, once per run.
    ///
    /// The emulator services a segment-prefixed read through the thread
    /// block it plants, so a run that walks the TLS array (`mov rax,
    /// gs:[0x58]` on x64) reads the word the block's TLS array field holds
    /// — planted zero, like the rest of the block's unplanted span — and
    /// indexes that array wherever the code's own index says. The index
    /// the corpus spells is the unlinked image's `_tls_index` cell, which
    /// the file leaves zero for the loader to bind, so this walk takes
    /// cell zero and lands on the address the machine's walk reads;
    /// walking the same words here, over the same entry-state memory
    /// ([`State::byte`]: the image, what the emulator plants and the
    /// bytes nothing backs hashed by address), turns a lifted
    /// `TLS_BASE + off` read into an ordinary memory read at that address
    /// plus `off`: both sides read the same bytes, and a wrong slot
    /// offset reads a wrong value rather than the same fill. In 32-bit
    /// code the lifter models no TLS array, so nothing there names a TLS
    /// pseudo-global and this walk never runs.
    ///
    /// INVARIANT: the base is resolved from the entry state, as every
    /// seeded value is; a block that itself stores through the segment
    /// base before reading a slot moves the machine's array without
    /// moving this one.
    fn resolve_tls(&mut self) -> u64 {
        let w = u64::from(self.width / 8);
        let array = self
            .read(self.pristine.tls_array_at(), w)
            .unwrap_or_default();
        self.read(array & low(self.width), w).unwrap_or_default() & low(self.width)
    }
}

/// Assembles `n` bytes, little-endian, at most 8.
///
/// # Arguments
///
/// * `n` - How many.
/// * `byte` - The byte at each offset.
pub(super) fn word(n: u64, byte: impl Fn(u64) -> u8) -> u64 {
    (0..n.min(8))
        .rev()
        .fold(0, |v, i| (v << 8) | u64::from(byte(i)))
}

/// Sign-extends the low `bits` of a value.
///
/// # Arguments
///
/// * `v` - The value.
/// * `bits` - The width, 1 to 64.
pub(super) fn sext(v: u64, bits: u8) -> Option<u64> {
    let shift = 64u32.checked_sub(u32::from(bits)).filter(|s| *s < 64)?;
    let wide = i64::from_ne_bytes(v.checked_shl(shift)?.to_ne_bytes()) >> shift;
    Some(u64::from_ne_bytes(wide.to_ne_bytes()))
}

/// A mask of the low `bits`.
///
/// # Arguments
///
/// * `bits` - The width.
pub(super) fn low(bits: u8) -> u64 {
    if bits >= 64 {
        u64::MAX
    } else {
        (1u64 << bits) - 1
    }
}

/// Evaluates a lifted expression under a starting state, with the lifter's
/// own folding for binary operators; `None` for what it cannot read.
///
/// Every operator is folded at the register width, as the text reads it:
/// in 32-bit code each variable is a `uint32_t`, so `(x << 8) >> 16` drops
/// the bits the left shift pushed past 32 before the right shift could
/// bring them back, where 64-bit arithmetic kept them.
///
/// # Arguments
///
/// * `e` - The expression.
/// * `st` - The starting state.
/// * `reads` - The memory ranges it read, gathered for the store check.
/// * `depth` - How much deeper to look.
pub(super) fn eval<M: Bench>(
    e: &Expr,
    st: &State<'_, M>,
    reads: &mut Vec<(u64, u64)>,
    depth: u8,
) -> Option<u64> {
    let d = depth.checked_sub(1)?;
    match e {
        Expr::Const(v) | Expr::FConst(v, _) => Some(*v),
        Expr::Var(k @ (Key::Reg(_) | Key::A64(_))) => st.regs.get(k).copied(),
        Expr::Var(Key::Tmp(id)) => eval(st.temps.get(id)?, st, reads, d),
        Expr::Var(Key::Slot(off)) => {
            let at = st.rsp.wrapping_add_signed(*off) & low(st.width);
            reads.push((at, 8));
            st.read(at, 8)
        }
        Expr::Var(Key::Global(at, bits)) => {
            let at =
                tls_slot(*at).map_or(*at, |off| st.tls_block.wrapping_add(off) & low(st.width));
            let n = u64::from(*bits / 8);
            reads.push((at, n));
            st.read(at, n)
        }
        Expr::Sp(off) => Some(st.rsp.wrapping_add_signed(*off) & low(st.width)),
        Expr::Bin(op, l, r) if op.is_float() => {
            let (fa, fb) = (float_bits(l, st)?, float_bits(r, st)?);
            let (a, b) = (
                float_of(eval(l, st, reads, d)?, fa),
                float_of(eval(r, st, reads, d)?, fb),
            );
            float_arith(*op, a, b, fa.max(fb))
        }
        Expr::Bin(op, l, r) => {
            let (a, b) = (eval(l, st, reads, d)?, eval(r, st, reads, d)?);
            match fold(*op, Expr::Const(a), Expr::Const(b), st.width) {
                Expr::Const(v) => Some(v),
                _ => None,
            }
        }
        Expr::Un(UnOp::Neg, inner) if float_bits(inner, st).is_some() => {
            let sign = 1u64 << (float_bits(inner, st)? - 1);
            Some(eval(inner, st, reads, d)? ^ sign)
        }
        Expr::Un(op @ (UnOp::Sqrt | UnOp::Fabs), inner) if float_bits(inner, st).is_some() => {
            float_un(*op, eval(inner, st, reads, d)?, float_bits(inner, st)?)
        }
        Expr::Un(op @ (UnOp::Neg | UnOp::Not), inner) => {
            let v = eval(inner, st, reads, d)?;
            match unary(*op, Expr::Const(v), st.width) {
                Expr::Const(v) => Some(v),
                _ => None,
            }
        }
        Expr::Deref(addr, ty) => {
            let at = eval(addr, st, reads, d)? & low(st.width);
            let n = u64::from(ty.bits() / 8);
            reads.push((at, n));
            st.read(at, n)
        }
        Expr::Cond(c) => eval_cond(c, st, reads, d).map(u64::from),
        Expr::Ternary(c, a, b) => {
            if eval_cond(c, st, reads, d)? {
                eval(a, st, reads, d)
            } else {
                eval(b, st, reads, d)
            }
        }
        Expr::Sext(inner, bits) => sext(eval(inner, st, reads, d)?, *bits),
        Expr::Cast(inner, ty) if ty.bits() <= 64 && !matches!(ty, Ty::F32 | Ty::F64) => {
            let v = eval(inner, st, reads, d)?;
            if let Some(fb) = float_bits(inner, st) {
                return Some(float_to_int(v, fb, ty.bits()));
            }
            Some(v & low(ty.bits()))
        }
        Expr::Cast(inner, ty @ (Ty::F32 | Ty::F64)) => {
            if let Some(fb) = float_bits(inner, st) {
                let v = eval(inner, st, reads, d)?;
                return Some(convert_float(v, Some(fb), *ty));
            }
            if let Some(v) = float_carried(inner, ty.bits(), |e| eval(e, st, reads, d)) {
                return Some(v);
            }
            if let Some(v) = reinterpret_float(inner, *ty, |e| eval(e, st, reads, d)) {
                return Some(v);
            }
            let (v, signed) = cast_integer(inner, |e| eval(e, st, reads, d))?;
            Some(integer_to_float(v, signed, *ty))
        }
        Expr::Call(name, args) => {
            if let Some(round) = RoundToInt::parse(name) {
                let src = args.first()?;
                let fb = fcvt_float_width(args.get(1), float_bits(src, st))?;
                let v = eval(src, st, reads, d)
                    .or_else(|| float_scale_at(src, fb, |e| eval(e, st, reads, d)));
                return round.apply(v?, fb);
            }
            match name.as_str() {
                "min" | "max" | "umin" | "umax" => {
                    let (a, b) = (args.first()?, args.get(1)?);
                    extremum_bits(
                        name,
                        eval(a, st, reads, d)?,
                        eval(b, st, reads, d)?,
                        st.width,
                    )
                }
                "abs" => abs_bits(eval(args.first()?, st, reads, d)?, st.width),
                "midpoint" => {
                    let (a, b) = (args.first()?, args.get(1)?);
                    midpoint_bits(eval(a, st, reads, d)?, eval(b, st, reads, d)?, st.width)
                }
                "align_up" => {
                    let (a, b) = (args.first()?, args.get(1)?);
                    align_up_bits(eval(a, st, reads, d)?, eval(b, st, reads, d)?, st.width)
                }
                "cls" => {
                    let arg = args.first()?;
                    let bits = match arg {
                        Expr::Cast(_, ty) | Expr::Deref(_, ty) => ty.bits().min(st.width),
                        _ => st.width,
                    };
                    cls_bits(eval(arg, st, reads, d)?, bits)
                }
                "rbit" | "rev16" | "rev32" => {
                    let arg = args.first()?;
                    let bits = match arg {
                        Expr::Cast(_, ty) | Expr::Deref(_, ty) => ty.bits().min(st.width),
                        _ => st.width,
                    };
                    let v = eval(arg, st, reads, d)?;
                    match name.as_str() {
                        "rbit" => rbit_bits(v, bits),
                        "rev16" => rev16_bits(v, bits),
                        _ => rev32_bits(v, bits),
                    }
                }
                "sub_sat" => {
                    let (a, b) = (args.first()?, args.get(1)?);
                    sub_sat_bits(eval(a, st, reads, d)?, eval(b, st, reads, d)?, st.width)
                }
                "rint" => {
                    let src = args.first()?;
                    rint_bits(eval(src, st, reads, d)?, float_bits(src, st)?)
                }
                _ => None,
            }
        }
        _ => None,
    }
}

/// The width of a floating-point expression, or `None` for an integer one.
///
/// A binary operation computes at the width the wider of its operands
/// carries ([`float_arith`]), the rounding the machine's own single
/// operation makes, so its value is that wide; the x87 stack holds its
/// values as doubles, which a store widens or narrows as the store's type
/// gives ([`convert_float`]).
///
/// # Arguments
///
/// * `e` - The expression.
/// * `st` - The starting state, whose temporaries are looked through.
pub(super) fn float_bits<M: Bench>(e: &Expr, st: &State<'_, M>) -> Option<u8> {
    match e {
        Expr::Deref(_, Ty::F32) | Expr::Cast(_, Ty::F32) | Expr::FConst(_, Ty::F32) => Some(32),
        Expr::Deref(_, Ty::F64) | Expr::Cast(_, Ty::F64) | Expr::FConst(_, Ty::F64) => Some(64),
        Expr::Var(Key::Tmp(id)) => float_bits(st.temps.get(id)?, st),
        Expr::Bin(op, l, r) if op.is_float() => Some(float_bits(l, st)?.max(float_bits(r, st)?)),
        Expr::Ternary(_, a, b) => either_width(float_bits(a, st), float_bits(b, st)),
        Expr::Un(_, inner) => float_bits(inner, st),
        Expr::Call(name, args) if name == "rint" => args.first().and_then(|a| float_bits(a, st)),
        _ => None,
    }
}

/// Reads the value a float store stores as the float it is.
///
/// The lifter keys a global by its width alone, so the double an x87
/// `fld qword [g]` loads is `Var(Global(g, 64))`, a float only by the
/// declaration the text gives it; under a float store it is the float at
/// its address.
///
/// # Arguments
///
/// * `e` - The stored value.
fn as_float(e: &Expr) -> Expr {
    let ty = match e {
        Expr::Var(Key::Global(at, 32)) if *at < TLS_BASE => Some((*at, Ty::F32)),
        Expr::Var(Key::Global(at, 64)) if *at < TLS_BASE => Some((*at, Ty::F64)),
        _ => None,
    };
    match (ty, e) {
        (Some((at, ty)), _) => Expr::Deref(Box::new(Expr::Const(at)), ty),
        (None, Expr::Un(op, inner)) => Expr::Un(*op, Box::new(as_float(inner))),
        (None, other) => other.clone(),
    }
}

/// The float the low `fb` bits of `v` encode.
///
/// # Arguments
///
/// * `v` - The bits.
/// * `fb` - 32 or 64.
pub(super) fn float_of(v: u64, fb: u8) -> f64 {
    if fb == 32 {
        f64::from(f32::from_bits(lo32(v)))
    } else {
        f64::from_bits(v)
    }
}

/// A float operation a cast names a width for, computed at that width.
///
/// The cast is not a conversion. A scalar `fadd` of two bare registers
/// carries no type of its own, and the cast records the width the
/// instruction used, so the bits are that operation's. An integer under
/// the cast is `None` here and converts by [`integer_to_float`]. A float
/// constant of a different width is `None`, not a value read at the wrong
/// width.
///
/// # Arguments
///
/// * `e` - The cast's operand.
/// * `fb` - The width the cast names, 32 or 64.
/// * `leaf` - The bits of one operand.
pub(super) fn float_carried(
    e: &Expr,
    fb: u8,
    mut leaf: impl FnMut(&Expr) -> Option<u64>,
) -> Option<u64> {
    if !matches!(fb, 32 | 64) {
        return None;
    }
    let wrong = |e: &Expr| matches!(e, Expr::FConst(_, ty) if ty.bits() != fb);
    match e {
        Expr::Bin(op, _, _) if op.is_float() => float_scale_at(e, fb, leaf),
        Expr::Un(op @ (UnOp::Sqrt | UnOp::Fabs), inner) if !wrong(inner) => {
            float_un(*op, leaf(inner)?, fb)
        }
        Expr::Un(UnOp::Neg, inner) if inner.is_float() && !wrong(inner) => {
            Some(leaf(inner)? ^ (1u64 << (u32::from(fb) - 1)))
        }
        Expr::Const(_)
        | Expr::FConst(_, _)
        | Expr::Var(_)
        | Expr::Str(_)
        | Expr::Sp(_)
        | Expr::Bin(_, _, _)
        | Expr::Un(_, _)
        | Expr::Deref(_, _)
        | Expr::Cond(_)
        | Expr::Ternary(_, _, _)
        | Expr::Sext(_, _)
        | Expr::Cast(_, _)
        | Expr::Call(_, _) => None,
    }
}

/// A float cast of a bitwise cut of a float, as the bits, not the number.
///
/// The cut is the encoding ([`super::interp`] does the same for the
/// operator). Casting those bits to a float keeps them, zero above a
/// single: converting them would be the integer the bits happen to be.
/// Anything other than that cut is `None`, and the cast converts by
/// [`integer_to_float`].
///
/// # Arguments
///
/// * `e` - The cast's operand.
/// * `to` - The float the cast names.
/// * `leaf` - The bits of one operand.
pub(super) fn reinterpret_float(
    e: &Expr,
    to: Ty,
    mut leaf: impl FnMut(&Expr) -> Option<u64>,
) -> Option<u64> {
    let Expr::Bin(op @ (Op::And | Op::Or | Op::Xor), l, r) = e else {
        return None;
    };
    if !l.is_float() && !r.is_float() {
        return None;
    }
    let (a, b) = (leaf(l)?, leaf(r)?);
    let v = match op {
        Op::And => a & b,
        Op::Or => a | b,
        Op::Xor => a ^ b,
        _ => return None,
    };
    match to {
        Ty::F32 => Some(u64::from(lo32(v))),
        Ty::F64 => Some(v),
        Ty::U8 | Ty::U16 | Ty::U32 | Ty::U64 | Ty::U128 => None,
    }
}

/// A float operation whose operands carry no float type, computed at `fb`.
///
/// A fixed-point conversion scales its register by a power of two before
/// rounding. The register's bits are the float; it has no float type of
/// its own, so the ordinary evaluator stops. The scale is exact at `fb`,
/// which is the width the conversion recorded. A float constant of a
/// different width is `None`, not a value read at the wrong width.
///
/// # Arguments
///
/// * `e` - The operation. Anything other than a float binary is `None`.
/// * `fb` - The width, 32 or 64.
/// * `leaf` - The bits of one operand.
pub(super) fn float_scale_at(
    e: &Expr,
    fb: u8,
    mut leaf: impl FnMut(&Expr) -> Option<u64>,
) -> Option<u64> {
    if !matches!(fb, 32 | 64) {
        return None;
    }
    let Expr::Bin(op, l, r) = e else {
        return None;
    };
    if !op.is_float() {
        return None;
    }
    let width_ok = |e: &Expr| !matches!(e, Expr::FConst(_, ty) if ty.bits() != fb);
    if !width_ok(l) || !width_ok(r) {
        return None;
    }
    float_arith(*op, float_of(leaf(l)?, fb), float_of(leaf(r)?, fb), fb)
}

/// Applies a float binary operator at the width its operands carry, as the
/// emulator computes it, and returns the result's bits.
///
/// A single's operation rounds its result to a single the way the
/// machine's `*ss` does, at the operation and not at the store, so a
/// quotient never rounds twice; a double's computes in a double. The
/// operands arrive as doubles over the same bits and narrow to `bits`
/// first, exactly for a value that width already holds.
///
/// # Arguments
///
/// * `op` - The operator.
/// * `l` - The left operand.
/// * `r` - The right operand.
/// * `bits` - The width both operands carry, 32 or 64.
///
/// # Returns
///
/// The result's bits, or `None` for an operator that is not a float one.
#[expect(
    clippy::cast_possible_truncation,
    reason = "narrowing a double to the single its operation computes in is the rounding itself"
)]
pub(super) fn float_arith(op: Op, l: f64, r: f64, bits: u8) -> Option<u64> {
    macro_rules! f {
        ($t:ty, $from:expr, $to:expr) => {{
            let (x, y): ($t, $t) = ($from(l), $from(r));
            let v: $t = match op {
                Op::FAdd => x + y,
                Op::FSub => x - y,
                Op::FMul => x * y,
                Op::FDiv => x / y,
                Op::FMin => {
                    if x < y {
                        x
                    } else {
                        y
                    }
                }
                Op::FMax => {
                    if x > y {
                        x
                    } else {
                        y
                    }
                }
                Op::Add
                | Op::Sub
                | Op::Mul
                | Op::Div
                | Op::Rem
                | Op::SDiv
                | Op::SRem
                | Op::And
                | Op::Or
                | Op::Xor
                | Op::Shl
                | Op::Shr
                | Op::Sar
                | Op::Rol(_)
                | Op::Ror(_)
                | Op::MulHi(_)
                | Op::SMulHi(_)
                | Op::SMulO(_)
                | Op::UAddO(_)
                | Op::USubO(_) => return None,
            };
            Some($to(v))
        }};
    }
    match bits {
        64 => f!(f64, |v: f64| v, f64::to_bits),
        _ => f!(f32, |v: f64| v as f32, |v: f32| u64::from(v.to_bits())),
    }
}

/// Applies a float unary operator at the width its operand carries, as
/// the emulator computes it, and returns the result's bits.
///
/// `fabs` clears the sign bit of the width, `sqrt` takes the square root
/// in the width's own arithmetic, so a single's root rounds to a single
/// the way the machine's `sqrtss` does.
///
/// # Arguments
///
/// * `op` - The operator, [`UnOp::Sqrt`] or [`UnOp::Fabs`].
/// * `v` - The operand's bits.
/// * `bits` - The width the operand carries, 32 or 64.
///
/// # Returns
///
/// The result's bits, or `None` for an operator that is not a float one.
pub(super) fn float_un(op: UnOp, v: u64, bits: u8) -> Option<u64> {
    match op {
        UnOp::Fabs => Some(v & !(1u64 << (u32::from(bits) - 1))),
        UnOp::Sqrt => match bits {
            64 => Some(f64::from_bits(v).sqrt().to_bits()),
            _ => Some(u64::from(f32::from_bits(lo32(v)).sqrt().to_bits())),
        },
        UnOp::Neg
        | UnOp::Not
        | UnOp::Bswap
        | UnOp::Tzcnt
        | UnOp::Lzcnt
        | UnOp::Popcnt
        | UnOp::Bsf
        | UnOp::Bsr => None,
    }
}

/// The integer a float cast converts, and whether that integer is signed.
///
/// A sign extension is signed, including from a full 64-bit register,
/// which [`sext`] does not re-extend. Anything else is the unsigned value
/// of its bits: an unsigned conversion masks a narrower source first, so
/// the high bit of a 32-bit value is already clear.
///
/// # Arguments
///
/// * `inner` - The cast's operand.
/// * `eval` - The bits of one subexpression.
pub(super) fn cast_integer(
    inner: &Expr,
    mut eval: impl FnMut(&Expr) -> Option<u64>,
) -> Option<(u64, bool)> {
    match inner {
        Expr::Sext(x, bits) => {
            let v = eval(x)?;
            let v = if *bits >= 64 { v } else { sext(v, *bits)? };
            Some((v, true))
        }
        other => Some((eval(other)?, false)),
    }
}

/// An integer rounded to `to`, the way `scvtf` and `ucvtf` do.
///
/// The value becomes a double first and a single narrows that double.
/// For an integer that is the same rounding as a direct conversion to a
/// single, and it is the rounding the fixed-point form divides before.
///
/// # Arguments
///
/// * `v` - The integer's bits, already sign-extended when `signed`.
/// * `signed` - Whether those bits are signed.
/// * `to` - The float written. Anything else returns `v`.
#[expect(
    clippy::cast_precision_loss,
    reason = "an integer converted to a float rounds, as the conversion does"
)]
pub(super) fn integer_to_float(v: u64, signed: bool, to: Ty) -> u64 {
    let wide = if signed {
        v.cast_signed() as f64
    } else {
        v as f64
    };
    match to {
        Ty::F32 => {
            #[expect(
                clippy::cast_possible_truncation,
                reason = "narrowing the double to a single is the conversion's last rounding"
            )]
            let n = wide as f32;
            u64::from(n.to_bits())
        }
        Ty::F64 => wide.to_bits(),
        Ty::U8 | Ty::U16 | Ty::U32 | Ty::U64 | Ty::U128 => v,
    }
}

/// Converts a float's bits to the width a store gives it, rounding a
/// double to a single as an x87 store to a single does.
///
/// # Arguments
///
/// * `v` - The float's bits.
/// * `from` - Its width, or `None` for an integer.
/// * `to` - The type stored.
#[expect(
    clippy::cast_possible_truncation,
    reason = "rounding a double to a single is the conversion the store makes"
)]
pub(super) fn convert_float(v: u64, from: Option<u8>, to: Ty) -> u64 {
    match (from, to) {
        (Some(64), Ty::F32) => u64::from((f64::from_bits(v) as f32).to_bits()),
        (Some(32), Ty::F64) => f64::from(f32::from_bits(lo32(v))).to_bits(),
        _ => v,
    }
}

/// Tells whether a value the emulator left and a lifted one agree.
///
/// Equal in the low `bits`, or, for a float, both NaNs: the x87 load the
/// emulator models quiets a signaling NaN the lifter copies as it is.
///
/// # Arguments
///
/// * `a` - One value.
/// * `b` - The other.
/// * `bits` - The width compared.
/// * `float` - Whether the value is a float.
pub(super) fn agree(a: u64, b: u64, bits: u8, float: bool) -> bool {
    let nan = |v: u64| match bits {
        32 => f32::from_bits(lo32(v)).is_nan(),
        64 => f64::from_bits(v).is_nan(),
        _ => false,
    };
    (a ^ b) & low(bits) == 0 || (float && nan(a) && nan(b))
}

/// Converts a float's bits to an integer the way `cvttss2si` does: toward
/// zero, and to the integer indefinite (the most negative value) when the
/// float is a NaN or does not fit.
///
/// A 32-bit or 64-bit destination uses that signed range. An 8-bit or
/// 16-bit destination uses its own: `fist` and `fisttp` of a word store
/// the indefinite integer there, not the low bits of a wider conversion.
///
/// # Arguments
///
/// * `v` - The float's bits.
/// * `fb` - The float's width, 32 or 64.
/// * `bits` - The integer's width.
#[expect(
    clippy::cast_possible_truncation,
    clippy::cast_precision_loss,
    reason = "the range checks guarantee the truncated float fits the integer, and the bound is a power of two"
)]
pub(super) fn float_to_int(v: u64, fb: u8, bits: u8) -> u64 {
    let f = float_of(v, fb).trunc();
    if matches!(bits, 8 | 16) {
        let shift = u32::from(bits) - 1;
        let top = (1u64 << shift) as f64;
        if f.is_nan() || f < -top || f >= top {
            return 1u64 << shift;
        }
        return (f as i64).cast_unsigned() & low(bits);
    }
    if bits <= 32 {
        if f.is_nan() || !(-2_147_483_648.0..=2_147_483_647.0).contains(&f) {
            return 0x8000_0000;
        }
        (f as i32).cast_unsigned().into()
    } else {
        if f.is_nan() || !(-9_223_372_036_854_775_808.0..9_223_372_036_854_775_808.0).contains(&f) {
            return 0x8000_0000_0000_0000;
        }
        (f as i64).cast_unsigned()
    }
}

/// Evaluates a condition by folding its flags' operands to constants and
/// asking the lifter's own condition logic.
///
/// # Arguments
///
/// * `c` - The condition.
/// * `st` - The starting state.
/// * `reads` - The memory ranges read.
/// * `d` - How much deeper to look.
pub(super) fn eval_cond<M: Bench>(
    c: &Cond,
    st: &State<'_, M>,
    reads: &mut Vec<(u64, u64)>,
    d: u8,
) -> Option<bool> {
    if let Flags::Float(a, b, fb) = &c.flags {
        let l = float_of(eval(a, st, reads, d)?, *fb);
        let r = float_of(eval(b, st, reads, d)?, *fb);
        return super::expr::float_cc(c.cc.0, l, r);
    }
    if let Flags::Cmp(a, b, _) = &c.flags
        && let Some(fb) = float_bits(a, st).or_else(|| float_bits(b, st))
    {
        let l = float_of(eval(a, st, reads, d)?, fb);
        let r = float_of(eval(b, st, reads, d)?, fb);
        return super::expr::float_cc(c.cc.0, l, r);
    }
    let mut k = |e: &Expr| eval(e, st, reads, d).map(Expr::Const);
    let flags = match &c.flags {
        Flags::Cmp(a, b, w) => Flags::Cmp(k(a)?, k(b)?, *w),
        Flags::Float(..) => return None,
        Flags::Test(a, b, w) => Flags::Test(k(a)?, k(b)?, *w),
        Flags::Result(a, w) => Flags::Result(k(a)?, *w),
        Flags::Add(a, b, w) => Flags::Add(k(a)?, k(b)?, *w),
        Flags::Carry(a) => Flags::Carry(k(a)?),
        Flags::Shift(a, w, b) => Flags::Shift(k(a)?, *w, k(b)?),
        Flags::Truth(a, cc) => Flags::Truth(k(a)?, *cc),
        Flags::Unknown => return None,
    };
    Cond { cc: c.cc, flags }.eval()
}

/// Tells whether the lifter writes an instruction as a statement whose
/// register results the environment does not hold: an atomic exchange, a
/// processor query, a counter read.
///
/// An `xadd` is not one: its flags are those of the addition it performs,
/// so the branch after it compares while its register result counts as
/// unreadable, the environment not holding the old value it received.
/// A `cmpxchg`'s flags name the variable the exchange leaves in `rax`,
/// which the evaluator would read as the entry accumulator rather than the
/// exchanged value, so the block stays skipped rather than comparing on a
/// value neither side computed.
///
/// # Arguments
///
/// * `i` - The instruction.
fn statement_only(i: &Instruction) -> bool {
    i.has_lock_prefix()
        || matches!(
            i.mnemonic(),
            Mnemonic::Cmpxchg
                | Mnemonic::Cmpxchg8b
                | Mnemonic::Cmpxchg16b
                | Mnemonic::Cpuid
                | Mnemonic::Rdtsc
                | Mnemonic::Rdtscp
                | Mnemonic::Rdrand
                | Mnemonic::Rdseed
                | Mnemonic::Xgetbv
        )
        || (i.mnemonic() == Mnemonic::Xchg
            && (i.op0_kind() == OpKind::Memory || i.op1_kind() == OpKind::Memory))
}

/// Checks the blocks of some functions against the emulator.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - The functions and their blocks.
/// * `entries` - The functions to check.
/// * `seed` - The starting state's seed; the same seed checks the same
///   way every time.
///
/// # Returns
///
/// What was compared and every disagreement.
#[must_use]
pub fn verify(program: &Program, analysis: &Analysis, entries: &[u64], seed: u64) -> Verified {
    in_parts(entries, |part| verify_some(program, analysis, part, seed))
}

/// Checks some functions in parts, one thread per part, and adds up what
/// the parts found in the order of `entries`.
///
/// # Arguments
///
/// * `entries` - The functions to check.
/// * `some` - Checks one part on the calling thread.
pub(super) fn in_parts(entries: &[u64], some: impl Fn(&[u64]) -> Verified + Sync) -> Verified {
    let threads = std::thread::available_parallelism()
        .map_or(1, std::num::NonZeroUsize::get)
        .min(entries.len().div_ceil(PAR_MIN).max(1));
    if threads <= 1 {
        return some(entries);
    }
    let chunk = entries.len().div_ceil(threads);
    let some = &some;
    let parts: Vec<Verified> = std::thread::scope(|scope| {
        let handles: Vec<_> = entries
            .chunks(chunk)
            .map(|part| scope.spawn(move || some(part)))
            .collect();
        handles.into_iter().filter_map(|h| h.join().ok()).collect()
    });
    let mut out = Verified::default();
    for part in parts {
        out.merge(part);
    }
    out
}

/// Tells whether an instruction aligns the stack pointer (`and rsp, -16`).
///
/// # Arguments
///
/// * `i` - The instruction.
pub(super) fn aligns_stack(i: &Instruction) -> bool {
    i.mnemonic() == Mnemonic::And
        && i.op0_kind() == OpKind::Register
        && matches!(i.op0_register(), Register::RSP | Register::ESP)
        && !matches!(i.op1_kind(), OpKind::Register | OpKind::Memory)
}

/// Decodes a block up to its first control transfer.
///
/// # Arguments
///
/// * `ctx` - The function's decompilation state, for decoding.
/// * `block` - The block.
///
/// # Returns
///
/// The straight-line instructions; the conditional branch that ends them
/// when it is a near jump that goes somewhere else than either way on;
/// and the address the straight line stops at.
fn straight_line(
    ctx: &Ctx<'_>,
    block: &BasicBlock,
) -> (Vec<Instruction>, Option<Instruction>, u64) {
    let mut instrs = Vec::new();
    let mut va = block.start;
    while va < block.end {
        let Some(i) = ctx.decode(va) else { break };
        if i.flow_control() != FlowControl::Next {
            let target = i.near_branch_target();
            let jcc = (i.flow_control() == FlowControl::ConditionalBranch
                && matches!(
                    i.op0_kind(),
                    OpKind::NearBranch16 | OpKind::NearBranch32 | OpKind::NearBranch64
                )
                && target != i.next_ip()
                && target != i.ip())
            .then_some(i);
            return (instrs, jcc, va);
        }
        va = i.next_ip();
        instrs.push(i);
    }
    (instrs, None, va)
}

/// The registers some instruction of a block writes, at the width the
/// lifter keys them by.
///
/// # Arguments
///
/// * `instrs` - The block's instructions.
/// * `width` - The register width, 32 or 64.
fn written_registers(instrs: &[Instruction], width: u8) -> Vec<Register> {
    let mut written = Vec::new();
    let mut info = InstructionInfoFactory::new();
    for i in instrs {
        for u in info.info(i).used_registers() {
            if matches!(
                u.access(),
                OpAccess::Write
                    | OpAccess::ReadWrite
                    | OpAccess::CondWrite
                    | OpAccess::ReadCondWrite
            ) {
                written.push(if width == 32 {
                    u.register().full_register32()
                } else {
                    u.register().full_register()
                });
            }
        }
    }
    written
}

/// What a block's comparisons suggest a register start next to.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum Near {
    /// The constant it is compared with.
    Constant(u64),
    /// The register it is compared with, which is seeded before it.
    Register(Key),
}

impl Near {
    /// A seed next to the comparand: one below it, it, or one above it.
    ///
    /// # Arguments
    ///
    /// * `regs` - The registers seeded so far.
    /// * `r` - A random value, which picks the offset and stands in for a
    ///   register not seeded yet.
    pub(super) fn seed(self, regs: &BTreeMap<Key, u64>, r: u64) -> u64 {
        let base = match self {
            Self::Constant(k) => k,
            Self::Register(other) => regs.get(&other).copied().unwrap_or(r),
        };
        base.wrapping_add((r >> 2) % 3).wrapping_sub(1)
    }
}

/// Reads the registers a block compares (`cmp`, `test`, `sub`) with a
/// constant or with another register.
///
/// A random seed leaves a branch on equality or on a boundary taken one
/// way, so a wrong condition code passes, while a seed next to the
/// comparand takes it both ways across seeds. A register compared with
/// itself (`test eax, eax`) starts next to zero.
///
/// # Arguments
///
/// * `instrs` - The block's instructions.
/// * `regs` - The registers seeded, in seeding order.
/// * `width` - The register width, 32 or 64.
fn comparands(
    instrs: &[Instruction],
    regs: &[(&str, Register)],
    width: u8,
) -> BTreeMap<Register, Near> {
    let full = |r: Register| {
        if width == 32 {
            r.full_register32()
        } else {
            r.full_register()
        }
    };
    let rank = |r: Register| regs.iter().position(|&(_, x)| x == r);
    let mut near = BTreeMap::new();
    for i in instrs.iter().filter(|i| {
        matches!(i.mnemonic(), Mnemonic::Cmp | Mnemonic::Test | Mnemonic::Sub)
            && i.op0_kind() == OpKind::Register
    }) {
        let r0 = full(i.op0_register());
        match i.op1_kind() {
            OpKind::Register => {
                let r1 = full(i.op1_register());
                if r0 == r1 {
                    near.insert(r0, Near::Constant(0));
                } else if let (Some(a), Some(b)) = (rank(r0), rank(r1)) {
                    let (first, second) = if a < b { (r0, r1) } else { (r1, r0) };
                    near.insert(second, Near::Register(Key::Reg(first)));
                }
            }
            OpKind::Memory => {}
            _ => {
                if let Ok(k) = i.try_immediate(1) {
                    near.insert(r0, Near::Constant(k));
                }
            }
        }
    }
    near
}

/// What every block of one verification shares.
struct Sweep<'p> {
    /// The image's emulator before any run, cloned for each block: building
    /// one plants its thread block, which costs more than the block's run.
    pristine: Emulator<'p>,
    /// The general registers compared, named as the emulator names them.
    regs: &'static [(&'static str, Register)],
    /// The register width, 32 or 64.
    width: u8,
    /// The verification's seed.
    seed: u64,
}

impl<'p> Sweep<'p> {
    /// Sets up a verification of one image.
    ///
    /// # Arguments
    ///
    /// * `program` - The image.
    /// * `seed` - The verification's seed.
    ///
    /// # Returns
    ///
    /// The sweep, or `None` when the image's bitness is unknown.
    fn new(program: &'p Program, seed: u64) -> Option<Self> {
        let (regs, width): (&'static [(&'static str, Register)], u8) =
            if program.arch.bitness()? == 32 {
                (&REGS_32, 32)
            } else {
                (&REGS, 64)
            };
        Some(Self {
            pristine: Emulator::new(program, 0)?,
            regs,
            width,
            seed,
        })
    }

    /// Builds the decompilation state a function's blocks are lifted in:
    /// nothing written out, and no flags carried between blocks, since
    /// each block starts from a state of its own.
    ///
    /// # Arguments
    ///
    /// * `program` - The image.
    /// * `analysis` - The functions and their blocks.
    /// * `overlay` - The names in force (none).
    /// * `f` - The function.
    fn ctx<'a>(
        &self,
        program: &'a Program,
        analysis: &'a Analysis,
        overlay: &'a Overlay,
        f: &Function,
    ) -> Ctx<'a> {
        let starts = f.blocks.iter().map(|b| b.start).collect();
        let bitness = u32::from(self.width);
        let mut ctx = new_ctx(program, analysis, overlay, f, bitness, starts, &[]);
        ctx.symbolic_only = true;
        ctx.flag_readers = vec![false; f.blocks.len()];
        ctx.rebase_flags = vec![None; f.blocks.len()];
        ctx
    }

    /// Runs one block both ways and compares every fact.
    ///
    /// # Arguments
    ///
    /// * `ctx` - The function's decompilation state, symbolic only.
    /// * `entry` - The function's entry.
    /// * `block` - The block.
    /// * `out` - Where the counts and disagreements go.
    ///
    /// # Errors
    ///
    /// Why the block was not checked.
    fn check(
        &self,
        ctx: &mut Ctx<'_>,
        entry: u64,
        block: &BasicBlock,
        out: &mut Verified,
    ) -> Result<(), &'static str> {
        let ran = self.run(ctx, entry, block, out)?;
        out.checked += 1;
        ran.compare(out);
        Ok(())
    }

    /// Runs one block on the emulator and through the lifter from one
    /// seeded state.
    ///
    /// # Arguments
    ///
    /// * `ctx` - The function's decompilation state, symbolic only.
    /// * `entry` - The function's entry.
    /// * `block` - The block.
    /// * `out` - Where the instructions the emulator lacks are tallied.
    ///
    /// # Returns
    ///
    /// Both runs, ready to compare.
    ///
    /// # Errors
    ///
    /// Why the block cannot be checked.
    fn run(
        &self,
        ctx: &mut Ctx<'_>,
        entry: u64,
        block: &BasicBlock,
        out: &mut Verified,
    ) -> Result<Ran<'_, Emulator<'p>, X86Regs>, &'static str> {
        let (instrs, jcc, end) = straight_line(ctx, block);
        if instrs.is_empty() {
            return Err("no straight-line code");
        }
        if instrs.iter().any(statement_only) {
            return Err("an atomic or system instruction the lifter writes as a statement");
        }
        let mut aligns = instrs.iter().filter(|i| aligns_stack(i));
        let align = aligns.next();
        let aligned = align.is_some();
        if align.is_some_and(|_| aligns.next().is_some()) {
            return Err("a frame alignment whose slack the seed cannot zero");
        }
        let mut rng = Rng(self.seed ^ block.start.rotate_left(17) ^ GOLDEN);
        let _ = rng.next();
        let fill = rng.next();
        let reps = instrs
            .iter()
            .filter(|i| i.has_rep_prefix() || i.has_repe_prefix() || i.has_repne_prefix())
            .count();
        let mut emu = self.pristine.clone();
        emu.set_budget(instrs.len() + 1 + reps * REGION_MAX);
        emu.set_permissive(true);
        emu.set_fill(Some(fill));
        if let Some(i) = align {
            let Some(to) = i
                .try_immediate(1)
                .ok()
                .map(|c| c.wrapping_neg())
                .filter(|a| a.is_power_of_two() && *a <= 4096)
            else {
                return Err("a frame alignment whose slack the seed cannot zero");
            };
            let slack = self.slack(&instrs, i, to, fill, reps, out)?;
            let seeded = emu.register("rsp").unwrap_or(0).wrapping_sub(slack);
            emu.set_register("rsp", seeded);
        }
        let mut st = State {
            pristine: &self.pristine,
            fill,
            regs: BTreeMap::new(),
            rsp: emu.register("rsp").unwrap_or(0),
            stack: BTreeMap::new(),
            width: self.width,
            temps: BTreeMap::new(),
            tls_block: 0,
        };
        let near = comparands(&instrs, self.regs, self.width);
        for &(name, reg) in self.regs {
            let r = rng.next();
            let v = match near.get(&reg) {
                Some(n) if r & 3 != 0 => n.seed(&st.regs, r),
                _ => r,
            } & low(self.width);
            emu.set_register(name, v);
            st.regs.insert(Key::Reg(reg), v);
        }
        for &(_, seg) in SEGS
            .iter()
            .filter(|&&(_, s)| !matches!(s, Register::FS | Register::GS))
        {
            st.regs.insert(Key::Reg(seg), 0);
        }
        for word in -STACK_WORDS..STACK_WORDS {
            let at = st.rsp.wrapping_add_signed(word * 8);
            for (i, b) in (0u64..).zip(rng.next().to_le_bytes()) {
                emu.poke(at.wrapping_add(i), b);
                st.stack.insert(at.wrapping_add(i), b);
            }
        }
        st.tls_block = st.resolve_tls();
        emu.stop_at(Some(end));
        let run = emu.run(block.start);
        match run.stop {
            Stop::Stopped(at) if at == end => {}
            Stop::Unmodeled(ref what) => {
                let kind = what.split(" at 0x").next().unwrap_or(what);
                *out.unmodeled.entry(kind.to_owned()).or_default() += 1;
                return Err("an instruction the emulator does not model");
            }
            Stop::Fault(_) => return Err("a fault on the emulator"),
            Stop::Budget => return Err("a repeat count past the regions compared"),
            _ => return Err("the emulator stopped early"),
        }
        let stored: FxHashSet<u64> = run.history.iter().map(|w| w.addr).collect();
        let written = written_registers(&instrs, self.width);
        let mut lifted_instrs = instrs;
        lifted_instrs.extend(jcc);
        ctx.probe = Some(Probe::default());
        let mut env = Env::entry();
        let lifted = exec_block(
            ctx,
            &lifted_instrs,
            None,
            &mut env,
            Pass::Dataflow,
            None,
            BlockFacts::default(),
        );
        let probe = ctx.probe.take().unwrap_or_default();
        if lifted.unmodeled > 0 {
            return Err(
                "an instruction the lifter leaves as asm, whose result the expressions after it name but do not compute",
            );
        }
        if aligned && env.sp.is_none() {
            return Err("a frame alignment whose slack the seed cannot zero");
        }
        st.temps = probe.temps;
        Ok(Ran {
            function: entry,
            block: block.start,
            st,
            emu,
            stored,
            regs: X86Regs {
                names: self.regs,
                written,
            },
            env,
            effects: probe.effects,
            branch: jcc
                .map(|j| Jcc {
                    ip: j.ip(),
                    target: j.near_branch_target(),
                })
                .zip(lifted.branch.map(|b| b.cond)),
        })
    }

    /// Measures the slack a block's stack alignment drops, on the machine.
    ///
    /// The stack pointer moves between the block's start and its alignment
    /// only by pushes, pops and adds the emulator models exactly, so a run
    /// stopped just before the alignment states the pointer the alignment
    /// is about to round, and the slack is that value's low bits. Seeding
    /// the checked run's stack pointer back by it makes the alignment
    /// write the value the pointer already holds, which is the zero slack
    /// the lifter tracks the frame under.
    ///
    /// # Arguments
    ///
    /// * `instrs` - The block's straight-line instructions.
    /// * `align` - The aligning instruction.
    /// * `to` - The alignment it rounds to, a power of two.
    /// * `fill` - The seed of the bytes nothing backs.
    /// * `reps` - The block's `rep` instructions, for the run's budget.
    /// * `out` - Where an instruction the emulator lacks is tallied.
    ///
    /// # Returns
    ///
    /// The slack in bytes, or `Err` why the alignment cannot be reached.
    ///
    /// # Errors
    ///
    /// Why the alignment cannot be reached: an instruction the emulator
    /// does not model or a fault before it, a repeat past the budget, or a
    /// stop the straight line does not explain.
    fn slack(
        &self,
        instrs: &[Instruction],
        align: &Instruction,
        to: u64,
        fill: u64,
        reps: usize,
        out: &mut Verified,
    ) -> Result<u64, &'static str> {
        let mut emu = self.pristine.clone();
        emu.set_budget(instrs.len() + 2 + reps * REGION_MAX);
        emu.set_permissive(true);
        emu.set_fill(Some(fill));
        emu.stop_at(Some(align.ip()));
        let start = instrs.first().map_or(align.ip(), Instruction::ip);
        match emu.run(start).stop {
            Stop::Stopped(at) if at == align.ip() => {
                Ok(emu.register("rsp").unwrap_or(0) & to.wrapping_sub(1))
            }
            Stop::Unmodeled(ref what) => {
                let kind = what.split(" at 0x").next().unwrap_or(what);
                *out.unmodeled.entry(kind.to_owned()).or_default() += 1;
                Err("an instruction the emulator does not model")
            }
            Stop::Fault(_) => Err("a fault on the emulator"),
            Stop::Budget => Err("a repeat count past the regions compared"),
            _ => Err("the emulator stopped early"),
        }
    }
}

/// A block's conditional branch, as the check steps it on the machine.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) struct Jcc {
    /// The branch's address.
    pub(super) ip: u64,
    /// Where it goes when taken.
    pub(super) target: u64,
}

/// The register facts an x86 block's check compares beyond what every
/// instruction set's does.
pub(super) struct X86Regs {
    /// The general registers compared, named as the emulator names them.
    names: &'static [(&'static str, Register)],
    /// The registers some instruction of the block writes.
    written: Vec<Register>,
}

/// One block run both ways, ready to compare.
pub(super) struct Ran<'p, M, R> {
    /// The function's entry.
    pub(super) function: u64,
    /// The block's start.
    pub(super) block: u64,
    /// The state both runs started from.
    pub(super) st: State<'p, M>,
    /// The machine, stopped where the straight line ends.
    pub(super) emu: M,
    /// Addresses the machine wrote.
    pub(super) stored: FxHashSet<u64>,
    /// The register facts of the block's instruction set.
    pub(super) regs: R,
    /// The lifter's environment where the straight line ends.
    pub(super) env: Env,
    /// The lifter's memory writes, in program order.
    pub(super) effects: Vec<Effect>,
    /// The conditional branch ending the block, with the condition the
    /// lifter says it is taken under.
    pub(super) branch: Option<(Jcc, Cond)>,
}

impl Ran<'_, Emulator<'_>, X86Regs> {
    /// Compares every fact: registers, the x87 stack, the xmm lanes, slots,
    /// stores, then the branch.
    ///
    /// # Arguments
    ///
    /// * `out` - Where the counts and disagreements go.
    fn compare(mut self, out: &mut Verified) {
        self.registers(out);
        self.x87(out);
        self.xmm(out);
        self.segments(out);
        let held = self.slots(out);
        self.stores(&held, out);
        if let Some((jcc, cond)) = self.branch.take() {
            self.step_branch(jcc, &cond, out);
        }
    }
}

impl<M: Bench, R> Ran<'_, M, R> {
    /// Evaluates a lifted value under the starting state.
    ///
    /// # Arguments
    ///
    /// * `e` - The value.
    pub(super) fn read(&self, e: &Expr) -> Read {
        let mut reads = Vec::new();
        let v = eval(e, &self.st, &mut reads, EVAL_DEPTH);
        if self.touches(&reads) {
            return Read::Stale;
        }
        v.map_or(Read::Unreadable, Read::Value)
    }

    /// Tells whether memory ranges overlap a byte the emulator wrote.
    ///
    /// # Arguments
    ///
    /// * `reads` - The ranges, as start and length.
    fn touches(&self, reads: &[(u64, u64)]) -> bool {
        reads
            .iter()
            .any(|&(at, n)| (0..n).any(|i| self.stored.contains(&at.wrapping_add(i))))
    }

    /// A byte of memory as the machine left it.
    ///
    /// # Arguments
    ///
    /// * `at` - The address.
    fn after(&self, at: u64) -> u8 {
        self.emu
            .byte_at(at)
            .unwrap_or_else(|| fill_byte(self.st.fill, at))
    }

    /// Records a disagreement in this block.
    ///
    /// # Arguments
    ///
    /// * `out` - Where it goes.
    /// * `fact` - Its kind.
    /// * `place` - Which fact.
    /// * `values` - What the emulator left, what the lifted expression
    ///   evaluates to, and the width compared.
    /// * `expr` - The lifted expression.
    pub(super) fn disagree(
        &self,
        out: &mut Verified,
        fact: Fact,
        place: String,
        values: (u64, u64, u8),
        expr: String,
    ) {
        let (emulated, lifted, bits) = values;
        out.mismatches.push(Mismatch {
            function: self.function,
            block: self.block,
            fact,
            place,
            emulated,
            lifted,
            bits,
            expr,
        });
    }
}

impl Ran<'_, Emulator<'_>, X86Regs> {
    /// Compares every general register and the stack pointer.
    ///
    /// # Arguments
    ///
    /// * `out` - Where the counts and disagreements go.
    fn registers(&self, out: &mut Verified) {
        let (env, width) = (&self.env, self.st.width);
        for &(name, reg) in self.regs.names {
            let key = Key::Reg(reg);
            let Some(emulated) = self.emu.register(name) else {
                continue;
            };
            let lane = env.narrow.get(&key).copied().unwrap_or(64);
            let value = env.vals.get(&key);
            let (read, bits) = match value {
                None if self.regs.written.contains(&reg) && lane != 32 => (Read::Unreadable, lane),
                None => (
                    Read::Value(self.st.regs.get(&key).copied().unwrap_or(0)),
                    lane,
                ),
                Some(e) => (self.read(e), lane.clamp(8, 64)),
            };
            let Some(mut lifted) = out.count(Fact::Register, read) else {
                continue;
            };
            let bits = if width == 32 {
                bits.min(32)
            } else if bits == 32 {
                lifted &= low(32);
                64
            } else {
                bits
            };
            if (lifted ^ emulated) & low(bits) != 0 {
                let expr = value.map_or_else(|| "(unchanged)".to_owned(), |e| format!("{e:?}"));
                self.disagree(
                    out,
                    Fact::Register,
                    name.to_owned(),
                    (emulated, lifted, bits),
                    expr,
                );
            }
        }
        if let (Some(sp), Some(emulated)) = (env.sp, self.emu.register("rsp")) {
            let lifted = self.st.rsp.wrapping_add_signed(sp);
            out.count(Fact::Register, Read::Value(lifted));
            if (lifted ^ emulated) & low(width) != 0 {
                self.disagree(
                    out,
                    Fact::Register,
                    "rsp".to_owned(),
                    (emulated, lifted, width),
                    format!("rsp {sp:+}"),
                );
            }
        }
    }

    /// Compares the x87 register stack: each register the lifter holds a
    /// value for with the emulator's, and each it wrote nothing to with
    /// the zero an empty register holds there.
    ///
    /// Both sides start the block with the stack empty, as a call leaves
    /// it. A register the machine moved but nothing wrote moves as its own
    /// text variable, which the evaluator cannot read and counts rather
    /// than compares.
    ///
    /// # Arguments
    ///
    /// * `out` - Where the counts and disagreements go.
    fn x87(&self, out: &mut Verified) {
        let (top, fpu) = self.emu.x87();
        for i in 0..8 {
            let key = Key::Reg(st_register(i));
            let emulated = fpu[(top + i) % fpu.len()].to_bits();
            let read = match self.env.vals.get(&key) {
                Some(e) => match (self.read(e), float_bits(e, &self.st)) {
                    (Read::Value(v), Some(fb)) => Read::Value(float_of(v, fb).to_bits()),
                    (Read::Value(_), None) => Read::Unreadable,
                    (other, _) => other,
                },
                None => Read::Value(0),
            };
            let Some(lifted) = out.count(Fact::X87, read) else {
                continue;
            };
            if !agree(emulated, lifted, 64, true) {
                let expr = match self.env.vals.get(&key) {
                    Some(e) => format!("{e:?}"),
                    None if self.env.unset.contains(&key) => "(empty)".to_owned(),
                    None => "(unchanged)".to_owned(),
                };
                self.disagree(
                    out,
                    Fact::X87,
                    format!("st{i}"),
                    (emulated, lifted, 64),
                    expr,
                );
            }
        }
    }

    /// Compares the low lane of every xmm register with the emulator's, at
    /// the width the lifted expression carries.
    ///
    /// Both sides start the block with the registers clear and the sweep
    /// seeds nothing into them, so a register the lifter wrote nothing to
    /// still holds zero. A float expression's lane is the width it computes
    /// at ([`float_bits`]), so a single's lane compares as the single the
    /// machine's own `*ss` rounding left, never as a double's bits read
    /// over it; an integer lane compares as the 64-bit lane the lifter's
    /// variable is, or narrower when the environment says so. What the
    /// evaluator cannot read (the merge a register-to-register `movss`
    /// lifts to as a call, an unheld register's own variable) is counted,
    /// not compared. A lane whose lifted variable is a general register
    /// read whole, where the machine wrote only a 32-bit lane and the
    /// difference lives above those 32 bits (`movd xmm, r32` before the
    /// lift narrowed its source to the bits the machine keeps), is the lane
    /// known roughness and is counted apart, not compared: a
    /// defect of the lifting to fix in the lifter or to excuse, never one
    /// to hide in a widened compare.
    ///
    /// # Arguments
    ///
    /// * `out` - Where the counts and disagreements go.
    fn xmm(&self, out: &mut Verified) {
        let lanes = self.emu.xmm();
        for (i, &reg) in XMMS.iter().enumerate() {
            let key = Key::Reg(reg);
            let held = self.env.vals.get(&key);
            let float = held.and_then(|e| float_bits(e, &self.st));
            let bits = float
                .or_else(|| self.env.narrow.get(&key).copied())
                .unwrap_or(64);
            let mask = u128::from(low(bits));
            #[expect(
                clippy::cast_possible_truncation,
                reason = "the lane is masked to the compared width first, so the cast drops no bit"
            )]
            let emulated = (lanes[i] & mask) as u64;
            let read = match held.map_or(Read::Value(0), |e| self.read(e)) {
                Read::Value(v)
                    if float.is_none()
                        && bits == 64
                        && matches!(held, Some(Expr::Var(Key::Reg(_))))
                        && (v ^ emulated) != 0
                        && (v ^ emulated) & low(32) == 0 =>
                {
                    Read::Rough
                }
                read => read,
            };
            let Some(lifted) = out.count(Fact::Xmm, read) else {
                continue;
            };
            if !agree(emulated, lifted, bits, float.is_some()) {
                let expr = held.map_or_else(|| "(unchanged)".to_owned(), |e| format!("{e:?}"));
                self.disagree(
                    out,
                    Fact::Xmm,
                    format!("xmm{i}"),
                    (emulated, lifted, bits),
                    expr,
                );
            }
        }
    }

    /// Compares every segment register's selector with the emulator's, at
    /// the sixteen bits a move writes.
    ///
    /// Both sides start the block with the registers clear, so a register
    /// the lifter wrote nothing to still holds zero and compares as the
    /// unchanged value both started from; the check's value is the rare
    /// block the machine moves a segment register in, where a lift that
    /// dropped the move or wrote it at the wrong width is caught. `fs` and
    /// `gs` start from no value the evaluator can read — a segment-prefixed
    /// address adds their selector as though it were the thread-block base
    /// the machine adds — so a block that moves them counts its fact as
    /// unreadable instead of comparing it, while the TLS slots a walk
    /// through them reads compare through the resolved base
    /// ([`State::resolve_tls`]).
    ///
    /// # Arguments
    ///
    /// * `out` - Where the counts and disagreements go.
    fn segments(&self, out: &mut Verified) {
        let segs = self.emu.segments();
        for (i, &(name, reg)) in SEGS.iter().enumerate() {
            let emulated = segs[i] & low(16);
            let held = self.env.vals.get(&Key::Reg(reg));
            let read = held.map_or(Read::Value(0), |e| self.read(e));
            let Some(lifted) = out.count(Fact::Segment, read) else {
                continue;
            };
            if (lifted ^ emulated) & low(16) != 0 {
                let expr = held.map_or_else(|| "(unchanged)".to_owned(), |e| format!("{e:?}"));
                self.disagree(
                    out,
                    Fact::Segment,
                    name.to_owned(),
                    (emulated, lifted, 16),
                    expr,
                );
            }
        }
    }
}

impl<M: Bench, R> Ran<'_, M, R> {
    /// Compares every stack slot the lifter holds a value for with the
    /// machine's stack.
    ///
    /// # Arguments
    ///
    /// * `out` - Where the counts and disagreements go.
    ///
    /// # Returns
    ///
    /// The bytes the lifter's slots hold, whose value this compared; the
    /// store check leaves them to it.
    pub(super) fn slots(&self, out: &mut Verified) -> FxHashSet<u64> {
        let (env, mask) = (&self.env, low(self.st.width));
        let mut held = FxHashSet::default();
        for (&k, &bits) in &env.slot_bits {
            let at = self.st.rsp.wrapping_add_signed(k) & mask;
            let n = u64::from(bits / 8).max(1);
            held.extend((0..n).map(|i| at.wrapping_add(i) & mask));
            let Some(e) = env.vals.get(&Key::Slot(k)) else {
                continue;
            };
            let read = if n > 8 {
                Read::Unreadable
            } else {
                self.read(e)
            };
            let Some(v) = out.count(Fact::Slot, read) else {
                continue;
            };
            let float = float_bits(e, &self.st);
            let to = match (bits, float) {
                (32, Some(_)) => Ty::F32,
                (64, Some(_)) => Ty::F64,
                _ => Ty::U64,
            };
            let lifted = convert_float(v, float, to) & low(bits);
            let emulated = word(n, |i| self.after(at.wrapping_add(i) & mask));
            if !agree(emulated, lifted, bits, float.is_some()) {
                let place = if k < 0 {
                    format!("{}-{:#x}", M::SP, k.unsigned_abs())
                } else {
                    format!("{}+{k:#x}", M::SP)
                };
                self.disagree(
                    out,
                    Fact::Slot,
                    place,
                    (emulated, lifted, bits),
                    format!("{e:?}"),
                );
            }
        }
        held
    }

    /// The bytes a lifted memory write covers, as start and length, when
    /// the evaluator can tell.
    ///
    /// A write to a TLS slot names the constant pseudo-address the lift
    /// folded (`TLS_BASE` plus its offset), translated to the address the
    /// entry state walks the TLS block to ([`State::resolve_tls`]) the way
    /// a read is; a write whose address the evaluator cannot read, or one
    /// that runs past the top of the address space (where the processor
    /// faults and neither side models it), has none.
    ///
    /// # Arguments
    ///
    /// * `effect` - The write.
    fn span(&self, effect: &Effect) -> Option<(u64, u64)> {
        let mask = low(self.st.width);
        let tls = |a: u64| tls_slot(a).map_or(a, |off| self.st.tls_block.wrapping_add(off) & mask);
        let (addr, len) = match effect {
            Effect::Store { addr, ty, .. } => {
                let a = match addr {
                    Expr::Const(a) => tls(*a),
                    other => {
                        let Read::Value(a) = self.read(other) else {
                            return None;
                        };
                        a
                    }
                };
                (a, u64::from(ty.bits() / 8).max(1))
            }
            Effect::Rep { dst, len, .. } => {
                let (Read::Value(a), Read::Value(n)) = (self.read(dst), self.read(len)) else {
                    return None;
                };
                (a, n)
            }
            Effect::Asm => return None,
        };
        let rest = len.saturating_sub(1);
        (len <= from_usize(REGION_MAX) && rest <= mask - (addr & mask))
            .then_some((addr & mask, len))
    }

    /// Compares every lifted store and `rep` region with the emulator's
    /// memory, then looks for bytes the emulator changed that no lifted
    /// write covers.
    ///
    /// A write is compared byte by byte where no later write overwrote it.
    /// A store over bytes an earlier store wrote is set aside: the symbolic
    /// pass reads memory as the block found it, so a read-modify-write after
    /// a store reads the old bytes, and folding can hide that read (`[p] -
    /// [p]` is 0) from the check that sets such reads aside.
    ///
    /// # Arguments
    ///
    /// * `held` - The bytes the lifter's slots hold, compared already.
    /// * `out` - Where the counts and disagreements go.
    pub(super) fn stores(&self, held: &FxHashSet<u64>, out: &mut Verified) {
        let mask = low(self.st.width);
        let spans: Vec<Option<(u64, u64)>> = self.effects.iter().map(|e| self.span(e)).collect();
        let covers = |(a, n): (u64, u64), x: u64| (x.wrapping_sub(a) & mask) < n;
        for (k, effect) in self.effects.iter().enumerate() {
            let later = spans.get(k + 1..).unwrap_or(&[]);
            let Some((a, n)) = spans.get(k).copied().flatten() else {
                if !matches!(effect, Effect::Asm) {
                    out.count(Fact::Store, Read::Unreadable);
                }
                continue;
            };
            if later.iter().any(Option::is_none) {
                out.count(Fact::Store, Read::Unreadable);
                continue;
            }
            let live =
                |x: u64| !held.contains(&x) && !later.iter().flatten().any(|&s| covers(s, x));
            match effect {
                Effect::Store { addr, ty, value } => {
                    let rewrite = self.effects.iter().zip(&spans).take(k).any(|(e, s)| {
                        matches!(e, Effect::Store { .. })
                            && s.is_some_and(|s| {
                                (0..n).any(|i| covers(s, a.wrapping_add(i) & mask))
                            })
                    });
                    let float = matches!(ty, Ty::F32 | Ty::F64);
                    let stored = if float {
                        as_float(value)
                    } else {
                        value.clone()
                    };
                    let read = match (n > 8, rewrite) {
                        (true, _) => Read::Unreadable,
                        (false, true) => Read::Stale,
                        (false, false) => self.read(&stored),
                    };
                    let Some(v) = out.count(Fact::Store, read) else {
                        continue;
                    };
                    let width = float_bits(&stored, &self.st);
                    let float = float || width.is_some();
                    let lifted = convert_float(v, width, *ty) & low(ty.bits());
                    let emulated = word(n, |i| self.after(a.wrapping_add(i) & mask));
                    let differs = (0..n).any(|i| {
                        let x = a.wrapping_add(i) & mask;
                        live(x) && self.after(x) != lo8(lifted >> (8 * i))
                    });
                    if differs && !agree(emulated, lifted, ty.bits(), float) {
                        let expr = format!("*({addr:?}) = {value:?}");
                        self.disagree(
                            out,
                            Fact::Store,
                            format!("{a:#x}"),
                            (emulated, lifted, ty.bits()),
                            expr,
                        );
                    }
                }
                Effect::Rep { src, .. } => {
                    let Some(bytes) = self.region(src, n, out) else {
                        continue;
                    };
                    let bad = (0u64..)
                        .zip(&bytes)
                        .map(|(i, &b)| (a.wrapping_add(i) & mask, b))
                        .find(|&(x, b)| live(x) && self.after(x) != b);
                    if let Some((x, b)) = bad {
                        let expr = format!(
                            "byte {:#x} of the region at {a:#x}, {n} bytes",
                            x.wrapping_sub(a) & mask
                        );
                        self.disagree(
                            out,
                            Fact::Store,
                            format!("{x:#x}"),
                            (u64::from(self.after(x)), u64::from(b), 8),
                            expr,
                        );
                    }
                }
                Effect::Asm => {}
            }
        }
        if spans.iter().any(Option::is_none) {
            return;
        }
        let end_sp = self.emu.register(M::SP).unwrap_or(self.st.rsp);
        let frame = |x: u64| {
            [self.st.rsp, end_sp]
                .iter()
                .any(|sp| (x.wrapping_sub(*sp).wrapping_add(FRAME_SPAN) & mask) < 2 * FRAME_SPAN)
        };
        let mut missed: Vec<u64> = self
            .stored
            .iter()
            .copied()
            .filter(|&x| {
                !held.contains(&x)
                    && !frame(x)
                    && !spans.iter().flatten().any(|&s| covers(s, x))
                    && self.after(x) != self.st.byte(x)
            })
            .collect();
        missed.sort_unstable();
        if let Some(&first) = missed.first() {
            let expr = format!(
                "the emulator changed {} bytes no lifted store writes",
                missed.len()
            );
            let values = (
                u64::from(self.after(first)),
                u64::from(self.st.byte(first)),
                8,
            );
            self.disagree(out, Fact::Store, format!("{first:#x}"), values, expr);
        }
    }

    /// The bytes a lifted `rep` region holds after it, counted as one
    /// store.
    ///
    /// # Arguments
    ///
    /// * `src` - The copied region's lowest address, or the fill's element
    ///   value and width.
    /// * `n` - The region's length in bytes.
    /// * `out` - Where the count goes.
    ///
    /// # Returns
    ///
    /// The bytes, or `None` when the evaluator cannot read them or a copy
    /// reads memory the block wrote.
    fn region(
        &self,
        src: &Result<Expr, (Expr, u8)>,
        n: u64,
        out: &mut Verified,
    ) -> Option<Vec<u8>> {
        let mask = low(self.st.width);
        match src {
            Ok(from) => {
                let read = match self.read(from) {
                    Read::Value(s) if self.touches(&[(s & mask, n)]) => Read::Stale,
                    other => other,
                };
                let s = out.count(Fact::Store, read)? & mask;
                Some(
                    (0..n)
                        .map(|i| self.st.byte(s.wrapping_add(i) & mask))
                        .collect(),
                )
            }
            Err((value, bits)) => {
                let v = out.count(Fact::Store, self.read(value))?;
                let size = u64::from(*bits / 8).max(1);
                Some((0..n).map(|i| lo8(v >> (8 * (i % size)))).collect())
            }
        }
    }

    /// Compares the block's conditional branch: the emulator steps it, the
    /// lifted condition is evaluated under the starting state.
    ///
    /// # Arguments
    ///
    /// * `jcc` - The branch.
    /// * `cond` - The lifted condition it is taken under.
    /// * `out` - Where the counts and disagreements go.
    pub(super) fn step_branch(&mut self, jcc: Jcc, cond: &Cond, out: &mut Verified) {
        let target = jcc.target;
        self.emu.set_budget(1);
        self.emu.stop_at(Some(target));
        let taken = match self.emu.run(jcc.ip).stop {
            Stop::Stopped(at) if at == target => true,
            Stop::Budget => false,
            _ => {
                out.undecided += 1;
                return;
            }
        };
        let mut reads = Vec::new();
        let lifted = eval_cond(cond, &self.st, &mut reads, EVAL_DEPTH);
        let read = if self.touches(&reads) {
            Read::Stale
        } else {
            lifted.map_or(Read::Unreadable, |b| Read::Value(u64::from(b)))
        };
        let Some(lifted) = out.count(Fact::Branch, read) else {
            return;
        };
        if lifted != u64::from(taken) {
            let values = (u64::from(taken), lifted, 1);
            self.disagree(
                out,
                Fact::Branch,
                format!("{:#x}", jcc.ip),
                values,
                format!("{cond:?}"),
            );
        }
    }
}

/// [`verify`] over some functions on the calling thread.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - The functions and their blocks.
/// * `entries` - The functions to check.
/// * `seed` - The starting state's seed.
fn verify_some(program: &Program, analysis: &Analysis, entries: &[u64], seed: u64) -> Verified {
    let mut out = Verified::default();
    let Some(sweep) = Sweep::new(program, seed) else {
        return out;
    };
    let overlay = Overlay::default();
    for &entry in entries {
        let Some(f) = analysis.function(entry) else {
            continue;
        };
        out.functions += 1;
        let mut ctx = sweep.ctx(program, analysis, &overlay, f);
        for block in &f.blocks {
            out.blocks += 1;
            if let Err(reason) = sweep.check(&mut ctx, entry, block, &mut out) {
                *out.skipped.entry(reason).or_default() += 1;
            }
        }
    }
    out
}

/// Renders a verification as a report.
///
/// A `#` summary, a line per kind of fact with what was compared, the
/// reasons blocks were not compared, the instructions the emulator lacks
/// by how often they stopped it, then a row per disagreement, at most
/// [`LISTED_MAX`].
///
/// # Arguments
///
/// * `v` - What [`verify`] found.
#[must_use]
pub fn verify_tsv(v: &Verified) -> String {
    report(v, &Fact::ALL)
}

/// Renders a verification as a report with a line for each of `kinds`.
///
/// # Arguments
///
/// * `v` - What a verification found.
/// * `kinds` - The kinds of fact the instruction set's check compares, in
///   report order.
pub(super) fn report(v: &Verified, kinds: &[Fact]) -> String {
    let skipped: usize = v.skipped.values().sum();
    let mut out = format!(
        "# verified {} functions, {} blocks: {} checked against the emulator, {skipped} not checked, {} disagreements\n",
        v.functions,
        v.blocks,
        v.checked,
        v.mismatches.len()
    );
    for &fact in kinds {
        let t = v.facts.get(&fact).copied().unwrap_or_default();
        let _ = write!(
            out,
            "# {fact}: {} compared, {} not readable, {} reading memory the block wrote, {} disagree",
            t.compared,
            t.unreadable,
            t.store_loads,
            v.mismatches.iter().filter(|m| m.fact == fact).count()
        );
        if t.lane > 0 {
            let _ = write!(out, ", {} the lane known roughness", t.lane);
        }
        if fact == Fact::Branch {
            let _ = write!(out, ", {} the emulator could not decide", v.undecided);
        }
        out.push('\n');
    }
    for (reason, n) in &v.skipped {
        let _ = writeln!(out, "# not checked: {n} for {reason}");
    }
    let mut unmodeled: Vec<(&String, &usize)> = v.unmodeled.iter().collect();
    unmodeled.sort_by(|a, b| b.1.cmp(a.1).then(a.0.cmp(b.0)));
    for (what, n) in unmodeled.iter().take(UNMODELED_LISTED) {
        let _ = writeln!(out, "#   unmodeled: {n} {what}");
    }
    if unmodeled.len() > UNMODELED_LISTED {
        let _ = writeln!(
            out,
            "#   unmodeled: showing {UNMODELED_LISTED} of {} kinds",
            unmodeled.len()
        );
    }
    if v.mismatches.len() > LISTED_MAX {
        let _ = writeln!(
            out,
            "# showing {LISTED_MAX} of {} disagreements",
            v.mismatches.len()
        );
    }
    out.push_str("function\tblock\tfact\tplace\temulated\tlifted\tbits\texpression\n");
    for m in v.mismatches.iter().take(LISTED_MAX) {
        let _ = writeln!(
            out,
            "{:#x}\t{:#x}\t{}\t{}\t{:#x}\t{:#x}\t{}\t{}",
            m.function, m.block, m.fact, m.place, m.emulated, m.lifted, m.bits, m.expr
        );
    }
    out
}

#[cfg(test)]
#[expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]
mod tests {
    use super::{Effect, Fact, Sweep, Verified, st_register, verify, verify_tsv};
    use crate::analysis::decompile::expr::{Expr, Key, Op, UnOp};
    use crate::analysis::{Analysis, Overlay};
    use crate::isa::x86::Register;
    use crate::program::{Arch, Program, Section, Symbol, SymbolKind};

    /// Lists the kinds of the disagreements, in order.
    fn kinds(out: &Verified) -> Vec<Fact> {
        out.mismatches.iter().map(|m| m.fact).collect()
    }

    /// Builds a raw x86-64 image with `code` at 0x1000 and a zeroed data
    /// section at 0x2000.
    ///
    /// The data section's first cell holds the module's TLS index the way
    /// an unlinked image's `_tls_index` does: zero, the loader binding it
    /// at runtime.
    ///
    /// # Arguments
    ///
    /// * `code` - The bytes placed at `0x1000`; at most one page.
    fn tls_image(code: &[u8]) -> Program {
        let mut bytes = vec![0xcc; 0x1000];
        bytes.resize(0x2000, 0);
        bytes[..code.len()].copy_from_slice(code);
        Program::raw(
            bytes,
            Arch::X86_64,
            0,
            Some(0x1000),
            vec![
                Section::mapped(".text", 0x1000, 0, 0x1000, false, true),
                Section::mapped(".data", 0x2000, 0x1000, 0x1000, true, false),
            ],
        )
    }

    /// A lifting with a wrong stored value, or with its branch condition
    /// flipped, is flagged on every seed.
    ///
    /// Every register still agrees: the store and the branch are facts of
    /// their own, which a check of registers alone passed.
    #[test]
    fn a_wrong_store_or_a_flipped_branch_is_flagged() {
        let p = Program::raw_x64(&[
            0x89, 0x51, 0x08, // ASM: mov [rcx+8], edx
            0x83, 0xc2, 0x01, // ASM: add edx, 1
            0x83, 0xfa, 0x05, // ASM: cmp edx, 5
            0x7c, 0x03, // ASM: jl 0x100e
            0x31, 0xc0, // ASM: xor eax, eax
            0xc3, // ASM: ret
            0xb8, 0x01, 0x00, 0x00, 0x00, // ASM: mov eax, 1
            0xc3, // ASM: ret
        ]);
        let a = Analysis::compute(&p);
        let overlay = Overlay::default();
        let f = a.function(0x1000).expect("function");
        let block = f.blocks.iter().find(|b| b.start == 0x1000).expect("block");
        for seed in 1..=8 {
            let sweep = Sweep::new(&p, seed).expect("sweep");
            let mut ctx = sweep.ctx(&p, &a, &overlay, f);
            let mut out = Verified::default();
            let ran = sweep.run(&mut ctx, 0x1000, block, &mut out).expect("run");
            ran.compare(&mut out);
            assert_eq!(kinds(&out), [], "seed {seed}: {}", verify_tsv(&out));
            for fact in [Fact::Store, Fact::Branch] {
                let compared = out.facts.get(&fact).map(|t| t.compared);
                assert_eq!(compared, Some(1), "seed {seed}: {}", verify_tsv(&out));
            }

            let mut out = Verified::default();
            let mut ran = sweep.run(&mut ctx, 0x1000, block, &mut out).expect("run");
            for effect in &mut ran.effects {
                if let Effect::Store { value, .. } = effect {
                    *value = Expr::Un(UnOp::Not, Box::new(value.clone()));
                }
            }
            ran.compare(&mut out);
            assert_eq!(
                kinds(&out),
                [Fact::Store],
                "seed {seed}: {}",
                verify_tsv(&out)
            );

            let mut out = Verified::default();
            let mut ran = sweep.run(&mut ctx, 0x1000, block, &mut out).expect("run");
            if let Some((_, cond)) = &mut ran.branch {
                *cond = cond.invert();
            }
            ran.compare(&mut out);
            assert_eq!(
                kinds(&out),
                [Fact::Branch],
                "seed {seed}: {}",
                verify_tsv(&out)
            );
        }
    }

    /// The x87 stack a block leaves is compared, and a lifted sum the text
    /// gets backwards is flagged on every seed.
    ///
    /// `fadd` leaves its result in `st0`, so the block's end state, not a
    /// store, carries what the lift computed; flipping the lifted value's
    /// sign disagrees with the emulator's for every load the seeds plant.
    #[test]
    fn the_x87_stack_is_compared() {
        let p = Program::raw_x64(&[
            0xd9, 0x01, // ASM: fld dword [rcx]
            0xdc, 0x41, 0x08, // ASM: fadd qword [rcx+8]
            0xc3, // ASM: ret
        ]);
        let a = Analysis::compute(&p);
        let overlay = Overlay::default();
        let f = a.function(0x1000).expect("function");
        let block = f.blocks.iter().find(|b| b.start == 0x1000).expect("block");
        for seed in 1..=8 {
            let sweep = Sweep::new(&p, seed).expect("sweep");
            let mut ctx = sweep.ctx(&p, &a, &overlay, f);
            let mut out = Verified::default();
            sweep
                .run(&mut ctx, 0x1000, block, &mut out)
                .expect("run")
                .compare(&mut out);
            assert_eq!(kinds(&out), [], "seed {seed}: {}", verify_tsv(&out));
            assert_eq!(
                out.facts.get(&Fact::X87).map(|t| t.compared),
                Some(1),
                "seed {seed}: {}",
                verify_tsv(&out)
            );

            let mut out = Verified::default();
            let mut ran = sweep.run(&mut ctx, 0x1000, block, &mut out).expect("run");
            let key = Key::Reg(st_register(0));
            let v = ran.env.vals.get(&key).cloned().expect("st0 value");
            ran.env.vals.insert(key, Expr::Un(UnOp::Neg, Box::new(v)));
            ran.compare(&mut out);
            assert_eq!(
                kinds(&out),
                [Fact::X87],
                "seed {seed}: {}",
                verify_tsv(&out)
            );
        }
    }

    /// The xmm lanes a block leaves are compared, and a lifted value the
    /// text gets wrong is flagged on every seed.
    ///
    /// `movss`/`addss` leave their single in `xmm0`'s low lane and `movq`
    /// an integer in `xmm2`'s, so the block's end state, not a store,
    /// carries what the lift computed: the single compares as the single
    /// the machine's own `addss` rounding left, never as a double's bits
    /// read over it, and negating it or flipping the integer lane's low bit
    /// disagrees with the emulator for every load the seeds plant.
    #[test]
    fn the_xmm_registers_are_compared() {
        let p = Program::raw_x64(&[
            0xf3, 0x0f, 0x10, 0x01, // ASM: movss xmm0,[rcx]
            0xf3, 0x0f, 0x58, 0x41, 0x04, // ASM: addss xmm0,[rcx+4]
            0x66, 0x48, 0x0f, 0x6e, 0xd0, // ASM: movq xmm2,rax
            0xc3, // ASM: ret
        ]);
        let a = Analysis::compute(&p);
        let overlay = Overlay::default();
        let f = a.function(0x1000).expect("function");
        let block = f.blocks.iter().find(|b| b.start == 0x1000).expect("block");
        for seed in 1..=8 {
            let sweep = Sweep::new(&p, seed).expect("sweep");
            let mut ctx = sweep.ctx(&p, &a, &overlay, f);
            let mut out = Verified::default();
            sweep
                .run(&mut ctx, 0x1000, block, &mut out)
                .expect("run")
                .compare(&mut out);
            assert_eq!(kinds(&out), [], "seed {seed}: {}", verify_tsv(&out));
            assert_eq!(
                out.facts.get(&Fact::Xmm).map(|t| t.compared),
                Some(16),
                "seed {seed}: {}",
                verify_tsv(&out)
            );

            for &(reg, flip) in &[(Register::XMM0, false), (Register::XMM2, true)] {
                let mut out = Verified::default();
                let mut ran = sweep.run(&mut ctx, 0x1000, block, &mut out).expect("run");
                let key = Key::Reg(reg);
                let v = ran.env.vals.get(&key).cloned().expect("xmm value");
                let wrong = if flip {
                    Expr::Bin(Op::Xor, Box::new(v), Box::new(Expr::Const(1)))
                } else {
                    Expr::Un(UnOp::Neg, Box::new(v))
                };
                ran.env.vals.insert(key, wrong);
                ran.compare(&mut out);
                assert_eq!(
                    kinds(&out),
                    [Fact::Xmm],
                    "seed {seed}, {reg:?}: {}",
                    verify_tsv(&out)
                );
            }
        }
    }

    /// A `movd` lane is lifted as the 32 bits the machine writes, so it
    /// compares exactly wherever a seed puts bits above bit 31.
    ///
    /// `movd xmm0, ecx` writes the low 32 bits of the lane and zeroes the
    /// rest; the lift narrows `ecx` to those bits, so the whole-read
    /// known roughness for a 32-bit source no longer reaches
    /// the lane: every lane compares, the bucket the sweep counts apart
    /// stays empty, and no seed disagrees.
    #[test]
    fn a_movd_lane_is_lifted_as_the_32_bits_the_machine_writes() {
        let p = Program::raw_x64(&[
            0x66, 0x0f, 0x6e, 0xc1, // ASM: movd xmm0,ecx
            0xc3, // ASM: ret
        ]);
        let a = Analysis::compute(&p);
        let overlay = Overlay::default();
        let f = a.function(0x1000).expect("function");
        let block = f.blocks.iter().find(|b| b.start == 0x1000).expect("block");
        for seed in 1..=8 {
            let sweep = Sweep::new(&p, seed).expect("sweep");
            let mut ctx = sweep.ctx(&p, &a, &overlay, f);
            let mut out = Verified::default();
            sweep
                .run(&mut ctx, 0x1000, block, &mut out)
                .expect("run")
                .compare(&mut out);
            assert_eq!(kinds(&out), [], "seed {seed}: {}", verify_tsv(&out));
            let t = out.facts.get(&Fact::Xmm).copied().unwrap_or_default();
            assert_eq!(t.compared, 16, "seed {seed}: {}", verify_tsv(&out));
            assert_eq!(t.lane, 0, "seed {seed}: {}", verify_tsv(&out));
        }
    }

    /// The segment registers a block leaves are compared, and a lifted move
    /// of one the text gets wrong is flagged on every seed.
    ///
    /// `mov es, ecx` moves a selector and `mov eax, es` reads it back, so
    /// the block's end state carries both what the lift wrote and what it
    /// read back: the five registers nothing moved compare as the clear
    /// values both sides start from, and negating the lifted `es` disagrees
    /// with the emulator's for every seed the sweep plants.
    #[test]
    fn the_segment_registers_are_compared() {
        let p = Program::raw_x64(&[
            0x8e, 0xc1, // ASM: mov es,ecx
            0x8c, 0xc0, // ASM: mov eax,es
            0xc3, // ASM: ret
        ]);
        let a = Analysis::compute(&p);
        let overlay = Overlay::default();
        let f = a.function(0x1000).expect("function");
        let block = f.blocks.iter().find(|b| b.start == 0x1000).expect("block");
        for seed in 1..=8 {
            let sweep = Sweep::new(&p, seed).expect("sweep");
            let mut ctx = sweep.ctx(&p, &a, &overlay, f);
            let mut out = Verified::default();
            sweep
                .run(&mut ctx, 0x1000, block, &mut out)
                .expect("run")
                .compare(&mut out);
            assert_eq!(kinds(&out), [], "seed {seed}: {}", verify_tsv(&out));
            assert_eq!(
                out.facts.get(&Fact::Segment).map(|t| t.compared),
                Some(6),
                "seed {seed}: {}",
                verify_tsv(&out)
            );

            let mut out = Verified::default();
            let mut ran = sweep.run(&mut ctx, 0x1000, block, &mut out).expect("run");
            let key = Key::Reg(Register::ES);
            let v = ran.env.vals.get(&key).cloned().expect("es value");
            ran.env.vals.insert(key, Expr::Un(UnOp::Not, Box::new(v)));
            ran.compare(&mut out);
            assert_eq!(
                kinds(&out),
                [Fact::Segment],
                "seed {seed}: {}",
                verify_tsv(&out)
            );
        }
    }

    /// The TLS slots a block reads are compared through the address the
    /// entry state walks the thread's TLS array to, and a lifted value the
    /// text gets wrong is flagged on every seed.
    ///
    /// `TR` walks `gs:[0x58]` to the TLS block, reads slot 0x10 into `rax`
    /// and `rdx` and stores both reads; the lift folds each read to the
    /// pseudo-global `TLS_BASE + 0x10` (the constructor `Tls::Tls` before
    /// it registered its singleton there), which the evaluator reads at
    /// the walked address so both sides see the same bytes: the two reads
    /// compare equal and the stores of them compare, while the register
    /// holding the block itself still names the segment selector and
    /// counts as unreadable. Flipping a read's low bit disagrees on its
    /// register, and flipping the stored values disagrees on both stores.
    #[test]
    fn tls_slot_reads_compare_through_the_walked_block() {
        let mut p = tls_image(&[
            0x48, 0x8b, 0xd9, // ASM: mov rbx,rcx
            0x65, 0x48, 0x8b, 0x04, 0x25, 0x58, 0x00, 0x00, 0x00, // ASM: mov rax,gs:[0x58]
            0x8b, 0x0d, 0xee, 0x0f, 0x00,
            0x00, // ASM: mov ecx,[rip+0xfee] -> 0x2000 (the index)
            0x48, 0x8b, 0x04, 0xc8, // ASM: mov rax,[rax+rcx*8]
            0x48, 0x89, 0x58, 0x10, // ASM: mov [rax+0x10],rbx
            0xc3, // ASM: ret
            0x65, 0x48, 0x8b, 0x04, 0x25, 0x58, 0x00, 0x00, 0x00, // ASM: mov rax,gs:[0x58]
            0x8b, 0x0d, 0xd6, 0x0f, 0x00, 0x00, // ASM: mov ecx,[rip+0xfd6] -> 0x2000
            0x4c, 0x8b, 0x04, 0xc8, // ASM: mov r8,[rax+rcx*8]
            0x49, 0x8b, 0x40, 0x10, // ASM: mov rax,[r8+0x10]
            0x49, 0x8b, 0x50, 0x10, // ASM: mov rdx,[r8+0x10]
            0x48, 0x89, 0x07, // ASM: mov [rdi],rax
            0x48, 0x89, 0x57, 0x08, // ASM: mov [rdi+8],rdx
            0xc3, // ASM: ret
        ]);
        p.symbols.push(Symbol {
            name: "Tls::Tls".to_owned(),
            addr: 0x1000,
            kind: SymbolKind::Export,
        });
        p.symbols.push(Symbol {
            name: "Tls::Read".to_owned(),
            addr: 0x101b,
            kind: SymbolKind::Export,
        });
        let a = Analysis::compute(&p);
        let overlay = Overlay::default();
        let read = a.function(0x101b).expect("reader");
        let block = read
            .blocks
            .iter()
            .find(|b| b.start == 0x101b)
            .expect("block");
        for seed in 1..=8 {
            let sweep = Sweep::new(&p, seed).expect("sweep");
            let mut ctx = sweep.ctx(&p, &a, &overlay, read);
            let mut out = Verified::default();
            sweep
                .run(&mut ctx, 0x1017, block, &mut out)
                .expect("run")
                .compare(&mut out);
            assert_eq!(kinds(&out), [], "seed {seed}: {}", verify_tsv(&out));
            let reg = out.facts.get(&Fact::Register).copied().unwrap_or_default();
            assert_eq!(reg.unreadable, 1, "seed {seed}: {}", verify_tsv(&out));
            let store = out.facts.get(&Fact::Store).copied().unwrap_or_default();
            assert_eq!(store.compared, 2, "seed {seed}: {}", verify_tsv(&out));
            assert_eq!(store.unreadable, 0, "seed {seed}: {}", verify_tsv(&out));

            let mut out = Verified::default();
            let mut ran = sweep.run(&mut ctx, 0x101b, block, &mut out).expect("run");
            let key = Key::Reg(Register::RAX);
            let v = ran.env.vals.get(&key).cloned().expect("the slot's value");
            ran.env.vals.insert(
                key,
                Expr::Bin(Op::Xor, Box::new(v), Box::new(Expr::Const(1))),
            );
            ran.compare(&mut out);
            assert_eq!(
                kinds(&out),
                [Fact::Register],
                "seed {seed}: {}",
                verify_tsv(&out)
            );

            let mut out = Verified::default();
            let mut ran = sweep.run(&mut ctx, 0x101b, block, &mut out).expect("run");
            for effect in &mut ran.effects {
                if let Effect::Store { value, .. } = effect {
                    *value = Expr::Un(UnOp::Not, Box::new(value.clone()));
                }
            }
            ran.compare(&mut out);
            assert_eq!(
                kinds(&out),
                [Fact::Store, Fact::Store],
                "seed {seed}: {}",
                verify_tsv(&out)
            );
        }
    }

    /// A store into a TLS slot compares at the walked block's address, and
    /// a lifted value the text gets wrong is flagged on every seed.
    ///
    /// `Tls::Tls` stores `this` at TLS offset 0x10 through the walked
    /// block; the lift folds the store's address to the pseudo-global
    /// `TLS_BASE + 0x10`, which the evaluator writes and reads at the
    /// address the entry state walked to, so the machine's bytes there
    /// compare with the stored register, and negating the lifted value
    /// disagrees for every seed.
    #[test]
    fn a_tls_slot_store_compares_at_the_walked_block() {
        let mut p = tls_image(&[
            0x48, 0x8b, 0xd9, // ASM: mov rbx,rcx
            0x65, 0x48, 0x8b, 0x04, 0x25, 0x58, 0x00, 0x00, 0x00, // ASM: mov rax,gs:[0x58]
            0x8b, 0x0d, 0xee, 0x0f, 0x00,
            0x00, // ASM: mov ecx,[rip+0xfee] -> 0x2000 (the index)
            0x48, 0x8b, 0x04, 0xc8, // ASM: mov rax,[rax+rcx*8]
            0x48, 0x89, 0x58, 0x10, // ASM: mov [rax+0x10],rbx
            0xc3, // ASM: ret
        ]);
        p.symbols.push(Symbol {
            name: "Tls::Tls".to_owned(),
            addr: 0x1000,
            kind: SymbolKind::Export,
        });
        let a = Analysis::compute(&p);
        let overlay = Overlay::default();
        let f = a.function(0x1000).expect("constructor");
        let block = f.blocks.iter().find(|b| b.start == 0x1000).expect("block");
        for seed in 1..=8 {
            let sweep = Sweep::new(&p, seed).expect("sweep");
            let mut ctx = sweep.ctx(&p, &a, &overlay, f);
            let mut out = Verified::default();
            sweep
                .run(&mut ctx, 0x1000, block, &mut out)
                .expect("run")
                .compare(&mut out);
            assert_eq!(kinds(&out), [], "seed {seed}: {}", verify_tsv(&out));
            let store = out.facts.get(&Fact::Store).copied().unwrap_or_default();
            assert_eq!(store.compared, 1, "seed {seed}: {}", verify_tsv(&out));
            assert_eq!(store.unreadable, 0, "seed {seed}: {}", verify_tsv(&out));

            let mut out = Verified::default();
            let mut ran = sweep.run(&mut ctx, 0x1000, block, &mut out).expect("run");
            for effect in &mut ran.effects {
                if let Effect::Store { value, .. } = effect {
                    *value = Expr::Un(UnOp::Not, Box::new(value.clone()));
                }
            }
            ran.compare(&mut out);
            assert_eq!(
                kinds(&out),
                [Fact::Store],
                "seed {seed}: {}",
                verify_tsv(&out)
            );
        }
    }

    /// An aligned entry block's stores are compared once the seed takes
    /// the alignment's slack as zero.
    ///
    /// `push rbp; mov rbp, rsp; and rsp, -16` leaves the stack pointer one
    /// push below the alignment rounds to, a slack of eight the lifter
    /// tracks as zero; seeding the checked run's stack pointer back by it
    /// makes the machine's aligned frame the one the lifter tracks, so the
    /// saved `rbp` the push wrote and the stores through `rsp` and through
    /// the saved `rbp` compare, and a lifted slot value the text gets wrong
    /// is flagged on every seed.
    #[test]
    fn an_aligned_entry_block_compares_its_stores() {
        let p = Program::raw_x64(&[
            0x55, // ASM: push rbp
            0x48, 0x89, 0xe5, // ASM: mov rbp,rsp
            0x48, 0x83, 0xe4, 0xf0, // ASM: and rsp,-16
            0x89, 0x44, 0x24, 0x08, // ASM: mov [rsp+8],eax
            0x89, 0x7d, 0xf8, // ASM: mov [rbp-8],edi
            0xc3, // ASM: ret
        ]);
        let a = Analysis::compute(&p);
        let overlay = Overlay::default();
        let f = a.function(0x1000).expect("function");
        let block = f.blocks.iter().find(|b| b.start == 0x1000).expect("block");
        for seed in 1..=8 {
            let sweep = Sweep::new(&p, seed).expect("sweep");
            let mut ctx = sweep.ctx(&p, &a, &overlay, f);
            let mut out = Verified::default();
            sweep
                .run(&mut ctx, 0x1000, block, &mut out)
                .expect("run")
                .compare(&mut out);
            assert_eq!(kinds(&out), [], "seed {seed}: {}", verify_tsv(&out));
            assert_eq!(
                out.facts.get(&Fact::Slot).map(|t| t.compared),
                Some(3),
                "seed {seed}: {}",
                verify_tsv(&out)
            );

            let mut out = Verified::default();
            let mut ran = sweep.run(&mut ctx, 0x1000, block, &mut out).expect("run");
            for (k, v) in &mut ran.env.vals {
                if matches!(k, Key::Slot(_)) {
                    *v = Expr::Un(UnOp::Not, Box::new(v.clone()));
                }
            }
            ran.compare(&mut out);
            assert_eq!(
                kinds(&out),
                [Fact::Slot, Fact::Slot, Fact::Slot],
                "seed {seed}: {}",
                verify_tsv(&out)
            );
        }
    }

    /// A block whose alignment the seed cannot zero stays counted as
    /// skipped, not run half-checked.
    ///
    /// `mov rsp, rsi` leaves the lifter no frame offsets to track, so the
    /// `and rsp, -16` after it rounds a pointer the lift cannot state: no
    /// fact of that frame can be compared, and the block is counted under
    /// the alignment reason.
    #[test]
    fn an_untracked_frame_alignment_stays_counted() {
        let p = Program::raw_x64(&[
            0x48, 0x89, 0xf4, // ASM: mov rsp,rsi
            0x48, 0x83, 0xe4, 0xf0, // ASM: and rsp,-16
            0xc3, // ASM: ret
        ]);
        let a = Analysis::compute(&p);
        for seed in 1..=4 {
            let v = verify(&p, &a, &[0x1000], seed);
            assert_eq!(v.checked, 0, "seed {seed}: {}", verify_tsv(&v));
            assert_eq!(
                v.skipped
                    .get("a frame alignment whose slack the seed cannot zero"),
                Some(&1),
                "seed {seed}: {}",
                verify_tsv(&v)
            );
        }
    }

    /// A signed branch on a one-bit shift's overflow compares, once the
    /// emulator computes the flag the SDM defines.
    ///
    /// The lift reads `shl eax, 1` as the `add eax, eax` it is for the
    /// flags, so `jl` after it is the sign of the doubled value; the
    /// machine's `jl` is the sign flag against the overflow, whose SDM
    /// value for a count of one is the result's sign xored with the carry
    /// — the same bit. The branch used to come back undecided (the
    /// emulator stopped on the jump); now every seed compares it, and a
    /// lifted condition flipped is flagged on every seed.
    #[test]
    fn shl_by_one_then_jl_reads_the_overflow() {
        let p = Program::raw_x64(&[
            0x8b, 0x01, // ASM: mov eax,[rcx]
            0xd1, 0xe0, // ASM: shl eax,1
            0x7c, 0x05, // ASM: jl 0x100b
            0xb8, 0x00, 0x00, 0x00, 0x00, // ASM: mov eax,0
            0xc3, // ASM: ret
            0xb8, 0x01, 0x00, 0x00, 0x00, // ASM: .taken: mov eax,1
            0xc3, // ASM: ret
        ]);
        let a = Analysis::compute(&p);
        let overlay = Overlay::default();
        let f = a.function(0x1000).expect("function");
        let block = f.blocks.iter().find(|b| b.start == 0x1000).expect("block");
        for seed in 1..=8 {
            let sweep = Sweep::new(&p, seed).expect("sweep");
            let mut ctx = sweep.ctx(&p, &a, &overlay, f);
            let mut out = Verified::default();
            sweep
                .run(&mut ctx, 0x1000, block, &mut out)
                .expect("run")
                .compare(&mut out);
            assert_eq!(kinds(&out), [], "seed {seed}: {}", verify_tsv(&out));
            assert_eq!(out.undecided, 0, "seed {seed}: {}", verify_tsv(&out));
            assert_eq!(
                out.facts.get(&Fact::Branch).map(|t| t.compared),
                Some(1),
                "seed {seed}: {}",
                verify_tsv(&out)
            );

            let mut out = Verified::default();
            let mut ran = sweep.run(&mut ctx, 0x1000, block, &mut out).expect("run");
            if let Some((_, cond)) = &mut ran.branch {
                *cond = cond.invert();
            }
            ran.compare(&mut out);
            assert_eq!(
                kinds(&out),
                [Fact::Branch],
                "seed {seed}: {}",
                verify_tsv(&out)
            );
        }
    }

    /// A float binary operation evaluates, so the store of its result is
    /// compared, not counted as unreadable, and a lifted one with the
    /// wrong sign is flagged on every seed.
    #[test]
    fn a_float_binary_operation_is_compared() {
        let p = Program::raw_x64(&[
            0xf2, 0x0f, 0x10, 0x01, // ASM: movsd xmm0,[rcx]
            0xf2, 0x0f, 0x58, 0x41, 0x08, // ASM: addsd xmm0,[rcx+8]
            0xf2, 0x0f, 0x11, 0x41, 0x10, // ASM: movsd [rcx+16],xmm0
            0xc3, // ASM: ret
        ]);
        let a = Analysis::compute(&p);
        let overlay = Overlay::default();
        let f = a.function(0x1000).expect("function");
        let block = f.blocks.iter().find(|b| b.start == 0x1000).expect("block");
        for seed in 1..=8 {
            let sweep = Sweep::new(&p, seed).expect("sweep");
            let mut ctx = sweep.ctx(&p, &a, &overlay, f);
            let mut out = Verified::default();
            sweep
                .run(&mut ctx, 0x1000, block, &mut out)
                .expect("run")
                .compare(&mut out);
            assert_eq!(kinds(&out), [], "seed {seed}: {}", verify_tsv(&out));
            let store = out.facts.get(&Fact::Store).copied().unwrap_or_default();
            assert_eq!(store.compared, 1, "seed {seed}: {}", verify_tsv(&out));
            assert_eq!(store.unreadable, 0, "seed {seed}: {}", verify_tsv(&out));

            let mut out = Verified::default();
            let mut ran = sweep.run(&mut ctx, 0x1000, block, &mut out).expect("run");
            for effect in &mut ran.effects {
                if let Effect::Store { value, .. } = effect {
                    *value = Expr::Un(UnOp::Neg, Box::new(value.clone()));
                }
            }
            ran.compare(&mut out);
            assert_eq!(
                kinds(&out),
                [Fact::Store],
                "seed {seed}: {}",
                verify_tsv(&out)
            );
        }
    }

    /// A single's operation rounds at the operation, not at the store.
    ///
    /// `1 - 2^-25` is halfway between the two singles around it and rounds
    /// to `1` itself, so a compare against `1` and a store of the
    /// difference agree with the emulator only when the subtraction
    /// computes in a single: computed in a double it stays
    /// `0.99999997`, which compares below `1` and stores as the low half
    /// of a double's bits, as a chain of `subss` and `divss` in the corpus
    /// once did.
    #[test]
    fn a_single_rounds_at_the_operation() {
        let p = Program::raw_x64(&[
            0xf3, 0x0f, 0x10, 0x0d, 0x28, 0x00, 0x00, 0x00, // ASM: movss xmm1,[rip+0x28]
            0xf3, 0x0f, 0x10, 0x05, 0x24, 0x00, 0x00, 0x00, // ASM: movss xmm0,[rip+0x24]
            0xf3, 0x0f, 0x5c, 0xc1, // ASM: subss xmm0,xmm1
            0x0f, 0x2e, 0x05, 0x1d, 0x00, 0x00, 0x00, // ASM: ucomiss xmm0,[rip+0x1d]
            0x0f, 0x93, 0xc0, // ASM: setae al
            0x24, 0x01, // ASM: and al,1
            0xf3, 0x0f, 0x11, 0x84, 0x24, 0x90, 0x00, 0x00,
            0x00, // ASM: movss [rsp+0x90],xmm0
            0x88, 0x44, 0x24, 0x33, // ASM: mov [rsp+0x33],al
            0xc3, // ASM: ret
            0xcc, 0xcc, 0x00, 0x00, 0x00, 0x33, 0x00, 0x00, 0x80, 0x3f, 0x00, 0x00, 0x80, 0x3f,
        ]);
        let a = Analysis::compute(&p);
        let overlay = Overlay::default();
        let f = a.function(0x1000).expect("function");
        let block = f.blocks.iter().find(|b| b.start == 0x1000).expect("block");
        for seed in 1..=8 {
            let sweep = Sweep::new(&p, seed).expect("sweep");
            let mut ctx = sweep.ctx(&p, &a, &overlay, f);
            let mut out = Verified::default();
            sweep
                .run(&mut ctx, 0x1000, block, &mut out)
                .expect("run")
                .compare(&mut out);
            assert_eq!(kinds(&out), [], "seed {seed}: {}", verify_tsv(&out));
            let slot = out.facts.get(&Fact::Slot).copied().unwrap_or_default();
            assert_eq!(slot.compared, 2, "seed {seed}: {}", verify_tsv(&out));
            assert_eq!(slot.unreadable, 0, "seed {seed}: {}", verify_tsv(&out));
        }
    }

    /// In 32-bit code a left shift's overflow is gone before a right shift
    /// reads it, in the text and in the check.
    ///
    /// `shrd eax, edx, 16` after `shl eax, 8` lifts as
    /// `((x << 8) >> 16) | (edx << 16)` over `uint32_t` variables. Folded at
    /// 64 bits, the top byte of `x` came back down into bits 16 to 23, and
    /// most seeds reported the right lifting as a disagreement, as a byte
    /// swap in a real game client did.
    #[test]
    fn a_32_bit_shift_chain_is_evaluated_at_32_bits() {
        let mut p = Program::raw_x64(&[
            0x8b, 0xc1, // ASM: mov eax, ecx
            0xc1, 0xe0, 0x08, // ASM: shl eax, 8
            0x0f, 0xac, 0xd0, 0x10, // ASM: shrd eax, edx, 16
            0xc3, // ASM: ret
        ]);
        p.arch = Arch::X86;
        p.is_64 = false;
        let a = Analysis::compute(&p);
        for seed in 1..=16 {
            let v = verify(&p, &a, &[0x1000], seed);
            assert_eq!(v.checked, 1, "seed {seed}: {}", verify_tsv(&v));
            assert!(v.compared > 0, "seed {seed}: {}", verify_tsv(&v));
            assert_eq!(kinds(&v), [], "seed {seed}: {}", verify_tsv(&v));
        }
    }
}
