//! Instruction semantics: executes one basic block over a symbolic environment.
//!
//! Pseudo-C statements are emitted only when a value must exist in the text
//! (a store, a call, a return, or a variable about to be clobbered).
//!
//! Invariant: every `Var` in the environment means "the current
//! value of that variable in the emitted text". Before any emitted line
//! changes a variable, every environment entry that reads it is written out
//! first ([`Exec::materialize`]), so no expression ever refers to a stale value.

/// Records a pseudo-C line only in the emission pass: the dataflow pass
/// discards lines, so it must not pay for rendering them. Defined before
/// the child modules, which see a `macro_rules!` only after it.
macro_rules! emit_line {
    ($ex:expr, $line:expr) => {
        if $ex.emit {
            $ex.lines.push($line);
        }
    };
}

mod calls;
mod conv;
mod effects;
mod float;
mod pack;
mod record;
mod state;
mod stated;
mod step;

pub(crate) use conv::*;
pub(in crate::analysis::decompile) use effects::*;
pub(in crate::analysis::decompile) use pack::*;
pub(in crate::analysis::decompile) use record::*;
pub(in crate::analysis::decompile) use state::try_level_store;
pub(in crate::analysis::decompile) use stated::*;

use std::collections::{BTreeMap, BTreeSet};

use crate::isa::x86::{
    Code, ConditionCode, FlowControl, Formatter, Instruction, InstructionInfoFactory, MemorySize,
    Mnemonic, NasmFormatter, OpAccess, OpKind, Register, RflagsBits, as_xmm, sized_register,
    st_depth, st_register,
};

use super::expr::{
    Cc, Cond, Expr, Flags, Key, Names, Op, Ty, UnOp, bare, either_width, fold, known_bits, mask,
    mask_bits, sign_extend, table_index, unary, without_addend,
};
use super::{Ctx, callee_shape, literal_at};
use crate::analysis::name_of;
use crate::analysis::returns::{RET_LANE_DEPTH, lane_before, last_rax_write};
use crate::fxmap::FxHashMap;
use crate::program::{BinaryFormat, Program, SymbolKind};

/// Expressions bigger than this are written to their variable immediately.
const MAX_EXPR: usize = 16;

/// Expressions bigger than this that the block reads twice or more before
/// rewriting their register are written to it once instead of being
/// inlined at every use.
const INLINE_MAX: usize = 6;
/// Largest value kept whole when nothing is written out
/// ([`Ctx::symbolic_only`]); a bigger one is held as an unknown, since a
/// value that reuses others would otherwise grow without bound.
const SYMBOLIC_MAX: usize = 256;

/// Outgoing stack-argument window materialized before a call (bytes above
/// the shadow space): 8 arguments.
const STACK_ARG_WINDOW: i64 = 0x40;

/// The widest slot access in bytes: an access this far below a slot may
/// reach into it.
pub(super) const SLOT_BYTES_MAX: i64 = 16;

/// The first id of the temporaries the dataflow pass numbers within one
/// run of a block: far above the ones a function's join or emission takes
/// from its own count, and meaningless outside that run.
pub(super) const BLOCK_TMP: u32 = 1 << 30;

/// Which pass runs a block: the dataflow computes state only, the
/// emission pass records text, declarations and temporaries as well.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum Pass {
    /// Compute the state after the block and discard the lines.
    Dataflow,
    /// Record the lines, declarations and temporaries.
    Emission,
}

/// Symbolic machine state at one program point.
#[derive(Debug, Clone, PartialEq)]
pub(super) struct Env {
    /// Known values by text variable; an absent key means "its own text value".
    pub vals: BTreeMap<Key, Expr>,
    /// Width in bits of the last store to each slot whose value is known.
    pub slot_bits: BTreeMap<i64, u8>,
    /// rsp minus its value at function entry; `None` once it is unknown.
    pub sp: Option<i64>,
    /// rax held this constant at the last call (`__chkstk` keeps it): the
    /// `sub rsp, rax` that follows adjusts the frame by it.
    pub chkstk: Option<u64>,
    /// Flags left for a successor that reads them before setting any
    /// (`cmp; jae A; ... A: jne B` reuses one compare); Unknown otherwise.
    pub flags: Flags,
    /// The direction flag: clear at entry and after a call (the ABI's
    /// promise both ways), set by `std`, and `None` where paths disagree or
    /// an instruction without a model (`popf`) wrote it. String instructions
    /// step backward while it is set.
    pub df: Option<bool>,
    /// Class of the object a text variable points at, from the declared
    /// return type of the call assigned to it; valid until it is reassigned.
    pub classes: BTreeMap<Key, String>,
    /// The text variable `rax` holds a value some statement assigned (a
    /// call's result or a write), so `return rax;` means something even
    /// when no instruction of the function computes the result itself.
    pub result_in_rax: bool,
    /// Type of the object a stack slot holds, from the declared parameter or
    /// by-value return its address was passed for (`Core::Ptr<T>` for a
    /// local smart pointer).
    pub slot_types: BTreeMap<i64, String>,
    /// Text variables holding the thread's TLS array (`gs:[0x58]`).
    pub tls_arrays: BTreeSet<Key>,
    /// Text variables holding this module's TLS block.
    pub tls_blocks: BTreeSet<Key>,
    /// Width in bits of the value a text variable holds when it is narrower
    /// than the register: a call's result (the callee's declared return
    /// type, or the widest read any of its callers makes) or a value that
    /// provably fits a byte or word ([`known_bits`]: a truth value, a masked
    /// value, a byte load, a small constant); a copy carries it along, and
    /// reads of that lane need no mask.
    pub narrow: FxHashMap<Key, u8>,
    /// Registers holding nothing on every path here: `ecx` when never set
    /// since the entry of a function it carries no argument into, or
    /// clobbered by a call since it was. A push of it only makes room on
    /// the stack; no other register is pushed for that, and `eax` and `edx`
    /// carry a call's result out.
    pub unset: BTreeSet<Key>,
    /// The operands of the last x87 compare whose outcome sits in the
    /// status word (`fcom`, `fcompp`, `ficomp`), until `fnstsw ax; sahf`
    /// moves it into the flags; `None` where paths disagree.
    pub fpu_cmp: Option<(Expr, Expr)>,
    /// Registers and stack slots some instruction wrote since the last
    /// call, on every path here; empty at the entry, where a register holds
    /// only what the caller left. A call whose callee states no arity passes
    /// these and nothing a register merely inherited. A register whose dead
    /// value was dropped unwritten ([`Exec::forget_dead`]) leaves it.
    pub fresh: BTreeSet<Key>,
    /// Registers some instruction wrote on some path here since the entry:
    /// a callee-saved register outside it still holds the caller's value,
    /// and a push of it is a save, no argument.
    pub touched: BTreeSet<Key>,
    /// Volatile registers a call clobbered on some path here, and registers
    /// whose dead pending value was dropped unwritten ([`Exec::forget_dead`]),
    /// that nothing wrote since: their text variables name no value the
    /// machine holds.
    pub clobbered: BTreeSet<Key>,
}

impl Env {
    /// Returns the state at function entry: nothing known, rsp at offset 0.
    pub(super) fn entry() -> Env {
        Env {
            vals: BTreeMap::new(),
            slot_bits: BTreeMap::new(),
            sp: Some(0),
            chkstk: None,
            flags: Flags::Unknown,
            df: Some(false),
            classes: BTreeMap::new(),
            result_in_rax: false,
            slot_types: BTreeMap::new(),
            tls_arrays: BTreeSet::new(),
            tls_blocks: BTreeSet::new(),
            narrow: FxHashMap::default(),
            unset: BTreeSet::new(),
            fpu_cmp: None,
            fresh: BTreeSet::new(),
            touched: BTreeSet::new(),
            clobbered: BTreeSet::new(),
        }
    }

    /// Returns the entry state with each detected parameter register holding
    /// its argument (`a1`, `a2`, ...), so copies of a parameter stay symbolic
    /// when the register itself is clobbered by a call.
    ///
    /// The registers a compiler pushes only to reserve a word are unset
    /// ([`Exec::makes_room`]): `ecx` in MSVC's 32-bit prologues, and `rax`,
    /// which no 64-bit convention passes an argument in, in clang's `push
    /// rax` for eight bytes of frame.
    ///
    /// # Arguments
    ///
    /// * `conv` - The calling convention (argument register order).
    /// * `params` - The parameter registers the function reads.
    pub(super) fn entry_with_params(conv: &Conv, params: &[Register]) -> Env {
        let mut env = Env::entry();
        env.unset = conv
            .volatile
            .iter()
            .filter(|r| matches!(**r, Register::ECX | Register::RAX) && !params.contains(r))
            .map(|r| Key::Reg(*r))
            .collect();
        for r in params {
            if let Some(i) = conv.param_pos(*r, params)
                && let Ok(i) = u8::try_from(i)
            {
                env.vals.insert(Key::Reg(*r), Expr::Var(Key::Param(i)));
            }
        }
        env
    }

    /// Returns the state with nothing known, rsp included.
    pub(super) fn unknown() -> Env {
        Env {
            vals: BTreeMap::new(),
            slot_bits: BTreeMap::new(),
            sp: None,
            chkstk: None,
            flags: Flags::Unknown,
            df: None,
            classes: BTreeMap::new(),
            result_in_rax: false,
            slot_types: BTreeMap::new(),
            tls_arrays: BTreeSet::new(),
            tls_blocks: BTreeSet::new(),
            narrow: FxHashMap::default(),
            unset: BTreeSet::new(),
            fpu_cmp: None,
            fresh: BTreeSet::new(),
            touched: BTreeSet::new(),
            clobbered: BTreeSet::new(),
        }
    }

    /// Meets two states at a join: only facts both sides agree on survive.
    ///
    /// PERF: the state is narrowed in place, so a join of many edges clones
    /// the first edge's state once rather than once per edge.
    ///
    /// # Arguments
    ///
    /// * `other` - The state arriving over the other edge.
    pub(super) fn meet(mut self, other: &Env) -> Env {
        self.slot_bits
            .retain(|k, v| other.slot_bits.get(k) == Some(v));
        self.vals.retain(|k, v| {
            other.vals.get(k) == Some(v)
                && match k {
                    Key::Slot(o) => self.slot_bits.contains_key(o),
                    Key::Reg(_) | Key::Global(..) | Key::Tmp(_) | Key::Param(_) | Key::A64(_) => {
                        true
                    }
                }
        });
        self.classes.retain(|k, v| other.classes.get(k) == Some(v));
        self.slot_types
            .retain(|k, v| other.slot_types.get(k) == Some(v));
        self.tls_arrays.retain(|k| other.tls_arrays.contains(k));
        self.tls_blocks.retain(|k| other.tls_blocks.contains(k));
        self.narrow.retain(|k, v| match (k, other.narrow.get(k)) {
            (Key::A64(_), Some(w)) => {
                *v = (*v).max(*w);
                true
            }
            (_, w) => w == Some(v),
        });
        self.unset.retain(|k| other.unset.contains(k));
        self.fresh.retain(|k| other.fresh.contains(k));
        self.touched.extend(other.touched.iter().copied());
        self.clobbered.extend(other.clobbered.iter().copied());
        self.result_in_rax &= other.result_in_rax;
        if self.sp != other.sp {
            self.sp = None;
        }
        if self.chkstk != other.chkstk {
            self.chkstk = None;
        }
        if self.flags != other.flags {
            self.flags = Flags::Unknown;
        }
        if self.df != other.df {
            self.df = None;
        }
        if self.fpu_cmp != other.fpu_cmp {
            self.fpu_cmp = None;
        }
        self
    }

    /// Returns the value of a variable, its own text value when unknown.
    ///
    /// # Arguments
    ///
    /// * `k` - The variable.
    pub(super) fn get(&self, k: Key) -> Expr {
        self.vals.get(&k).cloned().unwrap_or(Expr::Var(k))
    }

    /// Records a value; a variable equal to its own text value is simply forgotten.
    ///
    /// A plain copy of a narrow value keeps its width, a value that provably
    /// fits a byte or word is that narrow, and any other value is as wide as
    /// the register. A register or slot written is fresh until the next call
    /// ([`Env::fresh`]).
    ///
    /// # Arguments
    ///
    /// * `k` - The variable.
    /// * `v` - Its new symbolic value.
    fn set(&mut self, k: Key, v: Expr) {
        self.unset.remove(&k);
        self.clobbered.remove(&k);
        if matches!(k, Key::Reg(_) | Key::A64(_)) {
            self.touched.insert(k);
        }
        if matches!(k, Key::Reg(_) | Key::Slot(_) | Key::A64(_)) {
            self.fresh.insert(k);
        }
        let bits = match &v {
            Expr::Var(src) if self.vals.contains_key(src) => None,
            Expr::Var(src) => self.narrow.get(src).copied(),
            _ => match known_bits(&v) {
                b if b <= 0xff => Some(8),
                b if b <= 0xffff => Some(16),
                _ => None,
            },
        };
        match bits {
            Some(b) => {
                self.narrow.insert(k, b);
            }
            None => {
                self.narrow.remove(&k);
            }
        }
        let array = is_tls_array_expr(&v, &self.tls_arrays);
        let block = is_tls_block_expr(&v, &self.tls_arrays, &self.tls_blocks);
        if array {
            self.tls_arrays.insert(k);
        } else {
            self.tls_arrays.remove(&k);
        }
        if block {
            self.tls_blocks.insert(k);
        } else {
            self.tls_blocks.remove(&k);
        }
        if v == Expr::Var(k) {
            self.vals.remove(&k);
        } else {
            self.vals.insert(k, v);
        }
    }
}

/// Whether `e` is the thread's TLS array: the `gs:[0x58]` read, or a variable
/// already known to hold it.
///
/// # Arguments
///
/// * `e` - The value.
/// * `arrays` - Variables already known to hold the array.
fn is_tls_array_expr(e: &Expr, arrays: &BTreeSet<Key>) -> bool {
    match e {
        Expr::Var(k) => arrays.contains(k),
        Expr::Deref(a, _) => matches!(
            &**a,
            Expr::Bin(Op::Add, seg, off)
                if matches!(**seg, Expr::Var(Key::Reg(Register::GS)))
                    && matches!(**off, Expr::Const(0x58))
        ),
        _ => false,
    }
}

/// Whether `e` is this module's TLS block: the TLS array indexed by anything,
/// or a variable already known to hold it.
///
/// # Arguments
///
/// * `e` - The value.
/// * `arrays` - Variables already known to hold the TLS array.
/// * `blocks` - Variables already known to hold the block.
fn is_tls_block_expr(e: &Expr, arrays: &BTreeSet<Key>, blocks: &BTreeSet<Key>) -> bool {
    match e {
        Expr::Var(k) => blocks.contains(k),
        Expr::Deref(a, _) => {
            matches!(&**a, Expr::Bin(Op::Add, base, _) if is_tls_array_expr(base, arrays))
        }
        _ => false,
    }
}

/// Conditional branch captured at a block's end.
#[derive(Debug, Clone)]
pub(super) struct Branch {
    /// The condition under which the branch is taken.
    pub cond: Cond,
    /// Address jumped to when the condition holds.
    pub target: u64,
    /// Address of the fall-through block.
    pub fall: u64,
}

/// How a block re-expresses its `cmp`/`test` flags before a join whose other
/// predecessors compare the same value, so the flags agree at the join.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum Rebase {
    /// Every predecessor names the same registers: write them out and lift
    /// the comparison again over the registers themselves.
    Registers,
    /// Each predecessor compares one register, and this register holds the
    /// compared value on every edge (an alias such as `mov r15d, r13d`):
    /// write it out and let the operands read it.
    Alias(Key),
    /// The flags cannot be carried as they are (operands that differ per
    /// edge, an operand the block rewrites before its end, or block-local
    /// temporaries): each predecessor computes the successor's condition,
    /// under this condition code, into the shared temporary with this id,
    /// and the successor reads the temporary.
    Truth(Cc, u32),
}

/// What a block's position in the function tells the lifter before it runs.
#[derive(Debug, Clone, Copy, Default)]
pub(super) struct BlockFacts<'n> {
    /// Some successor reads the flags this block leaves.
    pub flags_out: bool,
    /// Per instruction, the registers read later with the lane width
    /// ([`need_after`]); `None` treats every register as needed.
    pub need: Option<&'n [FxHashMap<Key, u8>]>,
    /// A variable known to hold a constant throughout the block (the edge
    /// into it was an equality branch).
    pub assume: Option<(Key, u64)>,
    /// First instruction of the block that follows a block-ending call, so
    /// the call can see what reads its result.
    pub after: Option<Instruction>,
    /// The block is the function's entry block (prologue saves happen here).
    pub entry: bool,
    /// The block starts before the function's exception handler is
    /// registered: the first block of a function with an SEH frame, whose
    /// own prologue or the frame helper it calls registers it. Until then
    /// a push is the record's, not a store.
    pub unregistered: bool,
    /// How the out flags are re-expressed before a join whose other
    /// predecessors compare the same value.
    pub rebase_flags: Option<Rebase>,
}

/// A virtual call resolved through the receiver's class.
#[derive(Debug, Clone)]
struct Virtual {
    /// The receiver expression as passed to the callee.
    receiver: Expr,
    /// The variable shown before `->` (the smart pointer itself when the
    /// receiver is the word it holds); `None` shows the receiver expression.
    shown: Option<Key>,
    /// The receiver's class.
    class: String,
    /// The slot function's entry.
    entry: u64,
    /// The slot index in the vtable.
    slot: usize,
    /// The receiver's class leaves the slot pure: its function is the
    /// stub that only reports a pure virtual call, which no object of the
    /// class ever reaches, so the call is the slot's and not the stub's.
    pure: bool,
}

/// Where a call through a dispatch thunk or a read-only pointer goes
/// ([`Exec::dispatch`]).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Dispatch {
    /// The thunk ends in a jump through this register: the call is a call
    /// through the register (the CFG dispatcher's `jmp rax`).
    Through(Register),
    /// The pointer leads to the function at this entry, which only returns
    /// (the CFG check's default): the call does nothing.
    Nothing(u64),
}

/// Returns `T` for a smart-pointer class `X<T>` (`Core::Ptr<UI::Icon>`,
/// `std::shared_ptr<T>`): the class of the object its dereference yields.
///
/// # Arguments
///
/// * `class` - The declared class text.
fn smart_pointee(class: &str) -> Option<&str> {
    crate::analysis::classes::smart_pointee(class)
}

/// Values a block must write out at its end, computed from its OUT state.
pub(super) type PhiFn<'f> = dyn Fn(&Env) -> Vec<Key> + 'f;
/// Is a register still read by some successor of the block?
pub(super) type LiveFn<'f> = dyn Fn(Key) -> bool + 'f;

/// Result of executing one block.
#[derive(Debug, Default)]
pub(super) struct BlockOut {
    /// Emitted pseudo-C statements (empty in the dataflow pass).
    pub lines: Vec<String>,
    /// What those statements do, in the same order, the block's branch or
    /// dispatch last (empty in the dataflow pass).
    pub effects: Vec<Effect>,
    /// The conditional branch ending the block, if any.
    pub branch: Option<Branch>,
    /// Switch index expression when the block ends in a resolved jump table.
    pub switch_idx: Option<Expr>,
    /// Where that jump goes, as an expression: a register's value or the
    /// word its memory operand reads.
    pub switch_target: Option<Expr>,
    /// Unconditional jump target inside this function.
    pub goto: Option<u64>,
    /// Constant-folded outcome of the block's conditional branch: the edge
    /// not taken can be dropped from the CFG the emitter structures.
    pub branch_const: Option<(bool, u64, u64)>,
    /// Slot offsets read before being written in this block, each with
    /// the widest such read in bits.
    pub slot_use: BTreeMap<i64, u8>,
    /// Slot offsets written in this block, each with the widest store in
    /// bits.
    pub slot_def: BTreeMap<i64, u8>,
    /// Slots each call in the block may read, with the frame bytes already
    /// written in the block before that call.
    pub call_uses: Vec<(SlotUse, BTreeSet<i64>)>,
    /// The `cmp`/`test` whose flags the block leaves to its successors.
    pub flag_src: Option<Instruction>,
    /// A successor needed the out flags, but they mention this block's
    /// temporaries and could not cross (a truth temporary can carry them).
    pub tmp_flags: bool,
    /// Instructions the block left as `/* asm */` comments that wrote a
    /// register: every expression after one reads that register as the text
    /// variable the comment left, not as a value the block computed.
    pub unmodeled: usize,
}

/// Which slots a callee may read.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) enum SlotUse {
    /// Any slot (the stack pointer is unknown at the call).
    All,
    /// Offsets in `lo..hi` (the outgoing stack-argument window).
    Window(i64, i64),
}

/// Returns the scalar float type a mnemonic operates on: `sd` forms are
/// doubles, everything else single.
///
/// # Arguments
///
/// * `mn` - A scalar SSE/AVX mnemonic.
fn scalar_ty(mn: Mnemonic) -> Ty {
    match mn {
        Mnemonic::Addsd
        | Mnemonic::Subsd
        | Mnemonic::Mulsd
        | Mnemonic::Divsd
        | Mnemonic::Minsd
        | Mnemonic::Maxsd
        | Mnemonic::Sqrtsd
        | Mnemonic::Vaddsd
        | Mnemonic::Vsubsd
        | Mnemonic::Vmulsd
        | Mnemonic::Vdivsd
        | Mnemonic::Vminsd
        | Mnemonic::Vmaxsd
        | Mnemonic::Vsqrtsd
        | Mnemonic::Vfmadd132sd
        | Mnemonic::Vfmadd213sd
        | Mnemonic::Vfmadd231sd
        | Mnemonic::Vfmsub132sd
        | Mnemonic::Vfmsub213sd
        | Mnemonic::Vfmsub231sd
        | Mnemonic::Cvtsi2sd
        | Mnemonic::Vcvtsi2sd
        | Mnemonic::Cvtss2sd
        | Mnemonic::Vcvtss2sd => Ty::F64,
        _ => Ty::F32,
    }
}

/// Maps a scalar float arithmetic mnemonic to its operator.
///
/// # Arguments
///
/// * `mn` - `add`/`sub`/`mul`/`div`/`min`/`max` in `ss`/`sd`, SSE or AVX form.
fn float_op(mn: Mnemonic) -> Op {
    match mn {
        Mnemonic::Addss | Mnemonic::Addsd | Mnemonic::Vaddss | Mnemonic::Vaddsd => Op::FAdd,
        Mnemonic::Subss | Mnemonic::Subsd | Mnemonic::Vsubss | Mnemonic::Vsubsd => Op::FSub,
        Mnemonic::Mulss | Mnemonic::Mulsd | Mnemonic::Vmulss | Mnemonic::Vmulsd => Op::FMul,
        Mnemonic::Divss | Mnemonic::Divsd | Mnemonic::Vdivss | Mnemonic::Vdivsd => Op::FDiv,
        Mnemonic::Minss | Mnemonic::Minsd | Mnemonic::Vminss | Mnemonic::Vminsd => Op::FMin,
        _ => Op::FMax,
    }
}

/// Tells whether an operand kind is an immediate.
///
/// # Arguments
///
/// * `k` - The operand kind.
fn is_imm(k: OpKind) -> bool {
    matches!(
        k,
        OpKind::Immediate8
            | OpKind::Immediate8_2nd
            | OpKind::Immediate16
            | OpKind::Immediate32
            | OpKind::Immediate64
            | OpKind::Immediate8to16
            | OpKind::Immediate8to32
            | OpKind::Immediate8to64
            | OpKind::Immediate32to64
    )
}

/// Block executor: owns the lines being produced for one block.
pub(super) struct Exec<'c, 'a> {
    /// Per-function decompilation state (declarations, globals, escape floor).
    pub(super) ctx: &'c mut Ctx<'a>,
    /// The symbolic state, advanced instruction by instruction.
    pub(super) env: &'c mut Env,
    /// Statements emitted so far.
    pub(super) lines: Vec<String>,
    /// What those statements do, recorded beside them.
    pub(super) effects: Vec<Effect>,
    /// The instruction being lifted, which the effects it records name.
    pub(super) at: u64,
    /// What the flags register holds right now.
    pub(super) flags: Flags,
    /// Switch index captured at a jump-table dispatch (protected like flags).
    pub(in crate::analysis::decompile) switch_idx: Option<Expr>,
    /// Recording declarations and temporaries only in the emission pass.
    pub(super) emit: bool,
    /// Temporary counter of the dataflow pass (the emission pass counts in
    /// `ctx`); it starts at [`BLOCK_TMP`] so these never collide with the
    /// shared temporaries a join allocates from `ctx`.
    tmp_local: u32,
    /// Register read/write facts for instructions without a model.
    info: InstructionInfoFactory,
    /// Slot offsets read before being written in this block, each with
    /// the widest such read in bits.
    pub(super) slot_use: BTreeMap<i64, u8>,
    /// Slot offsets written in this block, each with the widest store in
    /// bits.
    pub(super) slot_def: BTreeMap<i64, u8>,
    /// Slots each call may read, with the frame bytes written before it.
    pub(super) call_uses: Vec<(SlotUse, BTreeSet<i64>)>,
    /// Is the return register read by a successor? (`None`: not known yet.)
    rax_live_out: Option<bool>,
    /// Values written out early for size, by key: a jump-table target
    /// computed through a wide index expression is found here.
    big_written: BTreeMap<Key, Expr>,
    /// While an instruction with several results records them, the
    /// variables whose early write-out waits until all are recorded
    /// ([`Exec::reg_write_all`]).
    pub(super) deferred: Option<Vec<Key>>,
    /// Flag bits a later reader needs, in the block or after it: none when
    /// the flags are dead at the current instruction, every bit when the
    /// reader is out of sight.
    pub(super) flags_needed: u32,
    /// A variable known to hold a constant throughout this block (the edge
    /// into it was an equality branch); substituted into every value read.
    assume: Option<(Key, u64)>,
    /// The block is the function's entry block.
    entry: bool,
    /// The handler registration is behind us: false only in the entry block
    /// of a function that registers one, until its `fs:[0]` store or frame
    /// helper has run, so the prologue's pushes of the try level, the
    /// handler and the chain's head render as nothing.
    seh_registered: bool,
    /// Words pushed since the last call, register saves and the handler
    /// record left out: the arguments an indirect call to an unknown callee
    /// takes, and what it pops when no `add esp` follows.
    args_pushed: u32,
    /// Words the caller cleans up right after the `__cdecl` call being
    /// lifted ([`Exec::stack_after`]): the arguments it passes, which may
    /// be more than the callee's body reads by name (a variable list past
    /// its `va_start`). `None` when nothing cleans them up there.
    cleaned: Option<u32>,
    /// The call being lifted renders fewer stack words than its callee is
    /// stated to read ([`Exec::args_for`]): its text leaves out arguments
    /// the machine passes, which the next recorded call carries
    /// ([`Call::short`]).
    args_short: bool,
    /// A declaration stated for the callee of the call being lifted
    /// contradicts the code around it, which the next recorded call
    /// carries ([`Call::contradicted`]).
    stated_contradicted: bool,
    /// A tail jump is being lifted: the callee's stack arguments are the
    /// caller's own, above the return address the jump leaves in place.
    forwarding: bool,
    /// A callee is being read in place of its call ([`Exec::trivial_callee`]);
    /// a call it jumps on to is not read in place again.
    in_place: bool,
    /// The fewest arguments a virtual call being lifted passes: the most any
    /// override of its slot reads ([`Exec::family_arity`]).
    arity_floor: usize,
    /// The argument register an indirect call goes through (`call [r8]`
    /// with the vtable pointer in `r8`): scratch, not an argument, and
    /// the arguments end before its slot.
    call_through: Option<Register>,
    /// The object a call through a vtable is made on: the register holding
    /// it carries the first argument whether or not the caller set it for
    /// this call (`mov rax, [rcx]; call [rax+8]` passes the `rcx` it read).
    receiver: Option<Expr>,
    /// The volatile registers the callee of the call being lifted leaves as
    /// it found them ([`preserved_volatiles`]): their values survive it.
    preserved: Vec<Key>,
    /// Registers assigned so far in this block execution (a save must precede any).
    written_here: BTreeSet<Key>,
    /// The `cmp`/`test` that produced the current flags, when one did.
    flag_src: Option<Instruction>,
    /// A floating-point compare in this block produced the current flags
    /// (`ucomisd`, `fcomip`, a `sahf` of a compare's status).
    float_flags: bool,
    /// `ah` holds the status bits of these floating-point compare flags,
    /// as a read of `ah` gives them right after `lahf` or `fnstsw ax`
    /// put them there; `test ah, 0x44` reads the compare through them.
    status_ah: Option<(Expr, Flags)>,
    /// Registers some later instruction reads once the current one has run,
    /// with the lane width needed; `None` when unknown (everything is needed).
    pub(in crate::analysis::decompile) regs_needed: Option<FxHashMap<Key, u8>>,
    /// For the current instruction, how many later instructions of the
    /// block read each register it writes ([`read_counts`]).
    reads_ahead: FxHashMap<Key, u32>,
    /// Instructions of this block without a model that wrote a register
    /// ([`Exec::unmodeled`]).
    pub(super) unmodeled: usize,
}

impl<'c, 'a> Exec<'c, 'a> {
    /// Builds the executor of one block: nothing written yet, the flags
    /// the predecessors left taken out of the environment, and the block's
    /// facts in force.
    ///
    /// # Arguments
    ///
    /// * `ctx` - Per-function state.
    /// * `env` - State at the block's entry.
    /// * `pass` - Record text (the emission pass) or only compute state.
    /// * `facts` - The equality the block runs under, whether it is the
    ///   entry block, and whether its handler is registered yet.
    /// * `at` - The block's first address.
    pub(super) fn new(
        ctx: &'c mut Ctx<'a>,
        env: &'c mut Env,
        pass: Pass,
        facts: &BlockFacts<'_>,
        at: u64,
    ) -> Self {
        let inherited = std::mem::replace(&mut env.flags, Flags::Unknown);
        Exec {
            ctx,
            env,
            lines: Vec::new(),
            effects: Vec::new(),
            at,
            flags: inherited,
            switch_idx: None,
            emit: pass == Pass::Emission,
            tmp_local: BLOCK_TMP,
            info: InstructionInfoFactory::new(),
            slot_use: BTreeMap::new(),
            slot_def: BTreeMap::new(),
            call_uses: Vec::new(),
            rax_live_out: None,
            flags_needed: u32::MAX,
            big_written: BTreeMap::new(),
            deferred: None,
            assume: facts.assume,
            entry: facts.entry,
            seh_registered: !facts.unregistered,
            args_pushed: 0,
            cleaned: None,
            args_short: false,
            stated_contradicted: false,
            forwarding: false,
            in_place: false,
            arity_floor: 0,
            call_through: None,
            receiver: None,
            preserved: Vec::new(),
            written_here: BTreeSet::new(),
            flag_src: None,
            float_flags: false,
            status_ah: None,
            regs_needed: None,
            reads_ahead: FxHashMap::default(),
            unmodeled: 0,
        }
    }
}

/// Executes one block from `env`, returning its lines and control-flow facts.
///
/// Flags inherited from the predecessors seed the executor. Flag liveness is
/// computed backwards inside the block (a flag is dead after its last reader
/// before the next writer), so dead flags are never protected in temporaries;
/// the block's own branch always counts as a reader, and `flags_out` keeps
/// them live to the end. After the phi writes the branch condition is
/// captured, and the flags are handed on to the environment only when a
/// successor wants them and no temporary is involved (temporaries are
/// numbered per pass).
///
/// # Arguments
///
/// * `ctx` - Per-function state.
/// * `instrs` - The block's instructions.
/// * `prev` - The block preceding it in address order (switch index probe).
/// * `env` - State at the block's entry; updated to the state at its exit.
/// * `pass` - Record text (the emission pass) or only compute state (dataflow).
/// * `phi` - Values the block must write out at its end because a successor
///   lost them at a join, and the liveness oracle used while doing so.
/// * `facts` - Whether a successor reads the flags, the equality the block
///   runs under, and the per-instruction register needs.
///
/// # Returns
///
/// The lines and the block's branch, jump, switch index and slot facts.
pub(super) fn exec_block(
    ctx: &mut Ctx<'_>,
    instrs: &[Instruction],
    prev: Option<&[Instruction]>,
    env: &mut Env,
    pass: Pass,
    phi: Option<(&PhiFn<'_>, &LiveFn<'_>)>,
    facts: BlockFacts<'_>,
) -> BlockOut {
    let flags_out = facts.flags_out;
    let mut ex = Exec::new(
        ctx,
        env,
        pass,
        &facts,
        instrs.first().map_or(0, Instruction::ip),
    );
    if let Some((_, live)) = phi {
        let rax = Key::Reg(canon(Register::RAX, ex.bitness()));
        ex.rax_live_out = Some(live(rax));
    }
    let mut flags_live_after = vec![0u32; instrs.len()];
    let mut live_flags: u32 = if flags_out { u32::MAX } else { 0 };
    for (idx, instr) in instrs.iter().enumerate().rev() {
        flags_live_after[idx] = live_flags;
        live_flags = (live_flags & !instr.rflags_modified()) | instr.rflags_read();
    }
    let mut out = BlockOut::default();
    let mut jcc: Option<(Cc, u64, u64)> = None;
    let mut go_folded = false;
    let reads_ahead = read_counts(&*ex.ctx, &mut ex.info, instrs);
    for (idx, instr) in instrs.iter().enumerate() {
        ex.at = instr.ip();
        if let Some(c) = ex.ctx.overlay.comments.get(&instr.ip()) {
            ex.lines.push(format!("// {c}"));
        }
        ex.flags_needed = flags_live_after[idx];
        if let Some(src) = facts.need.and_then(|n| n.get(idx)) {
            ex.regs_needed.get_or_insert_default().clone_from(src);
        } else {
            ex.regs_needed = None;
        }
        if let Some(src) = reads_ahead.get(idx) {
            ex.reads_ahead.clone_from(src);
        } else {
            ex.reads_ahead.clear();
        }
        let next = instrs.get(idx + 1);
        match instr.flow_control() {
            FlowControl::ConditionalBranch => {
                if let Some(t) = near_target(instr) {
                    jcc = Some((Cc(instr.condition_code()), t, instr.next_ip()));
                    go_folded = ex
                        .ctx
                        .go_check
                        .as_ref()
                        .is_some_and(|(at, _)| *at == instr.ip());
                } else {
                    ex.unmodeled(instr);
                }
            }
            FlowControl::UnconditionalBranch => match near_target(instr) {
                Some(t) if ex.ctx.block_starts.contains(&t) => out.goto = Some(t),
                Some(t) => ex.tail_call(t),
                None => {
                    if ex.ctx.analysis.jump_tables.contains_key(&instr.ip()) {
                        out.switch_target = ex.jump_target(instr);
                        ex.switch_idx = ex.switch_index(instr, instrs, prev);
                    } else {
                        ex.indirect_jump(instr);
                    }
                }
            },
            FlowControl::IndirectBranch => {
                if ex.ctx.analysis.jump_tables.contains_key(&instr.ip()) {
                    out.switch_target = ex.jump_target(instr);
                    ex.switch_idx = ex.switch_index(instr, instrs, prev);
                } else {
                    ex.indirect_jump(instr);
                }
            }
            FlowControl::Call | FlowControl::IndirectCall => {
                ex.call(
                    instr,
                    next.or(facts.after.as_ref()),
                    instrs.get(idx + 1..).unwrap_or(&[]),
                );
            }
            FlowControl::Return => ex.ret(),
            FlowControl::Next
            | FlowControl::Interrupt
            | FlowControl::Exception
            | FlowControl::XbeginXabortXend => ex.step(instr),
        }
        if instr.rflags_modified() != 0 {
            ex.flag_src =
                matches!(instr.mnemonic(), Mnemonic::Cmp | Mnemonic::Test).then_some(*instr);
            ex.float_flags = matches!(
                instr.mnemonic(),
                Mnemonic::Ucomiss
                    | Mnemonic::Ucomisd
                    | Mnemonic::Comiss
                    | Mnemonic::Comisd
                    | Mnemonic::Vucomiss
                    | Mnemonic::Vucomisd
                    | Mnemonic::Vcomiss
                    | Mnemonic::Vcomisd
                    | Mnemonic::Fcomi
                    | Mnemonic::Fcomip
                    | Mnemonic::Fucomi
                    | Mnemonic::Fucomip
                    | Mnemonic::Sahf
            );
        }
    }
    if jcc.is_none() && ex.switch_idx.is_none() && !flags_out {
        ex.flags = Flags::Unknown;
    }
    ex.flags_needed = u32::MAX;
    if let Some((phi, live)) = phi {
        for k in phi(ex.env) {
            ex.materialize_phi(k, live);
        }
    }
    let branch_flags = ex.flags.clone();
    if let Some(how) = facts.rebase_flags {
        let src = ex.flag_src;
        ex.rebase_flags(src.as_ref(), how);
    }
    if let Some((cc, target, fall)) = jcc {
        let flags = match &ex.flags {
            _ if go_folded => Flags::Cmp(Expr::Const(1), Expr::Const(0), 64),
            Flags::Truth(_, tcc) if *tcc != cc && tcc.invert() != cc => branch_flags,
            _ => ex.flags.clone(),
        };
        let cond = Cond { cc, flags };
        out.branch_const = cond.eval().map(|taken| (taken, target, fall));
        if ex.emit {
            ex.record(EffectKind::Branch(cond.clone()));
        }
        out.branch = Some(Branch { cond, target, fall });
    }
    let is_tmp = |k: Key| matches!(k, Key::Tmp(_));
    let crosses = matches!(ex.flags, Flags::Truth(..)) || !ex.flags.any_var(&is_tmp);
    out.tmp_flags = flags_out && !crosses;
    ex.env.flags = if flags_out && crosses {
        ex.flags.clone()
    } else {
        Flags::Unknown
    };
    out.switch_idx = ex.switch_idx.take();
    if let Some(idx) = out.switch_idx.as_ref().filter(|_| ex.emit) {
        ex.record(EffectKind::Switch(idx.clone()));
    }
    out.flag_src = ex.flag_src;
    out.lines = ex.lines;
    if ex.emit
        && let Some(start) = instrs.first().map(Instruction::ip)
        && let std::collections::btree_map::Entry::Vacant(first) = ex.ctx.effects.entry(start)
    {
        let mut packed = Vec::new();
        pack(&ex.effects, start, &mut packed);
        first.insert(packed);
    }
    out.effects = ex.effects;
    out.slot_use = ex.slot_use;
    out.slot_def = ex.slot_def;
    out.call_uses = ex.call_uses;
    out.unmodeled = ex.unmodeled;
    out
}

/// Strips the upper-bit merge from a byte or word write into the return register.
///
/// # Arguments
///
/// * `v` - The return register's value.
///
/// # Returns
///
/// `(value the caller sees, its width)`: the placed field and 8 or 16 for
/// `(old & ~mask) | v`, else `v` itself and 64.
fn strip_partial_result(v: Expr) -> (Expr, u8) {
    if let Expr::Bin(Op::Or, kept, placed) = &v
        && let Expr::Bin(Op::And, _, m) = kept.as_ref()
        && let Expr::Const(m) = m.as_ref()
    {
        for bits in [8u8, 16] {
            if *m == !((1u64 << bits) - 1) {
                return (placed.as_ref().clone(), bits);
            }
        }
    }
    (v, 64)
}

/// Strips from an argument the merge of a byte or word into the argument
/// register's own old bits.
///
/// `mov r8b, 1` before a call passes a `bool` or a `char`: the callee reads
/// the byte and the rest of the register is whatever it held, so
/// `(r8 & ~0xff) | 1` is `1`. A merge into anything but the register
/// itself is a value the code computed and stays.
///
/// # Arguments
///
/// * `e` - The argument's value.
/// * `r` - The argument register, canonical.
fn strip_own_merge(e: &Expr, r: Register) -> Expr {
    if let Expr::Bin(Op::Or, kept, placed) = e
        && let Expr::Bin(Op::And, old, m) = kept.as_ref()
        && **old == Expr::Var(Key::Reg(r))
        && let Expr::Const(m) = m.as_ref()
        && [8u8, 16].iter().any(|bits| *m == !((1u64 << bits) - 1))
    {
        return placed.as_ref().clone();
    }
    e.clone()
}

/// Returns the operand width of an instruction in bits.
///
/// # Arguments
///
/// * `instr` - The instruction: the first operand's size, else the memory
///   size, else the machine word.
fn op_bits(instr: &Instruction) -> u8 {
    let size = match instr.op0_kind() {
        OpKind::Register => instr.op0_register().size(),
        OpKind::Memory
        | OpKind::MemoryESRDI
        | OpKind::MemoryESEDI
        | OpKind::MemorySegRSI
        | OpKind::MemorySegESI => instr.memory_size().size(),
        _ => 0,
    };
    match size {
        0 => 64,
        n => u8::try_from((n * 8).min(128)).unwrap_or(64),
    }
}

/// Returns the width in bits of operand `op` (a register or memory source).
///
/// # Arguments
///
/// * `instr` - The instruction.
/// * `op` - Operand index; other operand kinds count as 64.
fn src_bits(instr: &Instruction, op: u32) -> u8 {
    match instr.op_kind(op) {
        OpKind::Register => u8::try_from(instr.op_register(op).size() * 8).unwrap_or(64),
        OpKind::Memory => u8::try_from(instr.memory_size().size() * 8).unwrap_or(64),
        _ => 64,
    }
}

/// Renders a call through a computed pointer as `(*p)`.
///
/// # Arguments
///
/// * `target` - The pointer value; parenthesized unless a plain name or constant.
/// * `n` - Name resolution.
fn call_through(target: &Expr, n: &Names<'_>) -> String {
    match target {
        Expr::Var(_) | Expr::Const(_) => format!("(*{})", target.render(n)),
        _ => format!("(*({}))", target.render(n)),
    }
}

/// Finds the register compared by the last `cmp reg, ...` in a block.
///
/// # Arguments
///
/// * `list` - The block's instructions.
fn last_cmp_register(list: &[Instruction]) -> Option<Register> {
    list.iter()
        .rev()
        .find(|i| i.mnemonic() == Mnemonic::Cmp && i.op0_kind() == OpKind::Register)
        .map(|i| i.op0_register())
}

/// Tells whether two stack accesses overlap.
///
/// # Arguments
///
/// * `a` - Offset of the first access.
/// * `a_bits` - Its width in bits (at least one byte).
/// * `b` - Offset of the second access.
/// * `b_bits` - Its width in bits.
fn ranges_overlap(a: i64, a_bits: u8, b: i64, b_bits: u8) -> bool {
    let a_end = a + i64::from(a_bits / 8).max(1);
    let b_end = b + i64::from(b_bits / 8).max(1);
    a < b_end && b < a_end
}

/// A numbered slot name as a call spells it: `vfunc_3_627`, the 627th
/// function named for slot 3, is the slot's method `vfunc_3` at a call
/// through the class; any other name is kept.
///
/// # Arguments
///
/// * `method` - The method part of the callee's name.
fn slot_method(method: &str) -> &str {
    let Some(rest) = method.strip_prefix("vfunc_") else {
        return method;
    };
    match rest.split_once('_') {
        Some((k, n))
            if !k.is_empty()
                && !n.is_empty()
                && k.bytes().all(|b| b.is_ascii_digit())
                && n.bytes().all(|b| b.is_ascii_digit()) =>
        {
            &method[..method.len() - n.len() - 1]
        }
        _ => method,
    }
}

/// Spells a constant a float instruction reads as the float its bits are.
///
/// A float constant reaches a float instruction through an integer move
/// (`mov dword [rsp+0x60], 0x3f800000` then `movss xmm0, [rsp+0x60]`), so
/// the value arrives as integer bits; a float instruction reading them
/// reads `1.0f`, exactly.
///
/// # Arguments
///
/// * `v` - The operand's value.
/// * `ty` - The float type the instruction reads.
fn float_bits(v: Expr, ty: Ty) -> Expr {
    match (v, ty) {
        (Expr::Const(bits), Ty::F32 | Ty::F64) => Expr::FConst(bits, ty),
        (other, _) => other,
    }
}

/// The width a scalar float expression already carries.
///
/// A bare register carries none: nothing in this function cleared the
/// bits above an incoming value. A select carries a width when either
/// arm does.
///
/// # Arguments
///
/// * `v` - The value a scalar float instruction reads.
fn float_lane(v: &Expr) -> Option<u8> {
    match v {
        Expr::Deref(_, ty) | Expr::Cast(_, ty) | Expr::FConst(_, ty) => {
            matches!(ty, Ty::F32 | Ty::F64).then_some(ty.bits())
        }
        Expr::Bin(op, l, r) if op.is_float() => Some(float_lane(l)?.max(float_lane(r)?)),
        Expr::Un(UnOp::Sqrt | UnOp::Fabs | UnOp::Neg, inner) => float_lane(inner),
        Expr::Ternary(_, a, b) => either_width(float_lane(a), float_lane(b)),
        Expr::Call(name, args) if name == "fabs" => args.first().and_then(float_lane),
        Expr::Const(_)
        | Expr::Var(_)
        | Expr::Str(_)
        | Expr::Sp(_)
        | Expr::Bin(..)
        | Expr::Un(..)
        | Expr::Cond(_)
        | Expr::Sext(..)
        | Expr::Call(..) => None,
    }
}

/// Whether a single's bits above bit 31 are zero in this function.
///
/// `movss` from memory zeroes them, and a later scalar single keeps them
/// zero when its destination already had them zero. A legacy scalar single
/// does not clear them on its own, and a cast down from a double did not
/// either.
///
/// # Arguments
///
/// * `v` - The value held before a wider read.
fn lane_zeros_above(v: &Expr) -> bool {
    match v {
        Expr::FConst(_, Ty::F32) | Expr::Deref(_, Ty::F32) => true,
        Expr::Un(UnOp::Neg | UnOp::Fabs, inner) => lane_zeros_above(inner),
        Expr::Bin(op, l, r) if op.is_float() => {
            float_lane(l) == Some(32) && float_lane(r) == Some(32) && lane_zeros_above(l)
        }
        Expr::Const(_)
        | Expr::FConst(_, _)
        | Expr::Var(_)
        | Expr::Str(_)
        | Expr::Sp(_)
        | Expr::Bin(..)
        | Expr::Un(..)
        | Expr::Deref(_, _)
        | Expr::Cond(_)
        | Expr::Ternary(..)
        | Expr::Sext(..)
        | Expr::Cast(..)
        | Expr::Call(..) => false,
    }
}

/// Sign bit of a 32-bit lane.
const SIGN32: u64 = 0x8000_0000;

/// Sign bit of both 32-bit lanes in a qword: a broadcast `xorps` mask.
const SIGN32_SPLAT: u64 = 0x8000_0000_8000_0000;

/// Magnitude mask of a 32-bit lane. Anding a qword with it clears the rest.
const MAG32: u64 = 0x7fff_ffff;

/// Magnitude mask of both 32-bit lanes in a qword.
const MAG32_SPLAT: u64 = 0x7fff_ffff_7fff_ffff;

/// Bit 63, which a broadcast 32-bit sign mask sets in a zero-extended single.
const SIGN_ABOVE: u64 = 0x8000_0000_0000_0000;

/// The value `xorps` or `andps` with a sign or magnitude mask leaves.
///
/// A 32-bit mask whose later lanes are zero, applied to a single that
/// already has zeros above, is a negation or an `fabs`: the bits above
/// stay zero. The same sign mask broadcast over every lane sets bit 63
/// as well, so a wider read is not that zero-extend. Applied to a double,
/// a scalar sign mask flips only bit 31 and leaves the high half, a
/// broadcast sign mask flips bit 31 and bit 63, a scalar magnitude mask
/// clears everything above the low lane, and a broadcast one clears both
/// lanes' signs. Anything else stays the unary form: a mixed mask, a
/// 64-bit lane mask, or a single whose bits above this function did not
/// clear and does not hold as a double.
///
/// # Arguments
///
/// * `abs` - Magnitude mask (`andps`), otherwise a sign mask (`xorps`).
/// * `ty` - The lane width [`Exec::float_mask`] reported.
/// * `broadcast` - `Some(true)` when later lanes repeat the mask,
///   `Some(false)` when they are zero, `None` when they mix.
/// * `x` - The register's value.
fn masked_lanes(abs: bool, ty: Ty, broadcast: Option<bool>, x: Expr) -> Expr {
    let plain = Expr::Un(
        if abs { UnOp::Fabs } else { UnOp::Neg },
        Box::new(x.clone()),
    );
    if ty != Ty::F32 {
        return plain;
    }
    let Some(broadcast) = broadcast else {
        return plain;
    };
    if lane_zeros_above(&x) {
        if !abs && broadcast {
            return sign_above_zero(x);
        }
        return plain;
    }
    if float_lane(&x) != Some(64) {
        return plain;
    }
    let (op, mask) = match (abs, broadcast) {
        (false, false) => (Op::Xor, SIGN32),
        (false, true) => (Op::Xor, SIGN32_SPLAT),
        (true, false) => (Op::And, MAG32),
        (true, true) => (Op::And, MAG32_SPLAT),
    };
    Expr::Bin(op, Box::new(x), Box::new(Expr::Const(mask)))
}

/// The low 32 bits of `low`, with bit 63 set.
///
/// That is the shape a broadcast 32-bit sign mask leaves, and the shape a
/// later scalar single leaves when it replaces the lane and keeps the bit.
///
/// # Arguments
///
/// * `low` - The new low lane.
fn with_sign_above(low: Expr) -> Expr {
    let low = Expr::Bin(Op::And, Box::new(low), Box::new(Expr::Const(0xffff_ffff)));
    Expr::Bin(Op::Or, Box::new(low), Box::new(Expr::Const(SIGN_ABOVE)))
}

/// A zero-extended single with its sign flipped and bit 63 set.
///
/// That is a broadcast 32-bit sign mask xored into a `movss` load: lane
/// zero is the negation, and the next lane is the sign bit rather than zero.
///
/// # Arguments
///
/// * `x` - The single.
fn sign_above_zero(x: Expr) -> Expr {
    with_sign_above(Expr::Un(UnOp::Neg, Box::new(x)))
}

/// Bits 63:32, which a scalar single leaves alone.
const HIGH32: u64 = 0xffff_ffff_0000_0000;

/// The low lane of `v` beside the value that holds bits 63:32.
///
/// A scalar single replaces the low lane and keeps this half. The two
/// halves are the masks, in either order.
///
/// # Arguments
///
/// * `v` - The register's value.
fn merged_parts(v: &Expr) -> Option<(&Expr, &Expr)> {
    let Expr::Bin(Op::Or, a, b) = v else {
        return None;
    };
    match (masked_half(a), masked_half(b)) {
        (Some((true, low)), Some((false, high))) | (Some((false, high)), Some((true, low))) => {
            Some((high, low))
        }
        _ => None,
    }
}

/// One half of a merged scalar single: `true` is the low lane.
///
/// # Arguments
///
/// * `e` - One side of the `or`.
fn masked_half(e: &Expr) -> Option<(bool, &Expr)> {
    let Expr::Bin(Op::And, x, m) = e else {
        return None;
    };
    let Expr::Const(mask) = m.as_ref() else {
        return None;
    };
    match *mask {
        0xffff_ffff => Some((true, x.as_ref())),
        HIGH32 => Some((false, x.as_ref())),
        _ => None,
    }
}

/// The low lane of `low`, with the bits above it taken from `upper`.
///
/// # Arguments
///
/// * `upper` - The value whose bits 63:32 survive.
/// * `low` - The new low lane.
fn merge_low_lane(upper: Expr, low: Expr) -> Expr {
    let high = Expr::Bin(Op::And, Box::new(upper), Box::new(Expr::Const(HIGH32)));
    let low = Expr::Bin(Op::And, Box::new(low), Box::new(Expr::Const(0xffff_ffff)));
    Expr::Bin(Op::Or, Box::new(high), Box::new(low))
}

/// The low lane of a value whose bit 63 a broadcast sign set.
///
/// The lane is the negation when the mask itself was the last writer. A
/// scalar single that ran after the mask leaves its own low lane there
/// and keeps the same high bit.
///
/// # Arguments
///
/// * `v` - The register's value.
fn sign_above_low(v: &Expr) -> Option<&Expr> {
    let Expr::Bin(Op::Or, low, high) = v else {
        return None;
    };
    if !matches!(high.as_ref(), Expr::Const(SIGN_ABOVE)) {
        return None;
    }
    let Expr::Bin(Op::And, bits, mask) = low.as_ref() else {
        return None;
    };
    matches!(mask.as_ref(), Expr::Const(0xffff_ffff)).then_some(bits)
}

/// A double xored with a 32-bit sign mask, scalar or broadcast.
///
/// # Arguments
///
/// * `v` - The register's value.
fn sign_xor(v: &Expr) -> Option<(&Expr, u64)> {
    let Expr::Bin(Op::Xor, x, m) = v else {
        return None;
    };
    let Expr::Const(mask) = m.as_ref() else {
        return None;
    };
    if !matches!(*mask, SIGN32 | SIGN32_SPLAT) || !x.is_float() {
        return None;
    }
    Some((x, *mask))
}

/// A double anded with a 32-bit magnitude mask, scalar or broadcast.
///
/// # Arguments
///
/// * `v` - The register's value.
fn mag_and(v: &Expr) -> Option<(&Expr, u64)> {
    let Expr::Bin(Op::And, x, m) = v else {
        return None;
    };
    let Expr::Const(mask) = m.as_ref() else {
        return None;
    };
    if !matches!(*mask, MAG32 | MAG32_SPLAT) || !x.is_float() {
        return None;
    }
    Some((x, *mask))
}

/// The low 32 bits of `v` as a float, without converting the number.
///
/// # Arguments
///
/// * `v` - The value.
fn low_single(v: Expr) -> Expr {
    if float_lane(&v) == Some(32) {
        return v;
    }
    Expr::Cast(
        Box::new(Expr::Bin(
            Op::And,
            Box::new(v),
            Box::new(Expr::Const(0xffff_ffff)),
        )),
        Ty::F32,
    )
}

/// A 64-bit read of a scalar single that kept bits 63:32.
///
/// The low lane is a float so the read is those bits, not the integer
/// they form converted to a double. The high half is the value the single
/// left there.
///
/// # Arguments
///
/// * `high` - The value whose bits 63:32 survive.
/// * `low` - The low lane.
fn merged_as_double(high: &Expr, low: &Expr) -> Expr {
    let bits = Expr::Cast(
        Box::new(Expr::Bin(
            Op::And,
            Box::new(low.clone()),
            Box::new(Expr::Const(0xffff_ffff)),
        )),
        Ty::F64,
    );
    let high = Expr::Bin(
        Op::And,
        Box::new(high.clone()),
        Box::new(Expr::Const(HIGH32)),
    );
    Expr::Cast(
        Box::new(Expr::Bin(Op::Or, Box::new(bits), Box::new(high))),
        Ty::F64,
    )
}

/// A 64-bit read of a value whose high bit is [`SIGN_ABOVE`].
///
/// The cast keeps the bits. The low half is a float so the read is not an
/// integer converted to a double.
///
/// # Arguments
///
/// * `low` - The low lane, the negation or a later scalar single.
fn sign_above_as_double(low: &Expr) -> Expr {
    let bits = Expr::Cast(
        Box::new(Expr::Bin(
            Op::And,
            Box::new(low.clone()),
            Box::new(Expr::Const(0xffff_ffff)),
        )),
        Ty::F64,
    );
    Expr::Cast(
        Box::new(Expr::Bin(
            Op::Or,
            Box::new(bits),
            Box::new(Expr::Const(SIGN_ABOVE)),
        )),
        Ty::F64,
    )
}

/// The low lane a scalar single wrote beside kept bits, as a float.
///
/// The lane is the single the instruction computed, so a float value is
/// that number already; anything else is reinterpreted bits
/// ([`low_single`]).
///
/// # Arguments
///
/// * `low` - The low half of a merged value ([`merged_parts`]).
fn merged_low(low: &Expr) -> Expr {
    if low.is_float() {
        low.clone()
    } else {
        low_single(low.clone())
    }
}

/// The value a float `return` hands back from xmm0.
///
/// A scalar single that kept the bits above its lane leaves a merged
/// value, of which the caller reads only the low lane.
///
/// # Arguments
///
/// * `v` - The register's value at the `ret`.
pub(super) fn float_result(v: Expr) -> Expr {
    match merged_parts(&v) {
        Some((_, low)) => merged_low(low),
        None => v,
    }
}

/// Reads a sign or magnitude mask at the lane `ty` names, when `v` is one.
///
/// A 32-bit read is the lane's negation or `fabs`. A 64-bit read is the
/// bits the mask left, not a zero-extend and not the number converted.
///
/// # Arguments
///
/// * `v` - The register's value.
/// * `ty` - The lane the instruction reads.
fn lane_of_mask(v: &Expr, ty: Ty) -> Option<Expr> {
    if let Some(low) = sign_above_low(v) {
        return Some(if ty == Ty::F32 {
            low_single(low.clone())
        } else {
            sign_above_as_double(low)
        });
    }
    if let Some((high, low)) = merged_parts(v) {
        return Some(if ty == Ty::F32 {
            merged_low(low)
        } else {
            merged_as_double(high, low)
        });
    }
    if let Some((inner, _)) = sign_xor(v) {
        return Some(if ty == Ty::F32 {
            Expr::Un(UnOp::Neg, Box::new(low_single(inner.clone())))
        } else {
            Expr::Cast(Box::new(v.clone()), Ty::F64)
        });
    }
    if let Some((inner, _)) = mag_and(v) {
        return Some(if ty == Ty::F32 {
            Expr::Un(UnOp::Fabs, Box::new(low_single(inner.clone())))
        } else {
            Expr::Cast(Box::new(v.clone()), Ty::F64)
        });
    }
    None
}

/// Stores a sign or magnitude mask as the bytes `movss` or `movsd` copy.
///
/// A 32-bit store of a zero-extended single is the negation, and a 32-bit
/// store after a scalar single is that single's new lane. A 32-bit store
/// of a double is the low lane's bits, not a negation of the number: a
/// numeric negation changes a NaN's payload. A 64-bit store is the integer
/// the bits are, so it does not convert them and does not drop a sign bit
/// the mask set above the lane.
///
/// # Arguments
///
/// * `v` - The register's value.
/// * `bits` - The store's width, 32 or 64.
fn moved_lane_mask(v: &Expr, bits: u8) -> Option<(Ty, Expr)> {
    if let Some(low) = sign_above_low(v) {
        return Some(if bits <= 32 {
            (Ty::F32, low_single(low.clone()))
        } else {
            (Ty::U64, v.clone())
        });
    }
    if let Some((_, low)) = merged_parts(v) {
        return Some(if bits <= 32 {
            (Ty::F32, low_single(low.clone()))
        } else {
            (Ty::U64, v.clone())
        });
    }
    if let Some((inner, mask)) = sign_xor(v) {
        return Some(if bits <= 32 {
            let low = Expr::Bin(
                Op::Xor,
                Box::new(inner.clone()),
                Box::new(Expr::Const(mask & 0xffff_ffff)),
            );
            (
                Ty::U32,
                Expr::Bin(Op::And, Box::new(low), Box::new(Expr::Const(0xffff_ffff))),
            )
        } else {
            (Ty::U64, v.clone())
        });
    }
    if let Some((inner, _)) = mag_and(v) {
        return Some(if bits <= 32 {
            (
                Ty::U32,
                Expr::Bin(
                    Op::And,
                    Box::new(inner.clone()),
                    Box::new(Expr::Const(MAG32)),
                ),
            )
        } else {
            (Ty::U64, v.clone())
        });
    }
    None
}

/// Whether `v` may still hold lanes above the low qword.
///
/// A 128-bit load, a vector register this function has not narrowed, or a
/// move that copied one of those, still has bits a scalar write must not
/// drop. A scalar load, a merged lane, or float arithmetic does not.
///
/// # Arguments
///
/// * `v` - The register's value.
fn keeps_vector(v: &Expr) -> bool {
    match v {
        Expr::Deref(_, Ty::U128) => true,
        Expr::Var(Key::Reg(r)) => r.is_vector_register(),
        Expr::Var(Key::Param(_)) => true,
        Expr::Call(name, _) => matches!(
            name.as_str(),
            "movss"
                | "movsd"
                | "vmovss"
                | "vmovsd"
                | "movups"
                | "movaps"
                | "movupd"
                | "movapd"
                | "movdqa"
                | "movdqu"
                | "vmovups"
                | "vmovaps"
                | "vmovupd"
                | "vmovapd"
                | "vmovdqa"
                | "vmovdqu"
        ),
        Expr::Const(_)
        | Expr::FConst(_, _)
        | Expr::Var(_)
        | Expr::Str(_)
        | Expr::Sp(_)
        | Expr::Bin(..)
        | Expr::Un(..)
        | Expr::Deref(_, _)
        | Expr::Cond(_)
        | Expr::Ternary(..)
        | Expr::Sext(..)
        | Expr::Cast(..) => false,
    }
}

/// Reads `v` as the scalar lane `ty` names.
///
/// A wider value contributes its low bits. That is not a rounding
/// conversion. A narrower load or constant contributes those bits with
/// zeros above, which is what `movss` from memory leaves; a computed
/// single whose bits above the lane were not cleared is left as the
/// number, because a legacy scalar operation keeps whatever was there.
/// The same width is unchanged. The mask stays in the expression even
/// when the value already fits it, so the cast keeps the bits instead of
/// converting the number. A sign or magnitude mask the register still
/// holds is that mask's lane ([`lane_of_mask`]), not a zero-extend of a
/// negation the broadcast form is wider than.
///
/// # Arguments
///
/// * `v` - The operand.
/// * `ty` - The lane the instruction reads, [`Ty::F32`] or [`Ty::F64`].
fn scalar_lane(v: Expr, ty: Ty) -> Expr {
    if let Some(masked) = lane_of_mask(&v, ty) {
        return masked;
    }
    let want = ty.bits();
    let Some(have) = float_lane(&v) else {
        return float_bits(v, ty);
    };
    if have == want || !matches!(have, 32 | 64) || !matches!(want, 32 | 64) {
        return float_bits(v, ty);
    }
    if have < want && !lane_zeros_above(&v) {
        return float_bits(v, ty);
    }
    let kept = have.min(want);
    let bits = Expr::Bin(Op::And, Box::new(v), Box::new(Expr::Const(mask_bits(kept))));
    Expr::Cast(Box::new(bits), ty)
}

/// A `movss` or `movsd` into memory, as the bytes it copies.
///
/// The same width is that float. A wider float contributes its low bits,
/// which is not a rounding conversion. A narrower float whose bits above
/// the lane are zero contributes that encoding; storing the number would
/// be a different value. Those bits are an unsigned integer, so the store
/// does not convert them. A narrower float whose bits above the lane this
/// function did not clear stays the number: the bytes above it are not in
/// the value. A sign or magnitude mask is the bytes the mask left
/// ([`moved_lane_mask`]): a 32-bit store of the mask is still the negation or
/// `fabs`, a 32-bit store after a scalar single is that single's lane, and a
/// wider store keeps a sign bit the mask set above the lane.
///
/// # Arguments
///
/// * `v` - The register's value.
/// * `bits` - The store's width, 32 or 64.
fn scalar_moved(v: Expr, bits: u8) -> (Ty, Expr) {
    if let Some(masked) = moved_lane_mask(&v, bits) {
        return masked;
    }
    let (float, integer) = if bits <= 32 {
        (Ty::F32, Ty::U32)
    } else {
        (Ty::F64, Ty::U64)
    };
    let Some(have) = float_lane(&v) else {
        return (float, v);
    };
    if have == bits {
        return (float, v);
    }
    if have > bits || lane_zeros_above(&v) {
        let kept = have.min(bits);
        let masked = Expr::Bin(Op::And, Box::new(v), Box::new(Expr::Const(mask_bits(kept))));
        return (integer, masked);
    }
    (float, v)
}

/// Most instructions before the `ret` or `jmp` of a callee read in place of
/// its call.
const IN_PLACE_MAX: usize = 4;

/// Tells whether an instruction only loads a general register.
///
/// The register is not the stack pointer, and the load is a move, an
/// extension or an address from a register, a constant or memory off the
/// stack, or a register zeroed by `xor`.
///
/// # Arguments
///
/// * `i` - The instruction.
fn is_register_load(i: &Instruction) -> bool {
    let to_register = i.op_count() == 2
        && i.op0_kind() == OpKind::Register
        && i.op0_register().is_gpr()
        && i.op0_register().full_register() != Register::RSP;
    if !to_register {
        return false;
    }
    let off_stack = |i: &Instruction| {
        !matches!(
            i.memory_base().full_register(),
            Register::RSP | Register::RBP
        )
    };
    match i.mnemonic() {
        Mnemonic::Mov | Mnemonic::Movzx | Mnemonic::Movsx | Mnemonic::Movsxd | Mnemonic::Lea => {
            match i.op1_kind() {
                OpKind::Register => i.op1_register().is_gpr(),
                OpKind::Memory => off_stack(i),
                kind => matches!(
                    kind,
                    OpKind::Immediate8
                        | OpKind::Immediate16
                        | OpKind::Immediate32
                        | OpKind::Immediate64
                        | OpKind::Immediate8to32
                        | OpKind::Immediate8to64
                        | OpKind::Immediate32to64
                ),
            }
        }
        Mnemonic::Xor => i.op1_kind() == OpKind::Register && i.op1_register() == i.op0_register(),
        _ => false,
    }
}

/// Most significant decimal digits a float constant may need before an
/// integer store of its bits stays an integer.
const FLOAT_DIGITS_MAX: usize = 5;

/// Fewest set bits in a stored constant read as a float: `0x40000000` is
/// `2.0f` and also bit 30, and a flag word is the likelier of the two.
const FLOAT_BITS_MIN: u32 = 3;

/// Reads an integer constant stored to memory as the float it spells, when
/// it can only be one.
///
/// `mov dword [rax+0x100], 0x3f800000` is `x = 1.0f` compiled: the store
/// has no float instruction to type it. The constant is a float when its
/// shortest decimal form is short (`1`, `0.001`, `-7.5`), its magnitude is
/// between a thousandth and a million, and it sets at least
/// [`FLOAT_BITS_MIN`] bits; a four-character code, a hash or an id has a
/// long decimal form or a magnitude far outside that range. Eight-byte
/// stores are read as `double` the same way.
///
/// # Arguments
///
/// * `ty` - The store's width.
/// * `v` - The stored value.
///
/// # Returns
///
/// The float type and constant, or `None` to keep the integer store.
fn float_store(ty: Ty, v: &Expr) -> Option<(Ty, Expr)> {
    let &Expr::Const(bits) = v else {
        return None;
    };
    if bits.count_ones() < FLOAT_BITS_MIN {
        return None;
    }
    let (value, text) = match ty {
        Ty::U32 => {
            let f = f32::from_bits(u32::try_from(bits).ok()?);
            (f64::from(f), format!("{f:e}"))
        }
        Ty::U64 => {
            let f = f64::from_bits(bits);
            (f, format!("{f:e}"))
        }
        Ty::U8 | Ty::U16 | Ty::U128 | Ty::F32 | Ty::F64 => return None,
    };
    let magnitude = value.abs();
    if !value.is_finite() || !(1e-3..=1e6).contains(&magnitude) {
        return None;
    }
    let mantissa = text.split('e').next().unwrap_or("");
    let digits = mantissa.chars().filter(char::is_ascii_digit).count();
    let fty = if ty == Ty::U32 { Ty::F32 } else { Ty::F64 };
    (digits <= FLOAT_DIGITS_MAX).then_some((fty, Expr::FConst(bits, fty)))
}

/// Returns how many arguments a variadic function fixes, from its prologue.
///
/// A function taking a variable list stores every argument register from
/// the first variable one on into its home slot and takes that slot's
/// address for `va_start`, or on System V into its register save area
/// ([`Homes::fixed`]).
///
/// # Arguments
///
/// * `program` - Its format selects the convention.
/// * `bitness` - 32 or 64; only the 64-bit conventions keep their
///   argument registers so.
/// * `prologue` - The function's first instructions, up to its first call.
///
/// # Returns
///
/// How many arguments are fixed, or `None` when the function takes no
/// variable list.
pub(crate) fn vararg_fixed<'i>(
    program: &Program,
    bitness: u32,
    prologue: impl IntoIterator<Item = &'i Instruction>,
) -> Option<usize> {
    let mut homes = Homes::new(bitness, conv(program, bitness));
    for i in prologue {
        homes.step(i, bitness);
    }
    homes.fixed()
}

#[cfg(test)]
mod tests {
    use super::slot_method;
    use crate::analysis::decompile::decompile;
    use crate::analysis::{Analysis, Overlay};
    use crate::program::{Arch, Program};

    /// A stack address a 32-bit call takes in a register escapes to the
    /// callee, as one it takes on the stack does.
    ///
    /// `lea ecx, [ebp-8]; call f` hands `f` the slot (a `__thiscall` on
    /// a local object): the store to the slot before the call is written
    /// out for `f` to read, and the slot is read again after it, so the
    /// branch on it is not folded on the value stored before the call, which
    /// left the call's successor out of the text as unreachable.
    ///
    /// # Panics
    ///
    /// When the text folds the branch.
    #[test]
    fn a_32_bit_register_argument_lets_its_stack_address_escape() {
        let mut code = vec![
            0x55, // ASM: push ebp
            0x8b, 0xec, // ASM: mov ebp, esp
            0x83, 0xec, 0x08, // ASM: sub esp, 8
            0x83, 0x65, 0xf8, 0x00, // ASM: and dword [ebp-8], 0
            0x8d, 0x4d, 0xf8, // ASM: lea ecx, [ebp-8]
            0xe8, 0xee, 0x00, 0x00, 0x00, // ASM: call 0x1100
            0x83, 0x7d, 0xf8, 0x00, // ASM: cmp dword [ebp-8], 0
            0x7e, 0x05, // ASM: jle 0x101d
            0xe8, 0xf3, 0x00, 0x00, 0x00, // ASM: call 0x1110
            0xc9, // ASM: leave
            0xc3, // ASM: ret
        ];
        code.resize(0x100, 0xcc);
        code.extend([
            0xc7, 0x01, 0x05, 0x00, 0x00, 0x00, // ASM: mov dword [ecx], 5
            0xc3, // ASM: ret
        ]);
        code.resize(0x110, 0xcc);
        code.extend([
            0xb8, 0x01, 0x00, 0x00, 0x00, // ASM: mov eax, 1
            0xc3, // ASM: ret
        ]);
        let mut p = Program::raw_x64(&code);
        p.arch = Arch::X86;
        p.is_64 = false;
        let a = Analysis::compute(&p);
        let text = decompile(&p, &a, &Overlay::default(), 0x1000).expect("decompiles");
        assert!(text.contains("sub_1110()"), "{text}");
        assert!(!text.contains("unreachable"), "{text}");
    }

    /// A numbered slot name drops its number at a call; anything else stays.
    ///
    /// # Panics
    ///
    /// When a name is spelled wrongly.
    #[test]
    fn a_numbered_slot_name_calls_the_slot() {
        assert_eq!(slot_method("vfunc_3_627"), "vfunc_3");
        assert_eq!(slot_method("vfunc_12"), "vfunc_12");
        assert_eq!(slot_method("vfunc_3_x"), "vfunc_3_x");
        assert_eq!(slot_method("GetId_2"), "GetId_2");
    }
}
