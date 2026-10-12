//! The text checked against the binary: each block's statements, as the
//! emission recorded them, replayed under the lifter's own witness.
//!
//! [`verify`](super::verify) checks the lifter's environment against the
//! emulator; this checks what the text says. At every block the lifter
//! knows how the machine's state and the text's relate (the
//! dataflow's IN environment): a location with a pending value `e` holds
//! `e` evaluated over the text's variables, any other holds the text
//! variable of its own name, and an equality branch into the block fixes
//! one variable. A text state is drawn, the machine state built from it
//! through that relation, the block run on the emulator and its recorded
//! statements ([`Effect`]) replayed on the text state. Then the
//! relation must hold again at every successor (each register it reads,
//! each stack slot the text names, memory off the frame, the stack
//! pointer), the branch must go the machine's way, a call must pass what
//! the machine passes, and a return must hand back what it hands back: an
//! inductive check, block by block and edge by edge, that needs no
//! compiler and names the statement's instruction when it fails.
//!
//! Each block is tried from three states seeded by the seed, its address
//! and the trial: one random, two drawn mostly from the block's own
//! constants and the values around them (one either side, zero, the
//! signed and unsigned limits), so an off-by-one condition is taken both
//! ways. Scalar floats evaluate at the width their expressions carry, on
//! the one float model the verifier also uses; the `xmm` registers are
//! seeded the way the general ones are, so a float block and its
//! successors compare, and a block of packed integer operations has its
//! whole lanes drawn, held and compared, the emulator's lane arithmetic
//! against the text's own. What the replay cannot evaluate (a vector
//! form outside the packed model, a TLS slot, a float through a temporary
//! or converted from an integer, memory a store at an unknown address may
//! have changed, an access past the top of the address space) is counted,
//! not compared; blocks outside the checked subset (an x87 one, a form
//! the emulator or the lifter leaves alone), blocks with a statement no
//! effect models or a call the text leaves out, and blocks whose flags
//! reach a condition the text writes over unknown flags (their compare has
//! no statement), are not checked. What
//! the text leaves out on
//! purpose makes no claim: a register's save, a push that only makes room,
//! the try level of a registered exception handler, a store pending at a
//! block's start that the successor overwrites first. C variables do not
//! share bytes, so a slot read after the text wrote some of its bytes
//! under another slot's name is not compared either. A value that differs
//! only above its low 32 bits (a 32-bit result kept whole in a 64-bit
//! variable) is reported apart, as the known lane roughness. A
//! pass says the text agreed on the states tried, not that it is right; the
//! statements it checks are the ones the emission wrote, before the text
//! passes rewrote them.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;

use crate::isa::x86::{
    FlowControl, Instruction, InstructionInfoFactory, Mnemonic, OpKind, Register,
};

use super::expr::{Cond, Expr, Flags, Key, TLS_BASE, Ty, UnOp, a64_code, fold, known_bits, unary};
use super::lift::{
    ArgAt, Callee, Conv, Effect, EffectKind, Env, Routine, SLOT_BYTES_MAX, Shown, try_level_store,
};
use super::liveness::Live;
use super::verify::{
    EVAL_DEPTH, FRAME_SPAN, GOLDEN, REGION_MAX, REGS, REGS_32, Rng, STACK_WORDS, XMMS, agree,
    aligns_stack, convert_float, float_arith, float_cc, float_of, float_to_int, float_un, low,
    sext, word,
};
use super::{decompile_with, table_target};
use crate::analysis::decompiled_witnessed;
use crate::analysis::{Analysis, BasicBlock, Overlay, striped_with};
use crate::emulate::{Emulator, Stop, fill_byte};
use crate::fxmap::{FxHashMap, FxHashSet};
use crate::num::{from_usize, lo8};
use crate::program::Program;

/// States each block is tried from.
const TRIALS: u64 = 3;
/// States drawn again for a block where the branch into it ruled one out.
const RULED_OUT_RETRIES: u64 = 9;
/// Why a state is not tried: the branch into the block rules it out.
const RULED_OUT: &str = "a state the branch into the block rules out";
/// Why a block is not checked: a float or vector instruction outside the
/// checked subset ([`outside_subset`]).
const OUTSIDE_FLOAT: &str = "an instruction outside the checked subset";
/// Why a block is not checked: a call in it renders fewer stack words than
/// its callee reads ([`Call::short`](super::lift::Call::short)).
const SHORT_CALL: &str = "a call the text passes fewer words than its callee reads";
/// Why a block is not checked: a declaration the code contradicts.
///
/// A call in it follows one ([`Call::contradicted`](super::lift::Call::contradicted)),
/// or it returns from a function following a stated prototype the binary
/// contradicts ([`Witness::stated_contradicted`]).
const CONTRADICTED: &str = "a declaration the code contradicts";
/// Why a block is not checked: it returns nothing where the function's
/// callers read a result ([`Witness::result_read`]).
const BARE_RETURN: &str = "a return of nothing the callers read a result from";
/// Blocks that only jump on followed back to the branch a block runs under.
const GUARD_JUMPS: usize = 4;
/// Blocks followed forward from one that sets flags to the block reading
/// them ([`Function::flags_lost`]).
const FLAG_HOPS: usize = 4;
/// Fewest functions worth a thread of their own.
const PAR_MIN: usize = 16;
/// Why a block is not tried in an answer's check: the blocks before it
/// spent the budget ([`ANSWER_BLOCKS`]).
const OVER_BUDGET: &str = "beyond the answer's block budget";
/// Blocks an answer's check tries states for, in address order.
///
/// The budget keeps the check inside an answer's time, a count rather than
/// a clock so the same answer says the same thing. At 256 the check adds
/// 29-31 ms at the 99th percentile to a `decompile` answer on `kernel32`,
/// `d3dx9_43` and a large game client, and checks 78-90% of their blocks.
pub const ANSWER_BLOCKS: usize = 256;
/// The seed of an answer's check.
pub const ANSWER_SEED: u64 = 1;
/// Disagreements a report lists.
pub const LISTED_MAX: usize = 400;
/// Instructions of disagreeing statements an answer's header names.
const DISAGREE_SHOWN: usize = 4;

/// What the lifter knew about a function's blocks when it wrote the text:
/// the relation between machine and text that [`replay`] checks the text
/// with.
pub(super) struct Witness {
    /// Each block's instructions.
    pub(super) code: Code,
    /// Each block's IN environment.
    pub(super) ins: Vec<Env>,
    /// The blocks the dataflow ran.
    pub(super) processed: Vec<bool>,
    /// The equality each block runs under, if any.
    pub(super) assumes: Vec<Option<(Key, u64)>>,
    /// Which registers and slots each block reads.
    pub(super) live: Live,
    /// The blocks the text writes.
    pub(super) emitted: Vec<bool>,
    /// The blocks that read flags another block set.
    pub(super) flag_readers: Vec<bool>,
    /// The calling convention.
    pub(super) conv: &'static Conv,
    /// The width in bits of the value a `return` hands back.
    pub(super) ret_bits: u8,
    /// The result comes back in a floating-point register.
    pub(super) ret_float: bool,
    /// That register is `xmm0`, not the x87 stack's top.
    pub(super) ret_xmm: bool,
    /// The function's callers read what it hands back: some caller reads
    /// the return register after the call, or the result is a float.
    pub(super) result_read: bool,
    /// The function follows a stated prototype the binary contradicts
    /// ([`super::declared::contradictions`]): what its returns hand back
    /// is the prototype's, which nothing compares with what the callers
    /// read.
    pub(super) stated_contradicted: bool,
    /// Callees that only jump through a register, with the register: a
    /// call to one goes where the register points.
    pub(super) dispatches: BTreeMap<u64, Register>,
    /// The stack slots each block stores a value to, by offset from the
    /// entry stack pointer, each with the widest store in bits.
    pub(super) defs: Vec<BTreeMap<i64, u8>>,
    /// The function registers a structured exception handler, whose
    /// try-level stores the text leaves out ([`try_level_store`]).
    pub(super) seh_frame: bool,
    /// The width in bits each stack slot the text declares is declared
    /// with: what the slot's name reads.
    pub(super) slot_bits: BTreeMap<i64, u8>,
    /// The declaration type of each vector register the text names a
    /// float: the width its own variable reads.
    pub(super) reg_ty: BTreeMap<Key, Ty>,
}

impl std::fmt::Debug for Witness {
    /// Writes how many blocks the witness covers.
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let blocks = match &self.code {
            Code::X86(code) => code.len(),
        };
        f.debug_struct("Witness")
            .field("blocks", &blocks)
            .finish_non_exhaustive()
    }
}

/// A function's blocks in the instruction set it is written in, as the
/// lifter decoded them ([`super::arch::Lifter::witness`]).
pub(super) enum Code {
    /// x86 or x86-64 instructions, per block.
    X86(Vec<Vec<Instruction>>),
}

/// What a statement or a block's end claims, as compared with the machine.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Claim {
    /// A register a successor reads holds what the text says.
    Register,
    /// A stack slot the text names holds what the text says.
    Slot,
    /// Memory off the frame holds what the text stored.
    Memory,
    /// The stack pointer is where the successor expects it.
    StackPointer,
    /// The branch goes the machine's way.
    Branch,
    /// A call passes what the machine passes.
    Argument,
    /// A call or jump through a pointer goes where the machine goes.
    Target,
    /// A `return` hands back what the machine does.
    Return,
    /// A `switch` takes the arm the machine jumps to.
    Switch,
    /// A variable a successor reads as narrow fits its width.
    Narrow,
}

impl Claim {
    /// Every kind, in report order.
    const ALL: [Self; 10] = [
        Self::Register,
        Self::Slot,
        Self::Memory,
        Self::StackPointer,
        Self::Branch,
        Self::Argument,
        Self::Target,
        Self::Return,
        Self::Switch,
        Self::Narrow,
    ];
}

impl std::fmt::Display for Claim {
    /// Writes the kind's name as a report row spells it.
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            Self::Register => "register",
            Self::Slot => "slot",
            Self::Memory => "memory",
            Self::StackPointer => "stack pointer",
            Self::Branch => "branch",
            Self::Argument => "argument",
            Self::Target => "target",
            Self::Return => "return",
            Self::Switch => "switch",
            Self::Narrow => "narrow",
        })
    }
}

/// One claim of the text the machine does not bear out.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Disagreement {
    /// The function's entry.
    pub function: u64,
    /// The block's start.
    pub block: u64,
    /// The instruction of the statement that makes the claim; for the
    /// state at a block's end, its last instruction.
    pub at: u64,
    /// What kind of claim.
    pub claim: Claim,
    /// Which one: a register, a slot as an offset from the entry stack
    /// pointer, an address, a successor, an argument's place.
    pub place: String,
    /// What the text says, in the width compared.
    pub text: u64,
    /// What the machine holds, in the same width.
    pub machine: u64,
    /// The width compared, in bits.
    pub bits: u8,
    /// A roughness of the lane model rather than a wrong value:
    /// only bits above the low 32 differ (a 32-bit value the text keeps
    /// whole in a 64-bit variable), or a successor's claim that a variable
    /// is narrow fails where the text reads it at no narrower width.
    pub lane: bool,
    /// The text's expression.
    pub expr: String,
}

/// What a replay found.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Replayed {
    /// Functions visited.
    pub functions: usize,
    /// Blocks visited.
    pub blocks: usize,
    /// Blocks compared from at least one state.
    pub checked: usize,
    /// States compared, over all blocks.
    pub trials: usize,
    /// Blocks not compared, by reason.
    pub skipped: BTreeMap<&'static str, usize>,
    /// Claims compared, by kind.
    pub compared: BTreeMap<Claim, usize>,
    /// Claims whose text side the replay cannot evaluate, by kind.
    pub unreadable: BTreeMap<Claim, usize>,
    /// The disagreements, in function, block and trial order.
    pub disagreements: Vec<Disagreement>,
}

impl Replayed {
    /// Adds another part's findings to these, after them.
    ///
    /// # Arguments
    ///
    /// * `part` - What one function or thread found.
    pub fn merge(&mut self, part: Self) {
        self.functions += part.functions;
        self.blocks += part.blocks;
        self.checked += part.checked;
        self.trials += part.trials;
        for (k, n) in part.skipped {
            *self.skipped.entry(k).or_default() += n;
        }
        for (k, n) in part.compared {
            *self.compared.entry(k).or_default() += n;
        }
        for (k, n) in part.unreadable {
            *self.unreadable.entry(k).or_default() += n;
        }
        self.disagreements.extend(part.disagreements);
    }

    /// The disagreements that are wrong values, not lane roughness.
    #[must_use]
    pub fn wrong(&self) -> Vec<&Disagreement> {
        self.disagreements.iter().filter(|d| !d.lane).collect()
    }
}

/// Replays the text of some functions against the emulator, a stripe of
/// them per core.
///
/// # Arguments
///
/// * `program` - The image.
/// * `analysis` - Its functions.
/// * `entries` - The functions to check.
/// * `seed` - The states' seed; the same seed checks the same way.
///
/// # Returns
///
/// What was compared and every disagreement, in the entries' order.
#[must_use]
pub fn replay(program: &Program, analysis: &Analysis, entries: &[u64], seed: u64) -> Replayed {
    let parts = striped_with(
        entries,
        PAR_MIN,
        || Emulator::new(program, 0),
        |template, &entry| {
            template
                .as_ref()
                .map(|t| replay_one(program, analysis, t, entry, seed))
        },
    );
    let mut out = Replayed::default();
    for part in parts.into_iter().flatten().flatten() {
        out.merge(part);
    }
    out
}

/// Replays one function's text against the emulator.
///
/// # Arguments
///
/// * `program` - The image.
/// * `analysis` - Its functions.
/// * `entry` - The function's entry.
/// * `seed` - The states' seed.
///
/// # Returns
///
/// What was compared and every disagreement; nothing when the image has
/// no emulator.
#[must_use]
pub fn replay_function(program: &Program, analysis: &Analysis, entry: u64, seed: u64) -> Replayed {
    Emulator::new(program, 0)
        .map(|t| replay_one(program, analysis, &t, entry, seed))
        .unwrap_or_default()
}

/// [`replay_function`] over a template emulator a thread keeps.
///
/// # Arguments
///
/// * `program` - The image.
/// * `analysis` - Its functions.
/// * `template` - The image's emulator before any run, cloned per state.
/// * `entry` - The function's entry.
/// * `seed` - The states' seed.
fn replay_one(
    program: &Program,
    analysis: &Analysis,
    template: &Emulator<'_>,
    entry: u64,
    seed: u64,
) -> Replayed {
    let Some(f) = analysis.function(entry) else {
        return Replayed::default();
    };
    let overlay = Overlay::default();
    let Some(d) = decompile_with(program, analysis, &overlay, entry, true, &[], true) else {
        return Replayed::default();
    };
    let Some(w) = d.take_witness() else {
        return Replayed::default();
    };
    let effects: Vec<Vec<Effect>> = f
        .blocks
        .iter()
        .enumerate()
        .map(|(i, b)| d.effects.block(i, b.start).unwrap_or_default())
        .collect();
    replay_effects(
        program,
        analysis,
        template,
        entry,
        seed,
        (&w, &d.live.succs),
        &effects,
        usize::MAX,
    )
}

/// Checks the statements of one function's answer against the binary, as
/// [`replay_function`] does, under the answer's names and within
/// [`ANSWER_BLOCKS`].
///
/// # Arguments
///
/// * `program` - The image.
/// * `analysis` - Its functions.
/// * `overlay` - The names the answer is decompiled under.
/// * `entry` - The function's entry.
///
/// # Returns
///
/// What was checked, `None` when the function does not decompile or the
/// image has no emulator.
pub(crate) fn check_answer(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    entry: u64,
) -> Option<TextCheck> {
    let f = analysis.function(entry)?;
    let template = Emulator::new(program, 0)?;
    // PERF: the text the answer shows comes from the memo; built here first,
    // it keeps the lifter's witness for this check to take, so the answer
    // pays for one decompilation. A text someone else memoized first kept
    // none, and the check decompiles again for it: the same statements.
    let shared = decompiled_witnessed(program, analysis, overlay, overlay.fingerprint(), entry);
    let fresh;
    let (d, w) = match shared.as_ref().as_ref().map(|d| (d, d.take_witness())) {
        Some((d, Some(w))) => (d, w),
        _ => {
            fresh = decompile_with(program, analysis, overlay, entry, true, &[], true)?;
            let w = fresh.take_witness()?;
            (&fresh, w)
        }
    };
    let effects: Vec<Vec<Effect>> = f
        .blocks
        .iter()
        .enumerate()
        .map(|(i, b)| d.effects.block(i, b.start).unwrap_or_default())
        .collect();
    let r = replay_effects(
        program,
        analysis,
        &template,
        entry,
        ANSWER_SEED,
        (&w, &d.live.succs),
        &effects,
        ANSWER_BLOCKS,
    );
    (r.functions == 1).then(|| TextCheck::of(&r))
}

/// What the check of one function's answer found: the header line the
/// `decompile` tool prints.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct TextCheck {
    /// The function's blocks.
    pub blocks: usize,
    /// Blocks compared from at least one state.
    pub checked: usize,
    /// Blocks not compared, by what kept them out, most first.
    pub unchecked: Vec<(&'static str, usize)>,
    /// The instructions of the statements the machine does not bear out,
    /// lane roughness aside, in address order.
    pub disagree: Vec<u64>,
}

impl TextCheck {
    /// Sums a replay up.
    ///
    /// # Arguments
    ///
    /// * `r` - One function's replay.
    fn of(r: &Replayed) -> Self {
        let mut why: BTreeMap<&'static str, usize> = BTreeMap::new();
        for (reason, n) in &r.skipped {
            *why.entry(unchecked_label(reason)).or_default() += n;
        }
        let mut unchecked: Vec<(&'static str, usize)> = why.into_iter().collect();
        unchecked.sort_by(|a, b| b.1.cmp(&a.1).then(a.0.cmp(b.0)));
        let mut disagree: Vec<u64> = r.wrong().iter().map(|d| d.at).collect();
        disagree.sort_unstable();
        disagree.dedup();
        Self {
            blocks: r.blocks,
            checked: r.checked,
            unchecked,
            disagree,
        }
    }

    /// The bytes the result holds, which the memo keeping it counts.
    #[must_use]
    pub fn bytes(&self) -> usize {
        size_of::<Self>()
            + self.unchecked.capacity() * size_of::<(&'static str, usize)>()
            + self.disagree.capacity() * size_of::<u64>()
    }

    /// The header line: what of the answer was checked against the binary,
    /// what the binary contradicts, and what was not checked.
    ///
    /// Checked means the statements as the lifter emitted them were
    /// replayed from [`TRIALS`] states per block (one random, the others
    /// drawn from the block's own constants and their neighbors) and
    /// compared with the emulator. A statement the machine does not bear
    /// out is named by its instruction, the first [`DISAGREE_SHOWN`] of
    /// them, so a block that was compared and found wrong never reads as
    /// agreement; the blocks left out are counted by why. What a statement
    /// computes is checked, not how its C is spelled (a cast that makes C's
    /// `>>` the signed one, a constant written as a literal), and the text
    /// passes after the emission are not checked either, which the line
    /// says too. One line on every answer costs tokens, so it is terse:
    /// `// checked vs binary: statements as emitted, 41/44 blocks x3
    /// states; disagree at 0x401a2c; unchecked: 2 float/vector, 1 over
    /// budget, C spelling, later text passes`.
    #[must_use]
    pub fn header(&self) -> String {
        let mut out = format!(
            "// checked vs binary: statements as emitted, {}/{} blocks x{TRIALS} states; ",
            self.checked, self.blocks
        );
        if !self.disagree.is_empty() {
            let shown: Vec<String> = self
                .disagree
                .iter()
                .take(DISAGREE_SHOWN)
                .map(|a| format!("{a:#x}"))
                .collect();
            let _ = write!(out, "disagree at {}", shown.join(", "));
            let more = self.disagree.len().saturating_sub(DISAGREE_SHOWN);
            if more > 0 {
                let _ = write!(out, " (+{more} more)");
            }
            out.push_str("; ");
        }
        out.push_str("unchecked: ");
        for (label, n) in &self.unchecked {
            let _ = write!(out, "{n} {label}, ");
        }
        out.push_str("C spelling, later text passes");
        out
    }
}

/// The few words the header line gives a reason a block was not checked.
///
/// # Arguments
///
/// * `reason` - Why the replay did not compare the block.
fn unchecked_label(reason: &str) -> &'static str {
    match reason {
        "not in the text" => "not in text",
        OUTSIDE_FLOAT => "float/vector",
        "a read or write through the thread block" => "fs/gs access",
        OVER_BUDGET => "over budget",
        "a call the text leaves out or reads in place" => "call left out",
        SHORT_CALL => "call args dropped",
        CONTRADICTED => "declaration contradicted",
        BARE_RETURN => "result dropped",
        "a statement no effect models"
        | "an instruction the emulator does not model"
        | "an instruction outside every checked form"
        | "a trap or a branch with no model" => "unmodeled",
        "flags set in another block" => "flags across blocks",
        "the stack pointer unknown at its start" | "a frame alignment" => "stack unknown",
        _ => "other",
    }
}

/// Replays a decompiled function's effects against the emulator.
///
/// # Arguments
///
/// * `program` - The image.
/// * `analysis` - Its functions.
/// * `template` - The image's emulator before any run, cloned per state.
/// * `entry` - The function's entry.
/// * `seed` - The states' seed.
/// * `witnessed` - What the lifter knew when it wrote the statements, and
///   the successors of each block in the graph the text was written for.
/// * `effects` - Each block's effects, by block index.
/// * `budget` - Blocks to try states for, in address order; the rest are
///   not checked.
#[expect(
    clippy::too_many_arguments,
    reason = "one function's facts, threaded through"
)]
fn replay_effects(
    program: &Program,
    analysis: &Analysis,
    template: &Emulator<'_>,
    entry: u64,
    seed: u64,
    witnessed: (&Witness, &[Vec<usize>]),
    effects: &[Vec<Effect>],
    budget: usize,
) -> Replayed {
    let mut out = Replayed::default();
    let (w, succs) = witnessed;
    let (Some(f), Some(bitness)) = (analysis.function(entry), program.arch.bitness()) else {
        return out;
    };
    let Code::X86(code) = &w.code;
    out.functions = 1;
    let named = named_slots(effects, if bitness == 32 { 4 } else { 8 });
    let function = Function {
        analysis,
        template,
        entry,
        seed,
        w,
        code,
        succs,
        effects,
        named: &named,
        regs: if bitness == 32 { &REGS_32 } else { &REGS },
        width: if bitness == 32 { 32 } else { 64 },
    };
    let mut room = budget;
    for (b, block) in f.blocks.iter().enumerate() {
        out.blocks += 1;
        match function.check(b, block, &mut room, &mut out) {
            Ok(()) => out.checked += 1,
            Err(why) => *out.skipped.entry(why).or_default() += 1,
        }
    }
    out
}

/// The stack slots the text's statements name anywhere in a function, with
/// the most bytes they read or write at each.
///
/// Those are the slots whose bytes the check compares at a block's end: a
/// slot no statement names (a register's save, read back only by a restore
/// nothing prints) is no claim of the text.
///
/// # Arguments
///
/// * `effects` - Every block's effects.
/// * `word` - Bytes in a register, what a slot named whole holds.
fn named_slots(effects: &[Vec<Effect>], word: u64) -> BTreeMap<i64, u64> {
    let mut out: BTreeMap<i64, u64> = BTreeMap::new();
    let mut note = |o: i64, bytes: u64| {
        let e = out.entry(o).or_insert(bytes);
        *e = (*e).max(bytes);
    };
    let mut seen: Vec<&Expr> = Vec::new();
    for e in effects.iter().flatten() {
        match &e.kind {
            EffectKind::Assign(k, v, bits) => {
                if let Key::Slot(o) = k {
                    note(*o, u64::from(*bits / 8).max(1));
                }
                seen.push(v);
            }
            EffectKind::Store(s) => {
                seen.push(&s.0);
                seen.push(&s.2);
            }
            EffectKind::Call(c) => {
                if let Callee::Through(t) = &c.callee {
                    seen.push(t);
                }
                seen.extend(c.args.iter().map(|(_, e)| e));
            }
            EffectKind::Return(Some(v)) | EffectKind::Switch(v) | EffectKind::Jump(v) => {
                seen.push(v);
            }
            EffectKind::Branch(c) => cond_exprs(c, &mut seen),
            EffectKind::Return(None) | EffectKind::Unmodeled => {}
        }
    }
    let mut stack = seen;
    while let Some(e) = stack.pop() {
        match e {
            Expr::Deref(a, ty) => {
                if let Expr::Sp(o) = **a {
                    note(o, u64::from(ty.bits() / 8).max(1));
                }
                stack.push(a);
            }
            Expr::Var(Key::Slot(o)) => note(*o, word),
            Expr::Bin(_, l, r) => {
                stack.push(l);
                stack.push(r);
            }
            Expr::Un(_, x) | Expr::Sext(x, _) | Expr::Cast(x, _) => stack.push(x),
            Expr::Cond(c) => cond_exprs(c, &mut stack),
            Expr::Ternary(c, a, b) => {
                cond_exprs(c, &mut stack);
                stack.push(a);
                stack.push(b);
            }
            Expr::Call(_, args) => stack.extend(args.iter()),
            Expr::Const(_) | Expr::Var(_) | Expr::Str(_) | Expr::Sp(_) | Expr::FConst(..) => {}
        }
    }
    out
}

/// The stores of a block whose bytes cover the frame byte at `off`, by
/// their offsets.
///
/// # Arguments
///
/// * `defs` - The block's stores, each with its widest width in bits.
/// * `off` - The byte's frame offset.
fn covering(defs: &BTreeMap<i64, u8>, off: i64) -> impl Iterator<Item = i64> + '_ {
    defs.range(off.saturating_sub(SLOT_BYTES_MAX - 1)..=off)
        .filter(move |&(&o, &bits)| off < o.saturating_add(i64::from(bits / 8).max(1)))
        .map(|(&o, _)| o)
}

/// Tells whether a block's statements write the frame byte at `off`
/// before any of them may read it.
///
/// A read of a slot or of a computed frame address that may cover the
/// byte, a call, an unmodeled instruction or a return before the write
/// says no.
///
/// # Arguments
///
/// * `effects` - The block's statements.
/// * `off` - The byte's frame offset.
fn overwritten_first(effects: &[Effect], off: i64) -> bool {
    let covers = |o: i64, n: u64| off >= o && off.abs_diff(o) < n;
    for e in effects {
        let mut reads: Vec<&Expr> = Vec::new();
        let mut wrote = false;
        match &e.kind {
            EffectKind::Assign(k, v, bits) => {
                reads.push(v);
                if let Key::Slot(o) = k {
                    wrote = covers(*o, u64::from(*bits / 8).max(1));
                }
            }
            EffectKind::Store(st) => {
                reads.push(&st.0);
                reads.push(&st.2);
            }
            EffectKind::Branch(c) => cond_exprs(c, &mut reads),
            EffectKind::Switch(v) | EffectKind::Jump(v) | EffectKind::Return(Some(v)) => {
                reads.push(v);
            }
            EffectKind::Return(None) | EffectKind::Call(_) | EffectKind::Unmodeled => {
                return false;
            }
        }
        while let Some(r) = reads.pop() {
            match r {
                Expr::Deref(a, ty) => {
                    if let Expr::Sp(o) = **a {
                        if covers(o, u64::from(ty.bits() / 8).max(1)) {
                            return false;
                        }
                    } else if frame_base(a).is_some() {
                        return false;
                    }
                    reads.push(a);
                }
                Expr::Var(Key::Slot(o)) => {
                    if covers(*o, 8) {
                        return false;
                    }
                }
                Expr::Bin(_, l, rr) => {
                    reads.push(l);
                    reads.push(rr);
                }
                Expr::Un(_, x) | Expr::Sext(x, _) | Expr::Cast(x, _) => reads.push(x),
                Expr::Cond(c) => cond_exprs(c, &mut reads),
                Expr::Ternary(c, a, b) => {
                    cond_exprs(c, &mut reads);
                    reads.push(a);
                    reads.push(b);
                }
                Expr::Call(_, args) => reads.extend(args.iter()),
                Expr::Const(_) | Expr::Var(_) | Expr::Str(_) | Expr::Sp(_) | Expr::FConst(..) => {}
            }
        }
        if wrote {
            return true;
        }
    }
    false
}

/// The frame offset a computed address is based on: `Sp(k)` alone or plus
/// other terms, as the lifter reads it.
///
/// # Arguments
///
/// * `e` - The address.
fn frame_base(e: &Expr) -> Option<i64> {
    match e {
        Expr::Sp(k) => Some(*k),
        Expr::Bin(super::expr::Op::Add, l, r) => frame_base(l).or_else(|| frame_base(r)),
        _ => None,
    }
}

/// Pushes the operands of a condition's flags.
///
/// # Arguments
///
/// * `c` - The condition.
/// * `out` - Where they go.
fn cond_exprs<'e>(c: &'e Cond, out: &mut Vec<&'e Expr>) {
    match &c.flags {
        Flags::Cmp(a, b, _)
        | Flags::Test(a, b, _)
        | Flags::Add(a, b, _)
        | Flags::Shift(a, _, b) => {
            out.push(a);
            out.push(b);
        }
        Flags::Result(a, _) | Flags::Carry(a) | Flags::Truth(a, _) => out.push(a),
        Flags::Unknown => {}
    }
}

/// Renders a replay as a report.
///
/// A `#` summary, a line per kind of claim with what was compared, the
/// reasons blocks were not checked, then a row per disagreement, at most
/// [`LISTED_MAX`]; rows whose values differ only above the low 32 bits
/// or whose claim is a lane's say so in their `lane` column.
///
/// # Arguments
///
/// * `r` - What [`replay`] found.
#[must_use]
pub fn replay_tsv(r: &Replayed) -> String {
    let skipped: usize = r.skipped.values().sum();
    let lane = r.disagreements.iter().filter(|d| d.lane).count();
    let mut out = format!(
        "# replayed {} functions, {} blocks: {} checked from {} states, {skipped} not checked, {} disagreements ({lane} of a lane only)\n",
        r.functions,
        r.blocks,
        r.checked,
        r.trials,
        r.disagreements.len()
    );
    for claim in Claim::ALL {
        let _ = writeln!(
            out,
            "# {claim}: {} compared, {} not readable, {} disagree",
            r.compared.get(&claim).copied().unwrap_or(0),
            r.unreadable.get(&claim).copied().unwrap_or(0),
            r.disagreements
                .iter()
                .filter(|d| d.claim == claim && !d.lane)
                .count()
        );
    }
    for (reason, n) in &r.skipped {
        let _ = writeln!(out, "# not checked: {n} for {reason}");
    }
    if r.disagreements.len() > LISTED_MAX {
        let _ = writeln!(
            out,
            "# showing {LISTED_MAX} of {} disagreements",
            r.disagreements.len()
        );
    }
    out.push_str("function\tblock\tat\tclaim\tplace\ttext\tmachine\tbits\tlane\texpression\n");
    for d in r.disagreements.iter().take(LISTED_MAX) {
        let _ = writeln!(
            out,
            "{:#x}\t{:#x}\t{:#x}\t{}\t{}\t{:#x}\t{:#x}\t{}\t{}\t{}",
            d.function, d.block, d.at, d.claim, d.place, d.text, d.machine, d.bits, d.lane, d.expr
        );
    }
    out
}

/// How a block ends, which says where its run stops.
#[derive(Debug, Clone, Copy)]
enum End {
    /// A conditional branch: the run stops before it, then steps it.
    Branch(Instruction),
    /// A call, a return, or a jump (to a block, a tail call, a jump
    /// table, a computed `goto`): the run stops before it.
    Before(Instruction),
    /// Into the block at this address.
    Fall(u64),
}

impl End {
    /// How a block's instructions end.
    ///
    /// # Arguments
    ///
    /// * `code` - The block's instructions, at least one.
    ///
    /// # Errors
    ///
    /// Why the end cannot be checked: a trap.
    fn of(code: &[Instruction]) -> Result<Self, &'static str> {
        let last = *code.last().ok_or("no instructions")?;
        Ok(match last.flow_control() {
            FlowControl::ConditionalBranch
                if matches!(
                    last.op0_kind(),
                    OpKind::NearBranch16 | OpKind::NearBranch32 | OpKind::NearBranch64
                ) && last.near_branch_target() != last.ip() =>
            {
                Self::Branch(last)
            }
            FlowControl::Call
            | FlowControl::IndirectCall
            | FlowControl::Return
            | FlowControl::UnconditionalBranch
            | FlowControl::IndirectBranch => Self::Before(last),
            FlowControl::Next => Self::Fall(last.next_ip()),
            FlowControl::ConditionalBranch
            | FlowControl::Interrupt
            | FlowControl::Exception
            | FlowControl::XbeginXabortXend => return Err("a trap or a branch with no model"),
        })
    }

    /// Where the run stops.
    fn stop(self) -> u64 {
        match self {
            Self::Branch(i) | Self::Before(i) => i.ip(),
            Self::Fall(at) => at,
        }
    }

    /// The instruction the run stops before, if the block ends in one.
    fn last(self) -> Option<Instruction> {
        match self {
            Self::Branch(i) | Self::Before(i) => Some(i),
            Self::Fall(_) => None,
        }
    }
}

/// Tells whether the replay can check an instruction: general registers
/// only, no `lock`, no access through `fs` or `gs`, memory no wider than
/// a word.
///
/// # Arguments
///
/// * `i` - The instruction.
/// * `info` - Register-access facts.
fn integer(i: &Instruction, info: &mut InstructionInfoFactory) -> bool {
    let segment = |r: Register| matches!(r, Register::FS | Register::GS);
    if i.has_lock_prefix() || segment(i.segment_prefix()) {
        return false;
    }
    let memory = (0..i.op_count()).any(|n| i.op_kind(n) == OpKind::Memory);
    if memory && (i.memory_size().size() > 8 || segment(i.memory_segment())) {
        return false;
    }
    info.info(i).used_registers().iter().all(|u| {
        let r = u.register();
        r.is_gpr()
            || matches!(r, Register::RIP | Register::EIP)
            || (r.is_segment_register() && !segment(r))
    })
}

/// Tells whether the replay can check a scalar-float instruction: a move,
/// an arithmetic operation, a compare or a conversion on the low lane of
/// an `xmm` register.
///
/// Every such instruction is one the emulator models and the lifter
/// writes a statement for. Memory stays within a word and off `fs`/`gs`,
/// and no register but a general one or an `xmm` one is touched, so a
/// packed or 256-bit form, whose lanes the text does not model one by
/// one, is left out: a three-source VEX move the lifter writes no
/// statement for, and a fused multiply-add the emulator does not model,
/// are left out with it.
///
/// # Arguments
///
/// * `i` - The instruction.
/// * `info` - Register-access facts.
fn scalar_float(i: &Instruction, info: &mut InstructionInfoFactory) -> bool {
    use Mnemonic as M;
    if i.has_lock_prefix() || matches!(i.segment_prefix(), Register::FS | Register::GS) {
        return false;
    }
    let m = i.mnemonic();
    // The sign and magnitude masks a `xorps`/`andps` reads: the lifter
    // writes them as `-x` and `fabs(x)`, a 16-byte memory operand whose
    // text never reads the bytes. The register-register forms are the zero
    // fill's and the packed logic's, left to their own arms.
    let mask = matches!(m, M::Xorps | M::Xorpd | M::Andps | M::Andpd)
        && i.op_count() == 2
        && i.op0_kind() == OpKind::Register
        && i.op1_kind() == OpKind::Memory;
    if !mask
        && (0..i.op_count()).any(|n| i.op_kind(n) == OpKind::Memory)
        && (i.memory_size().size() > 8 || matches!(i.memory_segment(), Register::FS | Register::GS))
    {
        return false;
    }
    let two = i.op_count() == 2;
    let three = i.op_count() == 3;
    let reg_reg = two && i.op0_kind() == OpKind::Register && i.op1_kind() == OpKind::Register;
    let shape = match m {
        M::Movss | M::Movsd | M::Vmovss | M::Vmovsd | M::Movd | M::Movq | M::Vmovd | M::Vmovq => {
            two
        }
        M::Movaps | M::Movups | M::Movapd | M::Movupd | M::Movdqa | M::Movdqu => reg_reg,
        M::Xorps | M::Xorpd | M::Andps | M::Andpd => mask,
        M::Addss
        | M::Subss
        | M::Mulss
        | M::Divss
        | M::Minss
        | M::Maxss
        | M::Sqrtss
        | M::Addsd
        | M::Subsd
        | M::Mulsd
        | M::Divsd
        | M::Minsd
        | M::Maxsd
        | M::Sqrtsd => two,
        M::Vaddss
        | M::Vsubss
        | M::Vmulss
        | M::Vdivss
        | M::Vminss
        | M::Vmaxss
        | M::Vsqrtss
        | M::Vaddsd
        | M::Vsubsd
        | M::Vmulsd
        | M::Vdivsd
        | M::Vminsd
        | M::Vmaxsd
        | M::Vsqrtsd
        | M::Vcvtsi2ss
        | M::Vcvtsi2sd
        | M::Vcvtss2sd
        | M::Vcvtsd2ss => three,
        M::Comiss
        | M::Ucomiss
        | M::Comisd
        | M::Ucomisd
        | M::Vcomiss
        | M::Vucomiss
        | M::Vcomisd
        | M::Vucomisd
        | M::Cvtsi2ss
        | M::Cvtsi2sd
        | M::Cvtss2sd
        | M::Cvtsd2ss
        | M::Cvttss2si
        | M::Cvttsd2si
        | M::Vcvttss2si
        | M::Vcvttsd2si => two,
        _ => false,
    };
    shape
        && info.info(i).used_registers().iter().all(|u| {
            let r = u.register();
            r.is_gpr()
                || r.is_xmm()
                || matches!(r, Register::RIP | Register::EIP)
                || (r.is_segment_register() && !matches!(r, Register::FS | Register::GS))
        })
}

/// The instructions of a block that set the flags, each as its address
/// and whether it was a float compare (`comiss` and its kin), beside the
/// addresses of those that read them.
///
/// The lifter writes a float compare's condition as a `Cmp` no differently
/// from an integer one, and its operands may carry no float type (a
/// parameter's variable), so the instructions themselves are the only
/// witness of which way the condition a reader stands at reads: the
/// setter before the reader (`setcc` and `and` both follow a compare,
/// only the first reading its flags).
///
/// # Arguments
///
/// * `code` - The block's instructions.
fn flag_setters(code: &[Instruction]) -> (Vec<(u64, bool)>, Vec<u64>) {
    (
        code.iter()
            .filter(|i| i.rflags_modified() != 0)
            .map(|i| {
                (
                    i.ip(),
                    matches!(
                        i.mnemonic(),
                        Mnemonic::Comiss
                            | Mnemonic::Ucomiss
                            | Mnemonic::Comisd
                            | Mnemonic::Ucomisd
                            | Mnemonic::Vcomiss
                            | Mnemonic::Vucomiss
                            | Mnemonic::Vcomisd
                            | Mnemonic::Vucomisd
                    ),
                )
            })
            .collect(),
        code.iter()
            .filter(|i| i.rflags_read() != 0)
            .map(Instruction::ip)
            .collect(),
    )
}

/// Tells whether the replay can check a packed-integer instruction.
///
/// That is a 128-bit vector move to or from memory, a bitwise operation,
/// lane-wise addition and subtraction, a pack, an unpack or a shuffle:
/// each an instruction the emulator runs lane by lane and the lifter
/// writes a statement for, as the operation's own call.
///
/// The forms the two sides do not share stay out, each named: `pshufb`,
/// `palignr` and the VEX arithmetic (`vpaddb` and its kin), which the
/// emulator does not model; the lane compares, byte extremes, masks,
/// inserts, extracts and word shuffles, which both sides model but a
/// later slice admits; the 256-bit and `mmx` forms, whose registers no
/// word of this holds. A shift's count is an immediate, the only form
/// whose statement's argument names the count whole.
///
/// # Arguments
///
/// * `i` - The instruction.
/// * `info` - Register-access facts.
fn packed_integer(i: &Instruction, info: &mut InstructionInfoFactory) -> bool {
    use Mnemonic as M;
    if i.has_lock_prefix() || matches!(i.segment_prefix(), Register::FS | Register::GS) {
        return false;
    }
    // A memory operand, source or destination: sixteen bytes at an address
    // either side names, off the segment registers this check leaves out.
    let memory = (0..i.op_count()).any(|n| i.op_kind(n) == OpKind::Memory)
        && i.memory_size().size() == 16
        && !matches!(i.memory_segment(), Register::FS | Register::GS)
        && (matches!(
            i.memory_base(),
            Register::None | Register::RIP | Register::EIP
        ) || i.memory_base().is_gpr())
        && (i.memory_index() == Register::None || i.memory_index().is_gpr());
    let dst = i.op0_kind() == OpKind::Register && i.op0_register().is_xmm();
    let src = matches!(i.op1_kind(), OpKind::Register if i.op1_register().is_xmm()) || memory;
    let imm = i.op1_kind() == OpKind::Immediate8;
    let shape = match i.mnemonic() {
        M::Movaps | M::Movups | M::Movapd | M::Movupd | M::Movdqa | M::Movdqu => {
            i.op_count() == 2 && memory
        }
        M::Xorps
        | M::Xorpd
        | M::Andps
        | M::Andpd
        | M::Orps
        | M::Orpd
        | M::Andnps
        | M::Andnpd
        | M::Pxor
        | M::Pand
        | M::Pandn
        | M::Por
        | M::Paddb
        | M::Paddw
        | M::Paddd
        | M::Paddq
        | M::Psubb
        | M::Psubw
        | M::Psubd
        | M::Psubq
        | M::Packssdw
        | M::Packsswb
        | M::Packuswb
        | M::Punpcklbw
        | M::Punpcklwd
        | M::Punpckldq
        | M::Punpcklqdq
        | M::Punpckhbw
        | M::Punpckhwd
        | M::Punpckhdq
        | M::Punpckhqdq => i.op_count() == 2 && dst && src,
        M::Pshufd => {
            i.op_count() == 3
                && dst
                && (matches!(i.op1_kind(), OpKind::Register if i.op1_register().is_xmm()) || memory)
                && i.op2_kind() == OpKind::Immediate8
        }
        M::Psllw
        | M::Pslld
        | M::Psllq
        | M::Psrlw
        | M::Psrld
        | M::Psrlq
        | M::Psraw
        | M::Psrad
        | M::Pslldq
        | M::Psrldq => i.op_count() == 2 && dst && imm,
        _ => false,
    };
    shape
        && info.info(i).used_registers().iter().all(|u| {
            let r = u.register();
            r.is_gpr()
                || r.is_xmm()
                || matches!(r, Register::RIP | Register::EIP)
                || (r.is_segment_register() && !matches!(r, Register::FS | Register::GS))
        })
}

/// Tells whether the replay can check a block.
///
/// Every instruction is in the integer subset ([`integer`]), is a
/// scalar-float one ([`scalar_float`]), is a packed-integer one
/// ([`packed_integer`]), or is the zero fill of a structure, a vector
/// register zeroed (`xorps xmm0, xmm0`) and stored sixteen bytes at a
/// time (`movups [rsp+0x20], xmm0`), whose bytes both sides know.
///
/// # Arguments
///
/// * `code` - The block's instructions.
/// * `info` - Register-access facts.
fn integer_or_zero_fill(code: &[Instruction], info: &mut InstructionInfoFactory) -> bool {
    let mut zeroed: Vec<Register> = Vec::new();
    code.iter().all(|i| {
        if integer(i, info) || scalar_float(i, info) {
            return true;
        }
        let regs = i.op_count() == 2 && i.op1_kind() == OpKind::Register;
        match i.mnemonic() {
            Mnemonic::Xorps | Mnemonic::Xorpd | Mnemonic::Pxor
                if regs
                    && i.op0_kind() == OpKind::Register
                    && i.op0_register() == i.op1_register()
                    && i.op0_register().is_xmm() =>
            {
                zeroed.push(i.op0_register());
                true
            }
            Mnemonic::Movups
            | Mnemonic::Movaps
            | Mnemonic::Movupd
            | Mnemonic::Movapd
            | Mnemonic::Movdqu
            | Mnemonic::Movdqa
                if regs
                    && i.op0_kind() == OpKind::Memory
                    && i.memory_size().size() == 16
                    && zeroed.contains(&i.op1_register())
                    && !matches!(i.memory_segment(), Register::FS | Register::GS)
                    && i.memory_base().is_gpr()
                    && (i.memory_index() == Register::None || i.memory_index().is_gpr()) =>
            {
                true
            }
            _ => packed_integer(i, info),
        }
    })
}

/// Why a block outside the checked subset ([`integer_or_zero_fill`]) is not
/// checked, by its first instruction outside it.
///
/// A memory access through `fs` or `gs` reads the thread block (the
/// exception chain, the stack bounds, thread-local storage), which is no
/// float; an instruction naming a floating-point or vector register, or an
/// x87 one, is the float/vector form the replay leaves alone; anything
/// else is an instruction no model covers.
///
/// # Arguments
///
/// * `code` - The block's instructions.
/// * `info` - Register-access facts.
fn outside_subset(code: &[Instruction], info: &mut InstructionInfoFactory) -> &'static str {
    let Some(i) = code
        .iter()
        .find(|i| !(integer(i, info) || scalar_float(i, info) || packed_integer(i, info)))
    else {
        return OUTSIDE_FLOAT;
    };
    let memory = (0..i.op_count()).any(|n| i.op_kind(n) == OpKind::Memory);
    if memory && matches!(i.memory_segment(), Register::FS | Register::GS) {
        return "a read or write through the thread block";
    }
    let float = format!("{:?}", i.mnemonic()).starts_with('F')
        || info.info(i).used_registers().iter().any(|u| {
            let r = u.register();
            r.is_vector_register() || r.is_st() || r.is_mm() || r.is_k()
        });
    if float {
        OUTSIDE_FLOAT
    } else {
        "an instruction outside every checked form"
    }
}

/// Tells whether a block reads whole vector lanes: any of its instructions
/// is a packed-integer one ([`packed_integer`]), whose statements carry the
/// full 128 bits the machine's own registers hold.
///
/// # Arguments
///
/// * `code` - The block's instructions.
/// * `info` - Register-access facts.
fn reads_whole_lanes(code: &[Instruction], info: &mut InstructionInfoFactory) -> bool {
    code.iter().any(|i| packed_integer(i, info))
}

/// A value stored `n` bytes wide as the text holds it.
///
/// That is what it evaluates to up to a word, a whole vector for a full
/// lane, zero for a wider zero (a vector register's zero fill), `None`
/// for anything else wider.
///
/// # Arguments
///
/// * `text` - The text's state.
/// * `v` - The value.
/// * `n` - Its width in bytes.
fn wide_value(text: &Text<'_, '_>, v: &Expr, n: u64) -> Option<u128> {
    if n <= 8 {
        return text.eval(v).map(u128::from);
    }
    match v {
        Expr::Const(0) => Some(0),
        _ => text.vec(v),
    }
}

/// The values a block's comparisons turn on: its constants, one either
/// side of each, zero, one, and the signed and unsigned limits at the
/// register width.
///
/// # Arguments
///
/// * `code` - The block's instructions.
/// * `width` - The register width, 32 or 64.
fn comparands(code: &[Instruction], width: u8) -> Vec<u64> {
    let mask = low(width);
    let mut pool = vec![
        0,
        1,
        mask,
        0x7fff_ffff,
        0x8000_0000,
        0xffff_ffff,
        mask >> 1,
        (mask >> 1).wrapping_add(1),
    ];
    for i in code {
        for n in 0..i.op_count() {
            if let Ok(k) = i.try_immediate(n) {
                pool.extend([k, k.wrapping_add(1), k.wrapping_sub(1)]);
            }
        }
    }
    pool.iter_mut().for_each(|v| *v &= mask);
    pool.sort_unstable();
    pool.dedup();
    pool
}

/// Mixes bits, so neighbouring inputs give unrelated outputs.
///
/// # Arguments
///
/// * `x` - The input.
fn mix(mut x: u64) -> u64 {
    x ^= x >> 33;
    x = x.wrapping_mul(0xff51_afd7_ed55_8ccd);
    x ^= x >> 33;
    x = x.wrapping_mul(0xc4ce_b9fe_1a85_ec53);
    x ^ (x >> 33)
}

/// The low 64 bits of a whole vector lane.
///
/// # Arguments
///
/// * `v` - The lane, masked to the width its operation computes at first.
#[expect(
    clippy::cast_possible_truncation,
    reason = "a lane is masked to its width before this, so the cast drops no bit"
)]
fn low64(v: u128) -> u64 {
    v as u64
}

/// Two vectors combined lane by lane, each result kept to its lane.
///
/// # Arguments
///
/// * `a` - The first vector.
/// * `b` - The second.
/// * `bits` - The lane width, 8 through 64.
/// * `f` - The per-lane operation.
fn lanes(a: u128, b: u128, bits: u32, f: impl Fn(u64, u64) -> u64) -> u128 {
    let lane = (1u128 << bits) - 1;
    (0..128 / bits).fold(0u128, |out, k| {
        let at = k * bits;
        let (x, y) = ((a >> at) & lane, (b >> at) & lane);
        out | ((u128::from(f(low64(x), low64(y))) & lane) << at)
    })
}

/// One vector's every lane of `bits` wide on its own.
///
/// # Arguments
///
/// * `v` - The vector.
/// * `bits` - The lane width, 8 through 64.
/// * `f` - The per-lane operation.
fn each(v: u128, bits: u32, f: impl Fn(u64) -> u64) -> u128 {
    lanes(v, 0, bits, |x, _| f(x))
}

/// A lane's bits sign-extended to a signed word, at one of the widths a
/// lane operation narrows or shifts at (16 or 32), where the extension
/// loses nothing.
///
/// # Arguments
///
/// * `x` - The lane.
/// * `bits` - Its width.
fn lane_sext(x: u64, bits: u32) -> i64 {
    let shift = 64 - bits;
    (x << shift).cast_signed() >> shift
}

/// Tells whether an expression is a floating-point value.
///
/// # Arguments
///
/// * `e` - The expression.
fn floating(e: &Expr) -> bool {
    match e {
        Expr::FConst(..)
        | Expr::Deref(_, Ty::F32 | Ty::F64)
        | Expr::Cast(_, Ty::F32 | Ty::F64)
        | Expr::Un(UnOp::Sqrt | UnOp::Fabs, _) => true,
        Expr::Bin(op, l, r) => op.is_float() || floating(l) || floating(r),
        Expr::Var(Key::Reg(r)) => !r.is_gpr(),
        _ => false,
    }
}

/// The width a unary operator works at.
///
/// A bit count, scan or byte swap works at its operand's type
/// (`lzcnt((uint32_t)x)` counts 32 bits, as the lifter writes a 32-bit
/// one), anything else at the register width.
///
/// # Arguments
///
/// * `op` - The operator.
/// * `x` - Its operand.
/// * `width` - The register width, 32 or 64.
fn op_width(op: UnOp, x: &Expr, width: u8) -> u8 {
    match op {
        UnOp::Bswap | UnOp::Tzcnt | UnOp::Lzcnt | UnOp::Popcnt | UnOp::Bsf | UnOp::Bsr => match x {
            Expr::Cast(_, ty) | Expr::Deref(_, ty) => ty.bits().min(width),
            _ => width,
        },
        UnOp::Neg | UnOp::Not | UnOp::Sqrt | UnOp::Fabs => width,
    }
}

/// The value a register holds on the emulator, in the register's own lane.
///
/// # Arguments
///
/// * `emu` - The emulator.
/// * `r` - Any general register, or the stack pointer.
/// * `width` - The register width, 32 or 64.
fn reg_value(emu: &Emulator<'_>, r: Register, width: u8) -> Option<u64> {
    let full = if width == 32 {
        r.full_register32()
    } else {
        r.full_register()
    };
    let name = REGS
        .iter()
        .chain(REGS_32.iter())
        .find(|(_, x)| *x == full)
        .map(|(n, _)| *n)
        .or_else(|| matches!(full, Register::RSP | Register::ESP).then_some("rsp"))?;
    let v = emu.register(name)?;
    let high = matches!(r, Register::AH | Register::CH | Register::DH | Register::BH);
    let bits = u8::try_from(r.size() * 8).ok()?;
    Some(if high { v >> 8 } else { v } & low(bits))
}

/// The value of an instruction's first operand on the emulator: a
/// register's, a branch's target, or the word its memory operand reads.
///
/// # Arguments
///
/// * `emu` - The emulator, stopped before the instruction.
/// * `i` - The instruction.
/// * `width` - The register width, 32 or 64.
fn operand(emu: &Emulator<'_>, i: &Instruction, width: u8) -> Option<u64> {
    match i.op0_kind() {
        OpKind::Register => reg_value(emu, i.op0_register(), width),
        OpKind::NearBranch16 | OpKind::NearBranch32 | OpKind::NearBranch64 => {
            Some(i.near_branch_target())
        }
        OpKind::Memory => {
            if matches!(i.memory_segment(), Register::FS | Register::GS) {
                return None;
            }
            let base = i.memory_base();
            let mut at = i.memory_displacement64();
            if !matches!(base, Register::RIP | Register::EIP) {
                if base != Register::None {
                    at = at.wrapping_add(reg_value(emu, base, width)?);
                }
                if i.memory_index() != Register::None {
                    let index = reg_value(emu, i.memory_index(), width)?;
                    at = at.wrapping_add(index.wrapping_mul(u64::from(i.memory_index_scale())));
                }
            }
            machine_word(emu, at, from_usize(i.memory_size().size()), width)
        }
        _ => None,
    }
}

/// Where the replay notes the last write of a variable held outside
/// memory, beside the bytes it notes for memory: an address no program
/// maps, one per variable.
///
/// # Arguments
///
/// * `k` - A register, temporary or parameter.
fn key_spot(k: Key) -> u64 {
    let code = match k {
        Key::Reg(r) => from_usize(r as usize),
        Key::Tmp(id) => (1 << 32) | u64::from(id),
        Key::Param(i) => (2 << 32) | u64::from(i),
        Key::Slot(o) => (3 << 32) ^ o.cast_unsigned(),
        Key::Global(a, _) => (4 << 32) ^ a,
        Key::A64(r) => (5 << 32) | u64::from(a64_code(r)),
    };
    TLS_BASE.wrapping_sub(1 << 40) | code
}

/// The lane a value handed over in a register fills.
///
/// That is a byte, a word or a doubleword when the value provably fits one
/// ([`known_bits`]), else the whole register. The callee or caller reads
/// that lane, and the register's bits above it are whatever the
/// instruction that set the lane left there (`mov al, 1; ret` returns `1`).
///
/// # Arguments
///
/// * `e` - The value.
/// * `width` - The register width, 32 or 64.
fn value_lane(e: &Expr, width: u8) -> u8 {
    match known_bits(e) {
        k if k <= 0xff => 8,
        k if k <= 0xffff => 16,
        k if k <= 0xffff_ffff => 32,
        _ => width,
    }
    .min(width)
}

/// `n` bytes of the emulator's memory, little-endian.
///
/// # Arguments
///
/// * `emu` - The emulator.
/// * `at` - The address, wrapped at the register width.
/// * `n` - Bytes, at most 8.
/// * `width` - The register width, 32 or 64.
fn machine_word(emu: &Emulator<'_>, at: u64, n: u64, width: u8) -> Option<u64> {
    let mut v = 0u64;
    for i in (0..n.min(8)).rev() {
        v = (v << 8) | u64::from(emu.byte_at(at.wrapping_add(i) & low(width))?);
    }
    Some(v)
}

/// The text's state: its variables and memory, as the replay leaves them.
struct Text<'t, 'p> {
    /// Variables held outside memory: registers' and temporaries'.
    vars: FxHashMap<Key, u64>,
    /// Variables last assigned a value the replay cannot evaluate.
    unknown: FxHashSet<Key>,
    /// Whole 128-bit lanes of the vector registers, and of any variable a
    /// packed statement parked one in: what a whole-vector expression reads.
    vecs: FxHashMap<Key, u128>,
    /// Memory the text wrote.
    mem: FxHashMap<u64, u8>,
    /// Bytes last written with a value the replay cannot evaluate.
    lost: FxHashSet<u64>,
    /// A store through an address the replay cannot evaluate, or a call,
    /// may have changed any byte: memory reads as unknown.
    lost_all: bool,
    /// The bytes both sides start from: the seeded stack and any
    /// variable in memory the block's equality fixes.
    base: &'t FxHashMap<u64, u8>,
    /// The image's memory before any run.
    template: &'t Emulator<'p>,
    /// The seed of the bytes nothing backs ([`fill_byte`]).
    fill: u64,
    /// The stack pointer at the function's entry: where slot 0 is.
    sp0: u64,
    /// The register width, 32 or 64.
    width: u8,
    /// The trial's seed, which draws every variable's starting value.
    seed: u64,
    /// The values a draw prefers, empty for a random state.
    pool: &'t [u64],
    /// The instruction of the statement being replayed.
    at: u64,
    /// The stack pointer where the block's run stops: what the text's
    /// `rsp` names once the lifter lost the frame offset (`sub rsp, rax`
    /// for an `alloca`).
    rsp: Option<u64>,
    /// The statement that last wrote each byte the text wrote, and each
    /// variable held outside memory (at its [`key_spot`]), by its
    /// instruction: where a disagreement about it is the text's.
    writers: FxHashMap<u64, u64>,
    /// Each byte the text wrote, with its place in the write and the
    /// write's length: a byte past the low four of an eight-byte store
    /// differs only in a value's upper half.
    lanes: FxHashMap<u64, (u8, u8)>,
    /// Each frame byte the text last wrote through a slot's name, with that
    /// slot's offset.
    names: FxHashMap<u64, i64>,
    /// The width in bits each slot the text declares is declared with.
    slot_bits: &'t BTreeMap<i64, u8>,
    /// The declaration type of each vector register the text names a
    /// float, so a bare float variable's unary op carries a width.
    reg_ty: &'t BTreeMap<Key, Ty>,
    /// Each instruction of the block that sets the flags, as its address
    /// and whether it was a float compare, and each that reads them: the
    /// setter before the reader a condition's statement stands at says
    /// which way the condition reads when its operands carry no float
    /// type (a parameter's variable), because the lifter writes a float
    /// compare's `Cmp` no differently from an integer one. Empty once the
    /// block's statements are replayed, so a condition carried into a
    /// successor claims no instruction.
    flag_setters: (Vec<(u64, bool)>, Vec<u64>),
}

impl Text<'_, '_> {
    /// The starting value of a variable not in memory: a hash of the
    /// trial's seed and the variable, three times in four one of the
    /// pool's values when there is a pool.
    ///
    /// # Arguments
    ///
    /// * `k` - The variable.
    fn drawn(&self, k: Key) -> u64 {
        let h = mix(self.seed ^ mix(key_spot(k)));
        let v = match self.pool.len() {
            0 => h,
            n if h & 3 != 0 => self.pool[usize::try_from((h >> 2) % from_usize(n)).unwrap_or(0)],
            _ => h,
        };
        v & low(self.width)
    }

    /// A byte as the text holds it, `None` when unknown.
    ///
    /// # Arguments
    ///
    /// * `at` - The address.
    fn byte(&self, at: u64) -> Option<u8> {
        if self.lost_all || self.lost.contains(&at) {
            return None;
        }
        Some(
            self.mem
                .get(&at)
                .or_else(|| self.base.get(&at))
                .copied()
                .or_else(|| self.template.byte_at(at))
                .unwrap_or_else(|| fill_byte(self.fill, at)),
        )
    }

    /// Tells whether `n` bytes at `at` run past the top of the address
    /// space, where the processor faults and neither side's model of the
    /// access can be compared with the other's.
    ///
    /// # Arguments
    ///
    /// * `at` - The address.
    /// * `n` - Bytes.
    fn crosses_top(&self, at: u64, n: u64) -> bool {
        let mask = low(self.width);
        n.saturating_sub(1) > mask - (at & mask)
    }

    /// `n` bytes as the text holds them, little-endian.
    ///
    /// # Arguments
    ///
    /// * `at` - The address.
    /// * `n` - Bytes, at most 8.
    fn read(&self, at: u64, n: u64) -> Option<u64> {
        if self.crosses_top(at, n) {
            return None;
        }
        let mut v = 0u64;
        for i in (0..n.min(8)).rev() {
            v = (v << 8) | u64::from(self.byte(at.wrapping_add(i) & low(self.width))?);
        }
        Some(v)
    }

    /// Sixteen bytes as the text holds them, one whole vector lane.
    ///
    /// # Arguments
    ///
    /// * `at` - The address.
    fn read_vec(&self, at: u64) -> Option<u128> {
        if self.crosses_top(at, 16) {
            return None;
        }
        let lo = self.read(at, 8)?;
        let hi = self.read(at.wrapping_add(8) & low(self.width), 8)?;
        Some(u128::from(lo) | u128::from(hi) << 64)
    }

    /// Writes `n` bytes of `v`, or marks them unknown.
    ///
    /// # Arguments
    ///
    /// * `at` - The address.
    /// * `n` - Bytes.
    /// * `v` - The value, `None` when unknown.
    fn write(&mut self, at: u64, n: u64, v: Option<u128>) {
        if self.crosses_top(at, n) {
            self.lost_all = true;
            return;
        }
        for i in 0..n {
            let a = at.wrapping_add(i) & low(self.width);
            match v {
                Some(v) => {
                    self.mem.insert(
                        a,
                        lo8(low64(
                            v.checked_shr(8 * u32::try_from(i).unwrap_or(0))
                                .unwrap_or(0),
                        )),
                    );
                    self.lost.remove(&a);
                }
                None => {
                    self.lost.insert(a);
                }
            }
            self.writers.insert(a, self.at);
            self.names.remove(&a);
            self.lanes.insert(
                a,
                (
                    u8::try_from(i).unwrap_or(u8::MAX),
                    u8::try_from(n).unwrap_or(u8::MAX),
                ),
            );
        }
    }

    /// A variable's value, `None` when unknown.
    ///
    /// # Arguments
    ///
    /// * `k` - The variable.
    fn var(&self, k: Key) -> Option<u64> {
        if self.unknown.contains(&k) {
            return None;
        }
        match k {
            // INVARIANT: a slot's name reads the slot as the text declares
            // it, a `uint8_t` its one byte.
            Key::Slot(o) => {
                let bits = self.slot_bits.get(&o).copied().unwrap_or(self.width);
                if bits > 64 {
                    return None;
                }
                let n = u64::from(bits / 8).max(1);
                if self.foreign(o, n) {
                    return None;
                }
                self.read(self.sp0.wrapping_add_signed(o), n)
            }
            Key::Global(a, bits) => (a < TLS_BASE)
                .then_some(())
                .and_then(|()| self.read(a, u64::from(bits / 8).max(1))),
            Key::Reg(Register::RSP | Register::ESP) => self.rsp,
            // INVARIANT: the x87 stack registers hold their values on a
            // stack the machine runs and the text's state never seeded, so
            // an expression reading one stays unevaluated; an xmm
            // register's variable reads the state the trial seeded.
            Key::Reg(r) if !r.is_gpr() && !r.is_xmm() => None,
            Key::Reg(_) | Key::Tmp(_) | Key::Param(_) | Key::A64(_) => {
                Some(self.vars.get(&k).copied().unwrap_or_else(|| self.drawn(k)))
            }
        }
    }

    /// Tells whether the text last wrote any of `n` bytes at slot `o`
    /// through another slot's name.
    ///
    /// C variables do not share bytes: after `arg_3 = 0;` over the high
    /// byte of the parameter `a1`, the text's `a1` still holds what it
    /// held, so reading those bytes under `a1`'s name is no claim of the
    /// text.
    ///
    /// # Arguments
    ///
    /// * `o` - The slot read.
    /// * `n` - Bytes read.
    fn foreign(&self, o: i64, n: u64) -> bool {
        let at = self.sp0.wrapping_add_signed(o);
        (0..n).any(|i| {
            self.names
                .get(&(at.wrapping_add(i) & low(self.width)))
                .is_some_and(|p| *p != o)
        })
    }

    /// Evaluates an expression over the text's state, every operator at
    /// the register width as the text's variables are; `None` for what
    /// the replay cannot evaluate.
    ///
    /// # Arguments
    ///
    /// * `e` - The expression.
    fn eval(&self, e: &Expr) -> Option<u64> {
        self.eval_at(e, EVAL_DEPTH)
    }

    /// The width of a floating-point expression over the text's state, or
    /// `None` for an integer one.
    ///
    /// A typed node carries its width; a binary operation computes at the
    /// wider of its operands ([`float_arith`]), the rounding the machine's
    /// own single operation makes. A temporary's variable and a slot's own
    /// carry no type this walk can see (an integer slot is declared with
    /// the same widths a float one is), so an expression through one stays
    /// unevaluated, which the counts report.
    ///
    /// # Arguments
    ///
    /// * `e` - The expression.
    fn float_bits(&self, e: &Expr) -> Option<u8> {
        match e {
            Expr::Deref(_, Ty::F32) | Expr::Cast(_, Ty::F32) | Expr::FConst(_, Ty::F32) => Some(32),
            Expr::Deref(_, Ty::F64) | Expr::Cast(_, Ty::F64) | Expr::FConst(_, Ty::F64) => Some(64),
            Expr::Bin(op, l, r) if op.is_float() => {
                Some(self.float_bits(l)?.max(self.float_bits(r)?))
            }
            Expr::Un(_, inner) => self.float_bits(inner),
            _ => None,
        }
    }

    /// The width a float unary operation over `e` runs at: the width its
    /// expression carries, or the width the text's own declaration gives a
    /// bare vector register variable, whose sign flip and magnitude are
    /// the register's whole lane whatever else computed it.
    ///
    /// A binary operation takes nothing here: a register used at both
    /// widths - a double a stray single computes on - would be compared at
    /// the width the text claims and not the one the machine used, so a
    /// binary chain over bare variables stays counted.
    ///
    /// # Arguments
    ///
    /// * `e` - The unary operation's operand.
    fn un_width(&self, e: &Expr) -> Option<u8> {
        self.float_bits(e).or(match e {
            Expr::Var(k) => match self.reg_ty.get(k) {
                Some(Ty::F32) => Some(32),
                Some(Ty::F64) => Some(64),
                _ => None,
            },
            _ => None,
        })
    }

    /// [`Text::eval`] to a depth.
    ///
    /// # Arguments
    ///
    /// * `e` - The expression.
    /// * `depth` - How much deeper to look.
    fn eval_at(&self, e: &Expr, depth: u8) -> Option<u64> {
        let d = depth.checked_sub(1)?;
        let w = self.width;
        match e {
            Expr::Const(v) | Expr::FConst(v, _) => Some(*v),
            Expr::Var(k) => self.var(*k),
            Expr::Str(_) | Expr::Call(..) => None,
            Expr::Sp(o) => Some(self.sp0.wrapping_add_signed(*o) & low(w)),
            Expr::Bin(op, l, r) if op.is_float() => {
                let fb = self.float_bits(l)?.max(self.float_bits(r)?);
                let (a, b) = (
                    float_of(self.eval_at(l, d)?, fb),
                    float_of(self.eval_at(r, d)?, fb),
                );
                float_arith(*op, a, b, fb)
            }
            Expr::Bin(op, l, r) => {
                let (a, b) = (self.eval_at(l, d)?, self.eval_at(r, d)?);
                match fold(*op, Expr::Const(a), Expr::Const(b), w) {
                    Expr::Const(v) => Some(v),
                    _ => None,
                }
            }
            Expr::Un(UnOp::Neg, x) if self.un_width(x).is_some() => {
                let fb = self.un_width(x)?;
                Some(self.eval_at(x, d)? ^ (1u64 << (u32::from(fb) - 1)))
            }
            Expr::Un(op @ (UnOp::Sqrt | UnOp::Fabs), x) if self.un_width(x).is_some() => {
                float_un(*op, self.eval_at(x, d)?, self.un_width(x)?)
            }
            Expr::Un(op, x) => {
                match unary(*op, Expr::Const(self.eval_at(x, d)?), op_width(*op, x, w)) {
                    Expr::Const(v) => Some(v),
                    _ => None,
                }
            }
            Expr::Deref(a, ty) => {
                if *ty == Ty::U128 {
                    return None;
                }
                let n = u64::from(ty.bits() / 8).max(1);
                if let Expr::Sp(o) = **a
                    && self.foreign(o, n)
                {
                    return None;
                }
                let at = self.eval_at(a, d)? & low(w);
                self.read(at, n)
            }
            Expr::Cond(c) => self.cond_at(c, d).map(u64::from),
            Expr::Ternary(c, a, b) => {
                if self.cond_at(c, d)? {
                    self.eval_at(a, d)
                } else {
                    self.eval_at(b, d)
                }
            }
            Expr::Sext(x, bits) => sext(self.eval_at(x, d)?, *bits),
            Expr::Cast(x, ty) => {
                if *ty == Ty::U128 {
                    return None;
                }
                if matches!(ty, Ty::F32 | Ty::F64) {
                    // An integer converted to a float is not modelled: the
                    // conversion the machine makes has no helper here.
                    let from = self.float_bits(x)?;
                    return Some(convert_float(self.eval_at(x, d)?, Some(from), *ty));
                }
                let v = self.eval_at(x, d)?;
                match self.float_bits(x) {
                    // A float converted to an integer truncates, and a
                    // value the integer cannot hold (or a NaN) converts to
                    // the "integer indefinite" the processor gives. A float
                    // operand with no width this walk can see (an xmm
                    // register's own variable) is not converted at all.
                    Some(fb) => Some(float_to_int(v, fb, ty.bits())),
                    None if floating(x) => None,
                    None => Some(v & low(ty.bits())),
                }
            }
        }
    }

    /// [`Text::vec_at`] to the replay's depth.
    ///
    /// # Arguments
    ///
    /// * `e` - The expression.
    fn vec(&self, e: &Expr) -> Option<u128> {
        self.vec_at(e, EVAL_DEPTH)
    }

    /// A variable's whole 128-bit lane, `None` when the text does not hold
    /// it whole: a vector register's or a parked temporary's state, a slot's
    /// or a data global's own sixteen bytes.
    ///
    /// # Arguments
    ///
    /// * `k` - The variable.
    fn vec_var(&self, k: Key) -> Option<u128> {
        if self.unknown.contains(&k) {
            return None;
        }
        match k {
            Key::Slot(o) if !self.foreign(o, 16) => self.read_vec(self.sp0.wrapping_add_signed(o)),
            Key::Global(a, 128) if a < TLS_BASE => self.read_vec(a),
            Key::Reg(r) if !r.is_gpr() && !r.is_xmm() => None,
            Key::Reg(_) | Key::Tmp(_) | Key::Param(_) | Key::A64(_) => self.vecs.get(&k).copied(),
            Key::Slot(_) | Key::Global(..) => None,
        }
    }

    /// The whole 128-bit lane an expression holds, `None` for what the
    /// replay cannot evaluate at that width: a constant, a variable's own
    /// lane, a sixteen-byte read, or a packed operation over whole lanes,
    /// each lane as the machine's own instruction computes it.
    ///
    /// # Arguments
    ///
    /// * `e` - The expression.
    /// * `depth` - How much deeper to look.
    fn vec_at(&self, e: &Expr, depth: u8) -> Option<u128> {
        let d = depth.checked_sub(1)?;
        match e {
            Expr::Const(v) => Some(u128::from(*v)),
            Expr::Var(k) => self.vec_var(*k),
            Expr::Deref(a, Ty::U128) => {
                if let Expr::Sp(o) = **a
                    && self.foreign(o, 16)
                {
                    return None;
                }
                let at = self.eval_at(a, d)? & low(self.width);
                self.read_vec(at)
            }
            Expr::Call(name, args) => self.packed_op(name, args, d),
            Expr::Str(_) | Expr::FConst(..) | Expr::Sp(_) | Expr::Sext(..) | Expr::Cast(..) => None,
            Expr::Bin(..) | Expr::Un(..) | Expr::Cond(..) | Expr::Ternary(..) => None,
            Expr::Deref(..) => None,
        }
    }

    /// The value of a packed operation's call, the name the lifter gives
    /// the instruction, over whole-lane arguments; the shifts take their
    /// count from a constant argument. Any other name, or an argument the
    /// text cannot evaluate whole, is `None`.
    ///
    /// # Arguments
    ///
    /// * `name` - The call's name, the mnemonic lowercased.
    /// * `args` - The call's arguments.
    /// * `d` - How much deeper to look.
    fn packed_op(&self, name: &str, args: &[Expr], d: u8) -> Option<u128> {
        let two = |a: &Expr, b: &Expr| Some((self.vec_at(a, d)?, self.vec_at(b, d)?));
        Some(match (name, args) {
            ("pxor" | "xorps" | "xorpd", [a, b]) => {
                let (x, y) = two(a, b)?;
                x ^ y
            }
            ("pand" | "andps" | "andpd", [a, b]) => {
                let (x, y) = two(a, b)?;
                x & y
            }
            ("por" | "orps" | "orpd", [a, b]) => {
                let (x, y) = two(a, b)?;
                x | y
            }
            ("pandn" | "andnps" | "andnpd", [a, b]) => {
                let (x, y) = two(a, b)?;
                !x & y
            }
            (
                "paddb" | "paddw" | "paddd" | "paddq" | "psubb" | "psubw" | "psubd" | "psubq",
                [a, b],
            ) => {
                let lane: u32 = match name {
                    "paddb" | "psubb" => 8,
                    "paddw" | "psubw" => 16,
                    "paddd" | "psubd" => 32,
                    _ => 64,
                };
                let (x, y) = two(a, b)?;
                let sub = name.starts_with("psub");
                lanes(x, y, lane, |l, r| {
                    if sub {
                        l.wrapping_sub(r)
                    } else {
                        l.wrapping_add(r)
                    }
                })
            }
            ("packssdw" | "packsswb" | "packuswb", [a, b]) => {
                let wide: u32 = if name == "packssdw" { 32 } else { 16 };
                let narrow = wide / 2;
                let signed_out = name != "packuswb";
                let wmask = (1u128 << wide) - 1;
                let mut v = 0u128;
                for (slot, from) in [(0u32, self.vec_at(a, d)?), (1, self.vec_at(b, d)?)] {
                    for k in 0..128 / wide {
                        let lane = low64((from >> (k * wide)) & wmask);
                        let wide_lane = lane_sext(lane, wide);
                        let clamped = if signed_out {
                            let top = (1i64 << (narrow - 1)) - 1;
                            wide_lane.clamp(-top - 1, top).cast_unsigned() & ((1u64 << narrow) - 1)
                        } else {
                            let top = (1i64 << narrow) - 1;
                            wide_lane.clamp(0, top).cast_unsigned()
                        };
                        v |= u128::from(clamped) << ((slot * (128 / wide) + k) * narrow);
                    }
                }
                v
            }
            (
                "punpcklbw" | "punpcklwd" | "punpckldq" | "punpcklqdq" | "punpckhbw" | "punpckhwd"
                | "punpckhdq" | "punpckhqdq",
                [a, b],
            ) => {
                let lane: u32 = match name {
                    "punpcklbw" | "punpckhbw" => 8,
                    "punpcklwd" | "punpckhwd" => 16,
                    "punpckldq" | "punpckhdq" => 32,
                    _ => 64,
                };
                let high = name.starts_with("punpckh");
                let (dst, src) = two(a, b)?;
                let lane_mask = (1u128 << lane) - 1;
                let n = 64 / lane;
                let first = if high { n } else { 0 };
                (0..n).fold(0u128, |v, k| {
                    let from = (first + k) * lane;
                    v | ((dst >> from) & lane_mask) << (2 * k * lane)
                        | ((src >> from) & lane_mask) << ((2 * k + 1) * lane)
                })
            }
            ("pshufd", [s, Expr::Const(order)]) => {
                let src = self.vec_at(s, d)?;
                (0..4u32).fold(0u128, |v, slot| {
                    let pick = order >> (slot * 2) & 3;
                    v | ((src >> (pick * 32)) & 0xffff_ffff) << (slot * 32)
                })
            }
            ("psllw" | "pslld" | "psllq" | "psrlw" | "psrld" | "psrlq", [s, Expr::Const(n)]) => {
                let lane: u32 = match name {
                    "psllw" | "psrlw" => 16,
                    "pslld" | "psrld" => 32,
                    _ => 64,
                };
                let right = name.starts_with("psrl");
                let v = self.vec_at(s, d)?;
                each(v, lane, |x| {
                    if *n >= u64::from(lane) {
                        0
                    } else if right {
                        x >> *n
                    } else {
                        x << *n
                    }
                })
            }
            ("psraw" | "psrad", [s, Expr::Const(n)]) => {
                let lane: u32 = if name == "psrad" { 32 } else { 16 };
                let shift = (*n).min(u64::from(lane) - 1);
                let v = self.vec_at(s, d)?;
                each(v, lane, |x| (lane_sext(x, lane) >> shift).cast_unsigned())
            }
            ("pslldq" | "psrldq", [s, Expr::Const(n)]) => {
                let v = self.vec_at(s, d)?;
                if *n >= 16 {
                    0
                } else if name == "pslldq" {
                    v << (*n * 8)
                } else {
                    v >> (*n * 8)
                }
            }
            (
                "pshufd" | "psllw" | "pslld" | "psllq" | "psrlw" | "psrld" | "psrlq" | "psraw"
                | "psrad" | "pslldq" | "psrldq" | "pxor" | "xorps" | "xorpd" | "pand" | "andps"
                | "andpd" | "por" | "orps" | "orpd" | "pandn" | "andnps" | "andnpd" | "paddb"
                | "paddw" | "paddd" | "paddq" | "psubb" | "psubw" | "psubd" | "psubq" | "packssdw"
                | "packsswb" | "packuswb" | "punpcklbw" | "punpcklwd" | "punpckldq" | "punpcklqdq"
                | "punpckhbw" | "punpckhwd" | "punpckhdq" | "punpckhqdq",
                _,
            ) => return None,
            _ => return None,
        })
    }

    /// Moves the state to the side of a condition comparing a variable, or
    /// a variable plus a constant, with a constant that `want` says.
    ///
    /// The variable takes the value that meets the constant, one either side
    /// of it, zero or one, the first that puts the state there.
    ///
    /// # Arguments
    ///
    /// * `c` - The condition.
    /// * `want` - The side wanted.
    /// * `narrow` - The bits variables are known to fit in, where fewer
    ///   than a word: no value wider is tried.
    ///
    /// # Returns
    ///
    /// Whether the state is on that side now; where not, it is unchanged.
    fn steer(&mut self, c: &Cond, want: bool, narrow: &FxHashMap<Key, u8>) -> bool {
        let (x, n) = match &c.flags {
            Flags::Cmp(x, Expr::Const(n), _) => (x, *n),
            Flags::Test(x @ Expr::Var(k), Expr::Var(k2), _) if k == k2 => (x, 0),
            _ => return false,
        };
        let (k, d) = match x {
            Expr::Var(k) => (*k, 0),
            Expr::Bin(super::expr::Op::Add, v, d) => match (v.as_ref(), d.as_ref()) {
                (Expr::Var(k), Expr::Const(d)) => (*k, *d),
                _ => return false,
            },
            _ => return false,
        };
        if !matches!(k, Key::Reg(_) | Key::Tmp(_) | Key::Param(_)) {
            return false;
        }
        let old = self.vars.get(&k).copied();
        let n = n.wrapping_sub(d);
        let fits = low(narrow.get(&k).copied().unwrap_or(64).min(self.width));
        for v in [n, n.wrapping_add(1), n.wrapping_sub(1), 0, 1] {
            if v & fits != v {
                continue;
            }
            self.vars.insert(k, v);
            if self.cond(c) == Some(want) {
                return true;
            }
        }
        match old {
            Some(v) => self.vars.insert(k, v),
            None => self.vars.remove(&k),
        };
        false
    }

    /// Evaluates a condition over the text's state.
    ///
    /// # Arguments
    ///
    /// * `c` - The condition.
    fn cond(&self, c: &Cond) -> Option<bool> {
        self.cond_at(c, EVAL_DEPTH)
    }

    /// [`Text::cond`] to a depth.
    ///
    /// # Arguments
    ///
    /// * `c` - The condition.
    /// * `d` - How much deeper to look.
    fn cond_at(&self, c: &Cond, d: u8) -> Option<bool> {
        // A float comparison (`ucomiss` and its kin) reads its flags the
        // way the machine's compare leaves them, unordered on a NaN. Its
        // operands carry their width when they are typed, and when they
        // are not (a parameter's variable) the instruction that set the
        // flags is the only witness of which way the condition reads.
        if let Flags::Cmp(a, b, w) = &c.flags {
            let from_float = || {
                let (setters, readers) = &self.flag_setters;
                // The reader the statement stands at, then the setter
                // before it: a `setcc` and the folding after it read a
                // compare that earlier arithmetic no longer overwrote.
                readers
                    .iter()
                    .rev()
                    .find(|&&r| r <= self.at)
                    .and_then(|&r| setters.iter().rev().find(|&&(s, _)| s < r))
                    .is_some_and(|&(_, f)| f)
            };
            let fb = self
                .float_bits(a)
                .or_else(|| self.float_bits(b))
                .or_else(|| matches!(w, 32 | 64).then_some(*w).filter(|_| from_float()));
            if let Some(fb) = fb {
                let l = float_of(self.eval_at(a, d)?, fb);
                let r = float_of(self.eval_at(b, d)?, fb);
                return float_cc(c.cc.0, l, r);
            }
        }
        let k = |e: &Expr| {
            if floating(e) {
                None
            } else {
                self.eval_at(e, d).map(Expr::Const)
            }
        };
        let flags = match &c.flags {
            Flags::Cmp(a, b, w) => Flags::Cmp(k(a)?, k(b)?, *w),
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

    /// Replays `name = value;`.
    ///
    /// # Arguments
    ///
    /// * `k` - The variable.
    /// * `v` - The value.
    /// * `bits` - The variable's width, which the value is truncated to.
    fn assign(&mut self, k: Key, v: &Expr, bits: u8) {
        let n = u64::from(bits / 8).max(1);
        let mut value = wide_value(self, v, n);
        if bits <= 64 {
            value = value.map(|w| u128::from(low64(w) & low(bits)));
        }
        match k {
            Key::Slot(o) => {
                let at = self.sp0.wrapping_add_signed(o);
                self.write(at, n, value);
                for i in 0..n {
                    self.names.insert(at.wrapping_add(i) & low(self.width), o);
                }
            }
            Key::Global(a, gb) => {
                if a < TLS_BASE {
                    self.write(a, u64::from(gb / 8).max(1), value);
                }
            }
            Key::Reg(_) | Key::Tmp(_) | Key::Param(_) | Key::A64(_) => {
                // INVARIANT: a whole-lane write fills the vector's state and
                // its low half alike; a narrower one rewrites part of a lane
                // whose rest the machine keeps or clears by its own form, so
                // the whole-lane state stops holding the register.
                if bits > 64 {
                    match value {
                        Some(w) => {
                            self.vecs.insert(k, w);
                            self.vars.insert(k, low64(w));
                            self.unknown.remove(&k);
                        }
                        None => {
                            self.vecs.remove(&k);
                            self.unknown.insert(k);
                        }
                    }
                    self.writers.insert(key_spot(k), self.at);
                    return;
                }
                if matches!(k, Key::Reg(r) if r.is_xmm()) {
                    self.vecs.remove(&k);
                }
                match value.map(low64) {
                    Some(v) => {
                        self.vars.insert(k, v);
                        self.unknown.remove(&k);
                    }
                    None => {
                        self.unknown.insert(k);
                    }
                }
                self.writers.insert(key_spot(k), self.at);
            }
        }
    }

    /// Replays `*(T *)addr = value;`.
    ///
    /// # Arguments
    ///
    /// * `addr` - The address.
    /// * `ty` - The type stored.
    /// * `v` - The value.
    fn store(&mut self, addr: &Expr, ty: Ty, v: &Expr) {
        // INVARIANT: the lifter takes a store through a computed frame
        // address to cover the slots from its base up (an array's index is
        // not negative); a sampled index that reaches below the base is a
        // state the text does not speak about.
        if let (Some(k), Some(at)) = (frame_base(addr), self.eval(addr))
            && at
                .wrapping_sub(self.sp0.wrapping_add_signed(k))
                .cast_signed()
                .wrapping_shl(64 - u32::from(self.width))
                < 0
        {
            self.lost_all = true;
            return;
        }
        // INVARIANT: a TLS slot is a pseudo-address the machine reaches
        // through the thread block instead, so a store to one has no
        // machine bytes to compare.
        let Some(at) = self.eval(addr).filter(|a| *a < TLS_BASE) else {
            self.lost_all = true;
            return;
        };
        let n = u64::from(ty.bits() / 8).max(1);
        let value = wide_value(self, v, n);
        self.write(at, n, value);
    }

    /// Replays a `memset`, `memcpy` or `memmove` the text names for a
    /// string instruction.
    ///
    /// # Arguments
    ///
    /// * `routine` - Which.
    /// * `bits` - A fill's element width.
    /// * `args` - The destination, the fill value or the source, and the
    ///   length in bytes.
    fn routine(&mut self, routine: Routine, bits: u8, args: &[(ArgAt, Expr)]) {
        let [(_, dst), (_, from), (_, len)] = args else {
            self.lost_all = true;
            return;
        };
        let (Some(dst), Some(from), Some(len)) = (self.eval(dst), self.eval(from), self.eval(len))
        else {
            self.lost_all = true;
            return;
        };
        if len > from_usize(REGION_MAX) {
            self.lost_all = true;
            return;
        }
        let bytes: Option<Vec<u8>> = match routine {
            Routine::Memset => {
                let size = u64::from(bits / 8).max(1);
                Some(
                    (0..len)
                        .map(|i| {
                            lo8(from
                                .checked_shr(u32::try_from(8 * (i % size)).unwrap_or(0))
                                .unwrap_or(0))
                        })
                        .collect(),
                )
            }
            Routine::Memcpy | Routine::Memmove => (0..len)
                .map(|i| self.byte(from.wrapping_add(i) & low(self.width)))
                .collect(),
        };
        match bytes {
            Some(bytes) => {
                for (i, b) in (0u64..).zip(bytes) {
                    self.write(dst.wrapping_add(i), 1, Some(u128::from(b)));
                }
            }
            None => self.write(dst, len, None),
        }
    }
}

/// A function being replayed: what all its blocks share.
struct Function<'f, 'p> {
    /// The functions, for a jump table's targets.
    analysis: &'f Analysis,
    /// The image's emulator before any run, cloned per state.
    template: &'f Emulator<'p>,
    /// The function's entry.
    entry: u64,
    /// The replay's seed.
    seed: u64,
    /// The lifter's witness.
    w: &'f Witness,
    /// Each block's instructions, from the witness.
    code: &'f [Vec<Instruction>],
    /// The successors of each block in the graph the text was written for.
    succs: &'f [Vec<usize>],
    /// Each block's effects.
    effects: &'f [Vec<Effect>],
    /// The stack slots the text names, with their widest access in bytes.
    named: &'f BTreeMap<i64, u64>,
    /// The general registers, named as the emulator names them.
    regs: &'static [(&'static str, Register)],
    /// The register width, 32 or 64.
    width: u8,
}

/// One state a block is tried from, part way through: the emulator stopped
/// where the block ends, the text replayed so far.
struct Trial<'t, 'p> {
    /// The emulator.
    emu: Emulator<'p>,
    /// The text's state.
    text: Text<'t, 'p>,
    /// The stack pointer where the block starts on the emulator.
    rsp: u64,
    /// Bytes the emulator wrote.
    written: FxHashSet<u64>,
    /// Bytes of values pending in the block's IN environment, which the
    /// machine holds and the text does not hold yet.
    pending: FxHashSet<u64>,
    /// Whether the branch ending the block is taken, `None` when the
    /// emulator could not decide.
    taken: Option<bool>,
    /// A call made: what it may have changed is known on neither side.
    called: bool,
    /// Memory was compared at a call or a return already.
    settled: bool,
    /// The block's index.
    b: usize,
    /// The disagreements so far, by claim and place, one each.
    seen: BTreeSet<(Claim, String)>,
}

impl Function<'_, '_> {
    /// Checks one block from each of its states.
    ///
    /// # Arguments
    ///
    /// * `b` - The block's index.
    /// * `block` - The block.
    /// * `room` - Blocks still to be tried; this one spends one.
    /// * `out` - Where the counts and disagreements go.
    ///
    /// # Errors
    ///
    /// Why the block was not checked.
    fn check(
        &self,
        b: usize,
        block: &BasicBlock,
        room: &mut usize,
        out: &mut Replayed,
    ) -> Result<(), &'static str> {
        let w = self.w;
        let code = self
            .code
            .get(b)
            .filter(|c| !c.is_empty())
            .ok_or("no instructions")?;
        if !w.emitted.get(b).copied().unwrap_or(false) {
            return Err("not in the text");
        }
        if !w.processed.get(b).copied().unwrap_or(false) {
            return Err("not run by the dataflow");
        }
        if w.flag_readers.get(b).copied().unwrap_or(true) || self.flags_lost(b) {
            return Err("flags set in another block");
        }
        let inn = w.ins.get(b).ok_or("no witness")?;
        let sp = inn.sp.ok_or("the stack pointer unknown at its start")?;
        let effects = self.effects.get(b).ok_or("no effects")?;
        if effects.iter().any(|e| e.kind == EffectKind::Unmodeled) {
            return Err("a statement no effect models");
        }
        if effects.iter().any(|e| {
            matches!(&e.kind, EffectKind::Call(c) if matches!(c.shown, Shown::Elided | Shown::InPlace))
        }) {
            return Err("a call the text leaves out or reads in place");
        }
        // INVARIANT: the arguments a call shows are compared with what the
        // machine passes there, and the result a return shows with what it
        // hands back; what the text leaves out is compared with nothing, so
        // a block that drops a stack argument its callee reads, or returns
        // nothing where the callers read a result, makes no claim of
        // agreement.
        if effects
            .iter()
            .any(|e| matches!(&e.kind, EffectKind::Call(c) if c.short))
        {
            return Err(SHORT_CALL);
        }
        if effects
            .iter()
            .any(|e| matches!(&e.kind, EffectKind::Call(c) if c.contradicted))
            || (w.stated_contradicted
                && code
                    .last()
                    .is_some_and(|i| i.flow_control() == FlowControl::Return))
        {
            return Err(CONTRADICTED);
        }
        if w.result_read && effects.iter().any(|e| e.kind == EffectKind::Return(None)) {
            return Err(BARE_RETURN);
        }
        let mut info = InstructionInfoFactory::new();
        if !integer_or_zero_fill(code, &mut info) {
            return Err(outside_subset(code, &mut info));
        }
        if code.iter().any(aligns_stack) {
            return Err("a frame alignment");
        }
        let end = End::of(code)?;
        *room = room.checked_sub(1).ok_or(OVER_BUDGET)?;
        let pool = comparands(code, self.width);
        let mut seen = BTreeSet::new();
        let mut why = "no state compared";
        let mut compared = 0;
        // INVARIANT: a state the branch into the block rules out is drawn
        // again, a few times, so a block entered under a narrow condition
        // is still tried.
        let mut tried = 0;
        for trial in 0..TRIALS + RULED_OUT_RETRIES {
            if tried == TRIALS {
                break;
            }
            let pool: &[u64] = if trial == 0 { &[] } else { &pool };
            match self.trial(b, block, code, sp, end, pool, trial, &mut seen, out) {
                Ok(()) => compared += 1,
                Err(e) if e == RULED_OUT => {
                    why = e;
                    continue;
                }
                Err(e) => why = e,
            }
            tried += 1;
        }
        out.trials += compared;
        if compared == 0 { Err(why) } else { Ok(()) }
    }

    /// Tells whether the flags a block leaves reach a reader whose condition
    /// the text writes over unknown flags.
    ///
    /// Past blocks that leave the flags alone, a successor that reads them
    /// with none known on entry renders `FLAGS_UNKNOWN`, so the compare that
    /// set them has no statement anywhere in the text, and agreeing on the
    /// rest of the block says nothing about it.
    ///
    /// # Arguments
    ///
    /// * `b` - The block's index.
    fn flags_lost(&self, b: usize) -> bool {
        let w = self.w;
        let sets = |c: usize| {
            self.code
                .get(c)
                .is_some_and(|code| code.iter().any(|i| i.rflags_modified() != 0))
        };
        if !sets(b) {
            return false;
        }
        let mut next = self.succs.get(b).cloned().unwrap_or_default();
        let mut seen = BTreeSet::new();
        while let Some(s) = next.pop() {
            if !seen.insert(s) {
                continue;
            }
            if w.flag_readers.get(s).copied().unwrap_or(false)
                && w.ins.get(s).is_some_and(|env| env.flags == Flags::Unknown)
            {
                return true;
            }
            if !sets(s) && seen.len() <= FLAG_HOPS {
                next.extend(self.succs.get(s).into_iter().flatten());
            }
        }
        false
    }

    /// The condition a block is entered under: the text's branch ending its
    /// only predecessor, and whether the block is that branch's taken side.
    ///
    /// A predecessor that only jumps on, with no statement of its own, runs
    /// under its own branch, which is passed on.
    ///
    /// # Arguments
    ///
    /// * `b` - The block's index.
    fn guard(&self, b: usize) -> Option<(&Cond, bool)> {
        let mut b = b;
        for _ in 0..GUARD_JUMPS {
            let mut preds = (0..self.succs.len()).filter(|&p| self.succs[p].contains(&b));
            let p = preds.next()?;
            if preds.next().is_some() {
                return None;
            }
            let jcc = self.code.get(p)?.last()?;
            if jcc.flow_control() == FlowControl::UnconditionalBranch
                && self.effects.get(p).is_some_and(Vec::is_empty)
            {
                b = p;
                continue;
            }
            if jcc.flow_control() != FlowControl::ConditionalBranch {
                return None;
            }
            let start = self.code.get(b)?.first()?.ip();
            let (target, fall) = (jcc.near_branch_target(), jcc.next_ip());
            let taken = match start {
                _ if target == fall => return None,
                s if s == target => true,
                s if s == fall => false,
                _ => return None,
            };
            return match self.effects.get(p)?.last()? {
                Effect {
                    kind: EffectKind::Branch(c),
                    ..
                } => Some((c, taken)),
                _ => None,
            };
        }
        None
    }

    /// Checks one block from one state.
    ///
    /// # Arguments
    ///
    /// * `b` - The block's index.
    /// * `block` - The block.
    /// * `code` - Its instructions.
    /// * `sp` - The stack pointer at its start, from the function's entry.
    /// * `end` - How it ends.
    /// * `pool` - The values the state's variables are drawn from.
    /// * `trial` - Which state.
    /// * `seen` - The block's disagreements so far, by claim and place.
    /// * `out` - Where the counts and disagreements go.
    ///
    /// # Errors
    ///
    /// Why the state could not be compared.
    #[expect(
        clippy::too_many_arguments,
        reason = "one block's facts, threaded through"
    )]
    fn trial(
        &self,
        b: usize,
        block: &BasicBlock,
        code: &[Instruction],
        sp: i64,
        end: End,
        pool: &[u64],
        trial: u64,
        seen: &mut BTreeSet<(Claim, String)>,
        out: &mut Replayed,
    ) -> Result<(), &'static str> {
        let w = self.w;
        let inn = &w.ins[b];
        let mask = low(self.width);
        let mut rng = Rng(self.seed ^ block.start.rotate_left(17) ^ GOLDEN.wrapping_mul(trial + 1));
        let _ = rng.next();
        let fill = rng.next();
        let mut emu = self.template.clone();
        let reps = code
            .iter()
            .filter(|i| i.has_rep_prefix() || i.has_repe_prefix() || i.has_repne_prefix())
            .count();
        emu.set_budget(code.len() + 1 + reps * REGION_MAX);
        emu.set_permissive(true);
        emu.set_fill(Some(fill));
        let rsp = emu.register("rsp").ok_or("no stack pointer")?;
        let sp0 = rsp.wrapping_sub(sp.cast_unsigned()) & mask;
        let mut base: FxHashMap<u64, u8> = FxHashMap::default();
        for word in -STACK_WORDS..STACK_WORDS {
            let at = rsp.wrapping_add_signed(word * 8);
            for (i, byte) in (0u64..).zip(rng.next().to_le_bytes()) {
                base.insert(at.wrapping_add(i) & mask, byte);
            }
        }
        if let Some((k @ (Key::Slot(_) | Key::Global(..)), c)) = w.assumes.get(b).copied().flatten()
        {
            let (at, n) = match k {
                Key::Slot(o) => (
                    sp0.wrapping_add_signed(o),
                    u64::from(inn.slot_bits.get(&o).copied().unwrap_or(self.width) / 8),
                ),
                Key::Global(a, bits) => (a, u64::from(bits / 8).max(1)),
                Key::Reg(_) | Key::Tmp(_) | Key::Param(_) | Key::A64(_) => (0, 0),
            };
            for i in 0..n.min(8) {
                base.insert(at.wrapping_add(i) & mask, lo8(c >> (8 * i)));
            }
        }
        for (&at, &byte) in &base {
            emu.poke(at, byte);
        }
        let mut text = Text {
            vars: FxHashMap::default(),
            unknown: FxHashSet::default(),
            vecs: FxHashMap::default(),
            mem: FxHashMap::default(),
            lost: FxHashSet::default(),
            lost_all: false,
            base: &base,
            template: self.template,
            fill,
            sp0,
            width: self.width,
            seed: mix(self.seed ^ block.start ^ trial.rotate_left(40)),
            pool,
            at: block.start,
            rsp: None,
            writers: FxHashMap::default(),
            lanes: FxHashMap::default(),
            names: FxHashMap::default(),
            slot_bits: &w.slot_bits,
            reg_ty: &w.reg_ty,
            flag_setters: flag_setters(code),
        };
        for &(_, r) in self.regs {
            let k = Key::Reg(r);
            let mut v = text.drawn(k);
            if !inn.vals.contains_key(&k)
                && let Some(nb) = inn.narrow.get(&k)
            {
                v &= low(*nb);
            }
            text.vars.insert(k, v);
        }
        // INVARIANT: a copy of a variable takes the variable's width only
        // when nothing was pending in it, so the width is the variable's
        // own text value's, which stays until the copy is written out,
        // whatever the variable holds pending since.
        for (k, e) in &inn.vals {
            if let (Expr::Var(src @ (Key::Reg(_) | Key::Tmp(_) | Key::Param(_))), Some(nb)) =
                (e, inn.narrow.get(k))
                && let Some(v) = text.var(*src)
            {
                text.vars.insert(*src, v & low(*nb));
            }
        }
        if let Some((k @ (Key::Reg(_) | Key::Tmp(_) | Key::Param(_)), c)) =
            w.assumes.get(b).copied().flatten()
        {
            text.vars.insert(k, c & mask);
        }
        // INVARIANT: a block entered from one branch's one side only runs
        // where the text's condition went that way. The lifter reads a bit
        // scan as defined (`bsr; xor 63` as `lzcnt`), as code scans only
        // what is not zero, while a scan of zero leaves its destination as
        // it was; so a block that scans is tried only from states its branch
        // lets in, moved across where the condition compares a variable
        // with a constant, and not tried where it cannot be.
        if code
            .iter()
            .any(|i| matches!(i.mnemonic(), Mnemonic::Bsf | Mnemonic::Bsr))
            && let Some((c, taken)) = self.guard(b)
            && text.cond(c) == Some(!taken)
            && !text.steer(c, taken, &inn.narrow)
        {
            return Err(RULED_OUT);
        }
        for &(name, r) in self.regs {
            let k = Key::Reg(r);
            let v = match inn.vals.get(&k) {
                Some(e) => match text.eval(e) {
                    Some(v) => v & low(inn.narrow.get(&k).copied().unwrap_or(64)),
                    None => text.drawn(k),
                },
                None => text.var(k).unwrap_or(0),
            };
            emu.set_register(name, v & mask);
        }
        // INVARIANT: an xmm register's variable is seeded the way a general
        // register's is: every one drawn first, into the low lane, the rest
        // zero, so a register-to-register `movss` that merges into the
        // destination keeps the same bits on both sides; a block that reads
        // whole lanes (a packed operation, a 128-bit move) draws the full
        // 128, which its packed statements carry. Then a pending value the
        // block's IN environment holds is evaluated over that drawn state
        // into the machine alone, the relation the block runs under: the
        // text's own lane keeps the drawn entry value, which the pending
        // expressions, built over entry variables, still read.
        let mut packed_info = InstructionInfoFactory::new();
        let whole = reads_whole_lanes(code, &mut packed_info);
        for (n, &x) in XMMS.iter().enumerate() {
            let k = Key::Reg(x);
            let lo = text.drawn(k);
            let v = if whole {
                u128::from(lo) | u128::from(mix(lo)) << 64
            } else {
                u128::from(lo)
            };
            text.vars.insert(k, lo);
            text.vecs.insert(k, v);
            emu.set_xmm(n, v);
        }
        for (n, &x) in XMMS.iter().enumerate() {
            let k = Key::Reg(x);
            let Some(e) = inn.vals.get(&k) else { continue };
            if let Some(v) = text.vec(e).or_else(|| text.eval(e).map(u128::from)) {
                emu.set_xmm(n, v);
            }
        }
        let mut pending = FxHashSet::default();
        for (k, e) in &inn.vals {
            let (at, n) = match k {
                Key::Slot(o) => match inn.slot_bits.get(o) {
                    Some(bits) => (sp0.wrapping_add_signed(*o), u64::from(*bits / 8).max(1)),
                    None => continue,
                },
                Key::Global(a, bits) if *a < TLS_BASE => (*a, u64::from(*bits / 8).max(1)),
                Key::Global(..) | Key::Reg(_) | Key::Tmp(_) | Key::Param(_) | Key::A64(_) => {
                    continue;
                }
            };
            let value = wide_value(&text, e, n);
            for i in 0..n {
                let a = at.wrapping_add(i) & mask;
                pending.insert(a);
                match value {
                    Some(v) => emu.poke(
                        a,
                        lo8(low64(
                            v.checked_shr(8 * u32::try_from(i).unwrap_or(u32::MAX))
                                .unwrap_or(0),
                        )),
                    ),
                    None => {
                        text.lost.insert(a);
                    }
                }
            }
        }
        emu.stop_at(Some(end.stop()));
        let run = emu.run(block.start);
        match run.stop {
            Stop::Stopped(at) if at == end.stop() => {}
            Stop::Unmodeled(_) => return Err("an instruction the emulator does not model"),
            Stop::Fault(_) => return Err("a fault on the emulator"),
            Stop::Budget => return Err("a repeat past the regions compared"),
            _ => return Err("the emulator stopped early"),
        }
        let written: FxHashSet<u64> = run.history.iter().map(|x| x.addr).collect();
        text.rsp = emu.register("rsp");
        // INVARIANT: a register's save and a push that only makes room store
        // no value of the text's: what they leave in the frame is no
        // variable's, and a statement reading it reads a variable never set.
        let defs = w.defs.get(b);
        for &x in &written {
            let off = x.wrapping_sub(sp0).cast_signed();
            let frame = (x.wrapping_sub(rsp).wrapping_add(FRAME_SPAN) & mask) < 2 * FRAME_SPAN;
            if frame
                && !pending.contains(&x)
                && defs.is_none_or(|d| covering(d, off).next().is_none())
            {
                text.lost.insert(x);
            }
        }
        let taken = match end {
            End::Branch(jcc) if jcc.near_branch_target() != jcc.next_ip() => {
                let mut step = emu.clone();
                step.set_budget(1);
                step.stop_at(Some(jcc.near_branch_target()));
                match step.run(jcc.ip()).stop {
                    Stop::Stopped(_) => Some(true),
                    Stop::Budget => Some(false),
                    _ => None,
                }
            }
            End::Branch(_) | End::Before(_) | End::Fall(_) => None,
        };
        let mut t = Trial {
            emu,
            text,
            rsp,
            written,
            pending,
            taken,
            called: false,
            settled: false,
            b,
            seen: std::mem::take(seen),
        };
        let start = block.start;
        for e in &self.effects[b] {
            self.replay_effect(&mut t, start, end, block, e, out);
        }
        // A condition the statements leave inside a pending value was set
        // by an instruction of an earlier block, which this block's flag
        // setters say nothing about.
        t.text.flag_setters = (Vec::new(), Vec::new());
        let last = end.last().map_or(start, |i| i.ip());
        t.called |= end.last().is_some_and(|i| {
            matches!(
                i.flow_control(),
                FlowControl::Call | FlowControl::IndirectCall
            )
        });
        if !t.called && !t.settled {
            self.memory(&mut t, start, last, b, out);
        }
        for &s in self.succs.get(b).map_or(&[][..], Vec::as_slice) {
            if w.processed.get(s).copied().unwrap_or(false) {
                self.successor(&mut t, start, last, s, out);
            }
        }
        *seen = t.seen;
        Ok(())
    }

    /// Replays one effect, comparing what it claims at its point.
    ///
    /// # Arguments
    ///
    /// * `t` - The state.
    /// * `start` - The block's start.
    /// * `end` - How the block ends.
    /// * `block` - The block.
    /// * `e` - The effect.
    /// * `out` - Where the counts and disagreements go.
    fn replay_effect(
        &self,
        t: &mut Trial<'_, '_>,
        start: u64,
        end: End,
        block: &BasicBlock,
        e: &Effect,
        out: &mut Replayed,
    ) {
        t.text.at = e.at;
        match &e.kind {
            EffectKind::Assign(k, v, bits) => t.text.assign(*k, v, *bits),
            EffectKind::Store(s) => t.text.store(&s.0, s.1, &s.2),
            EffectKind::Call(c) => {
                if let Callee::Builtin(routine, bits) = c.callee {
                    t.text.routine(routine, bits, &c.args);
                    return;
                }
                let Some(instr) = end.last() else { return };
                if let Callee::Through(target) = &c.callee {
                    let machine = match operand(&t.emu, &instr, self.width) {
                        Some(to) => match self.w.dispatches.get(&to) {
                            Some(r) => reg_value(&t.emu, *r, self.width),
                            None => Some(to),
                        },
                        None => None,
                    };
                    if let Some(m) = machine {
                        let text = t.text.eval(target);
                        self.compare(
                            t,
                            out,
                            start,
                            e.at,
                            Claim::Target,
                            "callee".to_owned(),
                            text,
                            m,
                            self.width,
                            false,
                            || format!("{target:?}"),
                        );
                    }
                }
                let rsp_now = t.emu.register("rsp").unwrap_or(t.rsp);
                for (at, arg) in &c.args {
                    let (machine, stored) = match at {
                        ArgAt::Reg(r) if r.is_gpr() => (reg_value(&t.emu, *r, self.width), 64),
                        ArgAt::Stack(off, bits) => (
                            machine_word(
                                &t.emu,
                                rsp_now.wrapping_add_signed(*off),
                                u64::from(self.width / 8),
                                self.width,
                            ),
                            *bits,
                        ),
                        ArgAt::Reg(_) | ArgAt::Operand => (None, 64),
                    };
                    let Some(m) = machine else { continue };
                    let bits = value_lane(arg, self.width).min(stored.max(8));
                    let text = t.text.eval(arg);
                    self.compare(
                        t,
                        out,
                        start,
                        e.at,
                        Claim::Argument,
                        format!("{at:?}"),
                        text,
                        m,
                        bits,
                        false,
                        || format!("{arg:?}"),
                    );
                }
                self.memory(t, start, e.at, usize::MAX, out);
                t.settled = true;
                t.called = true;
                t.text.lost_all = true;
                for r in self.w.conv.volatile {
                    t.text.unknown.insert(Key::Reg(*r));
                }
                if let Some(k) = c.result {
                    t.text.unknown.insert(k);
                }
                if let Some(k) = c.result2 {
                    t.text.unknown.insert(k);
                }
            }
            EffectKind::Return(v) => {
                if let Some(v) = v
                    && !self.w.ret_float
                {
                    let bits = match self.w.ret_bits {
                        b @ (8 | 16 | 32) => b,
                        _ => self.width,
                    }
                    .min(value_lane(v, self.width));
                    if let Some(m) = self.regs.first().and_then(|(n, _)| t.emu.register(n)) {
                        let text = t.text.eval(v);
                        self.compare(
                            t,
                            out,
                            start,
                            e.at,
                            Claim::Return,
                            "result".to_owned(),
                            text,
                            m,
                            bits,
                            false,
                            || format!("{v:?}"),
                        );
                    }
                }
                // INVARIANT: a float result is the low lane of `xmm0`, at the
                // width its expression computes, the whole low quadword where
                // it names none; one left on the x87 stack is not compared.
                if let Some(v) = v
                    && self.w.ret_xmm
                {
                    let float = t.text.float_bits(v);
                    let bits = float.unwrap_or(64);
                    let machine = low64(t.emu.xmm().first().copied().unwrap_or(0)) & low(bits);
                    let text = t.text.eval(v);
                    self.compare(
                        t,
                        out,
                        start,
                        e.at,
                        Claim::Return,
                        "result".to_owned(),
                        text,
                        machine,
                        bits,
                        float.is_some(),
                        || format!("{v:?}"),
                    );
                }
                self.memory(t, start, e.at, usize::MAX, out);
                t.settled = true;
            }
            EffectKind::Branch(c) => {
                let text = t.text.cond(c).map(u64::from);
                match t.taken {
                    Some(m) => self.compare(
                        t,
                        out,
                        start,
                        e.at,
                        Claim::Branch,
                        format!("{:#x}", e.at),
                        text,
                        u64::from(m),
                        1,
                        false,
                        || format!("{c:?}"),
                    ),
                    None => *out.unreadable.entry(Claim::Branch).or_default() += 1,
                }
            }
            EffectKind::Switch(idx) => {
                let Some(jmp) = end.last() else { return };
                let Some(m) = operand(&t.emu, &jmp, self.width) else {
                    return;
                };
                // INVARIANT: the text switches on what the structurer renders:
                // the index without its sign extension.
                let shown = match idx {
                    Expr::Sext(e, _) => e.as_ref(),
                    other => other,
                };
                let text = t
                    .text
                    .eval(shown)
                    .and_then(|k| table_target(self.analysis, block, k));
                self.compare(
                    t,
                    out,
                    start,
                    e.at,
                    Claim::Switch,
                    "arm".to_owned(),
                    text,
                    m,
                    self.width,
                    false,
                    || format!("{shown:?}"),
                );
            }
            EffectKind::Jump(target) => {
                let Some(jmp) = end.last() else { return };
                let Some(m) = operand(&t.emu, &jmp, self.width) else {
                    return;
                };
                let text = t.text.eval(target);
                self.compare(
                    t,
                    out,
                    start,
                    e.at,
                    Claim::Target,
                    "goto".to_owned(),
                    text,
                    m,
                    self.width,
                    false,
                    || format!("{target:?}"),
                );
            }
            EffectKind::Unmodeled => {}
        }
    }

    /// Compares memory off the frame: every byte either side wrote, or the
    /// block started with a pending value for, must agree, but for values
    /// still pending at a successor.
    ///
    /// # Arguments
    ///
    /// * `t` - The state.
    /// * `start` - The block's start.
    /// * `at` - The statement or instruction compared at.
    /// * `b` - The block's index, whose successors' pending globals are
    ///   left out; `usize::MAX` at a call or a return, where none may be.
    /// * `out` - Where the counts and disagreements go.
    fn memory(&self, t: &mut Trial<'_, '_>, start: u64, at: u64, b: usize, out: &mut Replayed) {
        let mask = low(self.width);
        // INVARIANT: in 32-bit code an address past the low four gigabytes
        // is one the emulator reached without the wrap the processor makes,
        // so what it wrote there has no place to compare.
        if t.text.lost_all || t.written.iter().any(|x| *x > mask) {
            *out.unreadable.entry(Claim::Memory).or_default() += 1;
            return;
        }
        let now = t.emu.register("rsp").unwrap_or(t.rsp);
        let frame = |x: u64| {
            [t.rsp, now, t.text.sp0]
                .iter()
                .any(|sp| (x.wrapping_sub(*sp).wrapping_add(FRAME_SPAN) & mask) < 2 * FRAME_SPAN)
        };
        let mut kept: FxHashSet<u64> = FxHashSet::default();
        // INVARIANT: the try level at `[ebp-4]` is the compiler's
        // bookkeeping, which the text leaves out on purpose.
        let bitness = u32::from(self.width);
        if self.w.seh_frame
            && self
                .code
                .get(t.b)
                .is_some_and(|c| c.iter().any(|i| try_level_store(i, bitness)))
            && let Some(ebp) = reg_value(&t.emu, Register::EBP, self.width)
        {
            kept.extend((1..=4).map(|i| ebp.wrapping_sub(i) & mask));
        }
        for &s in self.succs.get(b).map_or(&[][..], Vec::as_slice) {
            for k in self
                .w
                .ins
                .get(s)
                .map_or(&BTreeMap::new(), |e| &e.vals)
                .keys()
            {
                if let Key::Global(a, bits) = *k {
                    kept.extend((0..u64::from(bits / 8).max(1)).map(|i| a.wrapping_add(i) & mask));
                }
            }
        }
        let mut addrs: Vec<u64> = t
            .written
            .iter()
            .chain(t.text.mem.keys())
            .chain(t.pending.iter())
            .copied()
            .filter(|x| !frame(*x) && !kept.contains(x) && !t.text.lost.contains(x))
            .collect();
        addrs.sort_unstable();
        addrs.dedup();
        if addrs.is_empty() {
            return;
        }
        *out.compared.entry(Claim::Memory).or_default() += 1;
        let differ: Vec<(u64, u8, u8)> = addrs
            .iter()
            .filter_map(|&x| {
                let m = t.emu.byte_at(x)?;
                let tv = t.text.byte(x)?;
                (m != tv).then_some((x, tv, m))
            })
            .collect();
        if let Some(&(x, tv, m)) = differ.first()
            && t.seen.insert((Claim::Memory, String::new()))
        {
            let writer = t.text.writers.get(&x).copied();
            let lane = differ
                .iter()
                .all(|(x, ..)| t.text.lanes.get(x).is_some_and(|&(i, n)| n == 8 && i >= 4));
            let statement = writer
                .and_then(|w| {
                    self.effects
                        .get(t.b)
                        .and_then(|es| es.iter().rev().find(|e| e.at == w))
                })
                .map_or_else(
                    || "no statement wrote it".to_owned(),
                    |e| format!("{:?}", e.kind),
                );
            out.disagreements.push(Disagreement {
                function: self.entry,
                block: start,
                at: writer.unwrap_or(at),
                claim: Claim::Memory,
                place: format!("{x:#x}"),
                text: u64::from(tv),
                machine: u64::from(m),
                bits: 8,
                lane,
                expr: format!(
                    "{} of {} bytes differ; {statement}",
                    differ.len(),
                    addrs.len()
                ),
            });
        }
    }

    /// Checks the relation at a successor: each register it reads, each
    /// pending or named slot it reads, and the stack pointer; after a call
    /// only the registers the callee keeps.
    ///
    /// # Arguments
    ///
    /// * `t` - The state at the block's end.
    /// * `start` - The block's start.
    /// * `at` - The block's last instruction.
    /// * `s` - The successor's index.
    /// * `out` - Where the counts and disagreements go.
    fn successor(&self, t: &mut Trial<'_, '_>, start: u64, at: u64, s: usize, out: &mut Replayed) {
        let w = self.w;
        let Some(sin) = w.ins.get(s) else { return };
        let succ = self
            .code
            .get(s)
            .and_then(|c| c.first())
            .map_or(0, Instruction::ip);
        let mask = low(self.width);
        for &(name, r) in self.regs {
            let k = Key::Reg(r);
            let Some(&need) = w.live.regs.get(s).and_then(|m| m.get(&k)) else {
                continue;
            };
            if t.called && w.conv.volatile.contains(&r) {
                continue;
            }
            let Some(m) = t.emu.register(name) else {
                continue;
            };
            let (text, at) = match sin.vals.get(&k) {
                Some(e) => (t.text.eval(e), at),
                None => (
                    t.text.var(k),
                    t.text.writers.get(&key_spot(k)).copied().unwrap_or(at),
                ),
            };
            let narrow = sin.narrow.get(&k).copied();
            let mut bits = need.min(self.width);
            if let Some(nb) = narrow {
                bits = bits.min(nb).max(8);
            }
            if let (Some(nb), Some(v), false) = (narrow, text, sin.vals.contains_key(&k))
                && nb < 32
                && v >> nb != 0
            {
                self.compare(
                    t,
                    out,
                    start,
                    at,
                    Claim::Narrow,
                    format!("{name} at {succ:#x}"),
                    Some(v),
                    v & low(nb),
                    64,
                    false,
                    || format!("{nb} bits"),
                );
            }
            self.compare(
                t,
                out,
                start,
                at,
                Claim::Register,
                format!("{name} at {succ:#x}"),
                text,
                m,
                bits,
                false,
                || {
                    sin.vals
                        .get(&k)
                        .map_or_else(|| "(its own variable)".to_owned(), |e| format!("{e:?}"))
                },
            );
        }
        for (n, &x) in XMMS.iter().enumerate() {
            let k = Key::Reg(x);
            if w.live.regs.get(s).and_then(|m| m.get(&k)).is_none() {
                continue;
            }
            if t.called && w.conv.volatile.contains(&x) {
                continue;
            }
            let held = sin.vals.get(&k);
            let float = held.and_then(|e| t.text.float_bits(e));
            let narrow = sin.narrow.get(&k).copied();
            let shown = held.map_or_else(|| "(its own variable)".to_owned(), |e| format!("{e:?}"));
            let (text, at) = match held {
                Some(e) => (t.text.eval(e), at),
                None => (
                    t.text.var(k),
                    t.text.writers.get(&key_spot(k)).copied().unwrap_or(at),
                ),
            };
            // INVARIANT: an integer the text holds by its whole lane (a
            // packed statement's value, or the register's own state after
            // one) is compared whole, both halves: the machine's register
            // and the text's lane were seeded and written together. A lane
            // the whole-lane state does not hold falls back to the low one
            // the scalar model keeps.
            if float.is_none() {
                let whole = match held {
                    Some(e) => t.text.vec(e),
                    None => t.text.vec_var(k),
                };
                if let Some(v) = whole {
                    let machine = t.emu.xmm()[n];
                    if let Some(nb) = narrow {
                        self.compare(
                            t,
                            out,
                            start,
                            at,
                            Claim::Register,
                            format!("xmm{n} at {succ:#x}"),
                            Some(low64(v)),
                            low64(machine),
                            nb,
                            false,
                            || shown.clone(),
                        );
                        continue;
                    }
                    self.compare(
                        t,
                        out,
                        start,
                        at,
                        Claim::Register,
                        format!("xmm{n} at {succ:#x}"),
                        Some(low64(v)),
                        low64(machine),
                        64,
                        false,
                        || shown.clone(),
                    );
                    self.compare(
                        t,
                        out,
                        start,
                        at,
                        Claim::Register,
                        format!("xmm{n}+8 at {succ:#x}"),
                        Some(low64(v >> 64)),
                        low64(machine >> 64),
                        64,
                        false,
                        || shown.clone(),
                    );
                    continue;
                }
            }
            // INVARIANT: a float's lane is the width its expression computes
            // at, an integer's the whole low lane the text's variable names,
            // narrowed where the successor reads it narrower; a lane above
            // the low 64 bits is a packed read the scalar model stays out
            // of, compared nowhere.
            let bits = float.or(narrow).unwrap_or(64).min(64);
            #[expect(
                clippy::cast_possible_truncation,
                reason = "the lane is masked to the compared width first, so the cast drops no bit"
            )]
            let machine = (t.emu.xmm()[n] & u128::from(low(bits))) as u64;
            self.compare(
                t,
                out,
                start,
                at,
                Claim::Register,
                format!("xmm{n} at {succ:#x}"),
                text,
                machine,
                bits,
                float.is_some(),
                || shown,
            );
        }
        if t.called {
            return;
        }
        // INVARIANT: a store the text cannot place may have landed on any
        // slot, so no slot's bytes can be held against the text's.
        if t.text.lost_all {
            *out.unreadable.entry(Claim::Slot).or_default() += 1;
            return;
        }
        let mut covered: Vec<(u64, u64)> = Vec::new();
        for (k, e) in &sin.vals {
            let Key::Slot(o) = k else { continue };
            let Some(&bits) = sin.slot_bits.get(o) else {
                continue;
            };
            let a = t.text.sp0.wrapping_add_signed(*o) & mask;
            let n = u64::from(bits / 8).max(1);
            covered.push((a, n));
            if !w.live.is_live(s, *k) {
                continue;
            }
            // INVARIANT: a wider value pending is compared a word at a
            // time, a whole vector lane word by word where the replay
            // knows it.
            if bits > 64 {
                let Some(w) = wide_value(&t.text, e, n) else {
                    continue;
                };
                for word in (0..n).step_by(8) {
                    let Some(m) = machine_word(&t.emu, a.wrapping_add(word) & mask, 8, self.width)
                    else {
                        continue;
                    };
                    self.compare(
                        t,
                        out,
                        start,
                        at,
                        Claim::Slot,
                        format!("{:+#x} at {succ:#x}", o.wrapping_add_unsigned(word)),
                        Some(low64(w >> (8 * word))),
                        m,
                        64,
                        false,
                        || format!("{e:?}"),
                    );
                }
                continue;
            }
            let Some(m) = machine_word(&t.emu, a, n, self.width) else {
                continue;
            };
            let text = t.text.eval(e);
            self.compare(
                t,
                out,
                start,
                at,
                Claim::Slot,
                format!("{o:+#x} at {succ:#x}"),
                text,
                m,
                bits,
                false,
                || format!("{e:?}"),
            );
        }
        // INVARIANT: a byte only the machine wrote is the text's claim only
        // where the lifter stores a value the successor still reads: a
        // register's save and a push that only makes room store none, and a
        // store the successor overwrites first is dead whatever wider slot
        // shares its bytes. A byte below the successor's stack pointer is no
        // slot's any more.
        let defs = w.defs.get(t.b);
        let defined = |off: i64| {
            defs.is_some_and(|d| covering(d, off).any(|d| w.live.is_live(s, Key::Slot(d))))
        };
        // INVARIANT: a store pending at the block's start that the edge
        // drops is dead where the successor's statements overwrite its
        // bytes before anything may read them, even where a wider slot the
        // successor reads later shares them, and where no read from the
        // successor on reaches its slot, a read of any of its bytes making
        // the slot live.
        let next = self.effects.get(s).map_or(&[][..], Vec::as_slice);
        let inn = &w.ins[t.b];
        let sp0 = t.text.sp0;
        let pending_live = |x: u64| {
            inn.slot_bits.iter().any(|(&p, &bits)| {
                let lo = sp0.wrapping_add_signed(p) & mask;
                x.wrapping_sub(lo) & mask < u64::from(bits / 8).max(1)
                    && inn.vals.contains_key(&Key::Slot(p))
                    && w.live.is_live(s, Key::Slot(p))
            })
        };
        let floor = sin.sp.unwrap_or(i64::MIN);
        for (&o, &n) in self.named {
            if !w.live.is_live(s, Key::Slot(o)) {
                continue;
            }
            let a = t.text.sp0.wrapping_add_signed(o) & mask;
            let bytes: Vec<u64> = (0i64..)
                .zip(0..n)
                .map(|(i, _)| (o + i, a.wrapping_add_signed(i) & mask))
                .filter(|&(off, x)| {
                    let text = t.text.mem.contains_key(&x)
                        || (t.pending.contains(&x)
                            && !overwritten_first(next, off)
                            && pending_live(x));
                    off >= floor
                        && (text || (t.written.contains(&x) && defined(off)))
                        && !covered
                            .iter()
                            .any(|&(c, len)| x.wrapping_sub(c) & mask < len)
                })
                .map(|(_, x)| x)
                .collect();
            if bytes.is_empty() {
                continue;
            }
            let pairs: Option<Vec<(u8, u8)>> = bytes
                .iter()
                .map(|&x| Some((t.text.byte(x)?, t.emu.byte_at(x)?)))
                .collect();
            let place = format!("{o:+#x} at {succ:#x}");
            match pairs {
                None => *out.unreadable.entry(Claim::Slot).or_default() += 1,
                Some(pairs) => {
                    let first = bytes.iter().zip(&pairs).find(|(_, p)| p.0 != p.1);
                    let writer = first.and_then(|(x, _)| t.text.writers.get(x).copied());
                    let how = match first {
                        Some(_) if writer.is_some() => "the text wrote it".to_owned(),
                        Some((x, _)) if t.pending.contains(x) => {
                            let held = w.ins.get(t.b).and_then(|inn| {
                                inn.vals.iter().find(|(k, _)| match k {
                                    Key::Slot(p) => inn.slot_bits.get(p).is_some_and(|bits| {
                                        let lo = t.text.sp0.wrapping_add_signed(*p) & mask;
                                        x.wrapping_sub(lo) & mask < u64::from(*bits / 8).max(1)
                                    }),
                                    _ => false,
                                })
                            });
                            match held {
                                Some((k, e)) => format!(
                                    "pending at the block's start as {k:?} = {e:?}, not written"
                                ),
                                None => "pending at the block's start, not written".to_owned(),
                            }
                        }
                        Some(_) => "the machine wrote it, the text did not".to_owned(),
                        None => String::new(),
                    };
                    let at = writer.unwrap_or(at);
                    let tv = word(from_usize(pairs.len()), |i| {
                        pairs
                            .get(usize::try_from(i).unwrap_or(0))
                            .map_or(0, |p| p.0)
                    });
                    let mv = word(from_usize(pairs.len()), |i| {
                        pairs
                            .get(usize::try_from(i).unwrap_or(0))
                            .map_or(0, |p| p.1)
                    });
                    let bits = u8::try_from(pairs.len().min(8) * 8).unwrap_or(64);
                    self.compare(
                        t,
                        out,
                        start,
                        at,
                        Claim::Slot,
                        place,
                        Some(tv),
                        mv,
                        bits,
                        false,
                        || format!("(its own variable; {how})"),
                    );
                }
            }
        }
        if let (Some(ssp), Some(now)) = (sin.sp, t.emu.register("rsp")) {
            let expected = t.text.sp0.wrapping_add_signed(ssp) & mask;
            self.compare(
                t,
                out,
                start,
                at,
                Claim::StackPointer,
                format!("at {succ:#x}"),
                Some(expected),
                now,
                self.width,
                false,
                || format!("entry {ssp:+}"),
            );
        }
    }

    /// Compares one claim and records a disagreement, once per block, claim
    /// and place.
    ///
    /// # Arguments
    ///
    /// * `t` - The state, which remembers the block's disagreements.
    /// * `out` - Where the counts and disagreements go.
    /// * `start` - The block's start.
    /// * `at` - The statement's instruction.
    /// * `claim` - What kind of claim.
    /// * `place` - Which one.
    /// * `text` - What the text says, `None` when the replay cannot tell.
    /// * `machine` - What the machine holds.
    /// * `bits` - The width compared.
    /// * `float` - Whether the value is a float, whose NaNs agree
    ///   ([`agree`]).
    /// * `expr` - The text's expression, rendered only for a disagreement.
    #[expect(
        clippy::too_many_arguments,
        reason = "one claim's facts, as a row reports them"
    )]
    fn compare(
        &self,
        t: &mut Trial<'_, '_>,
        out: &mut Replayed,
        start: u64,
        at: u64,
        claim: Claim,
        place: String,
        text: Option<u64>,
        machine: u64,
        bits: u8,
        float: bool,
        expr: impl FnOnce() -> String,
    ) {
        let Some(tv) = text else {
            *out.unreadable.entry(claim).or_default() += 1;
            return;
        };
        *out.compared.entry(claim).or_default() += 1;
        if agree(tv, machine, bits, float) || !t.seen.insert((claim, place.clone())) {
            return;
        }
        out.disagreements.push(Disagreement {
            function: self.entry,
            block: start,
            at,
            claim,
            place,
            text: tv & low(bits),
            machine: machine & low(bits),
            bits,
            lane: claim == Claim::Narrow || (bits > 32 && (tv ^ machine) & low(32) == 0),
            expr: expr(),
        });
    }
}

#[cfg(test)]
#[expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]
mod tests {
    use crate::isa::x86::Register;

    use super::{Claim, Replayed, TextCheck, replay_effects, replay_function, replay_tsv};
    use crate::analysis::decompile::expr::{Expr, UnOp};
    use crate::analysis::decompile::lift::{ArgAt, Effect, EffectKind};
    use crate::analysis::decompile::{decompile, decompile_with};
    use crate::analysis::{Analysis, Overlay};
    use crate::emulate::Emulator;
    use crate::program::{Arch, Program};

    /// The claims the disagreements are about, in order, but for those
    /// of a lane only.
    fn claims(r: &Replayed) -> Vec<Claim> {
        r.wrong().iter().map(|d| d.claim).collect()
    }

    /// Replays a function's effects after `change` rewrote them.
    ///
    /// # Arguments
    ///
    /// * `p` - The image.
    /// * `entry` - The function.
    /// * `seed` - The states' seed.
    /// * `change` - Rewrites one effect.
    fn replayed_with(p: &Program, entry: u64, seed: u64, change: impl Fn(&mut Effect)) -> Replayed {
        let a = Analysis::compute(p);
        let f = a.function(entry).expect("function");
        let d = decompile_with(p, &a, &Overlay::default(), entry, true, &[], true).expect("text");
        let mut effects: Vec<Vec<Effect>> = f
            .blocks
            .iter()
            .enumerate()
            .map(|(i, b)| d.effects.block(i, b.start).expect("block"))
            .collect();
        effects.iter_mut().flatten().for_each(change);
        let template = Emulator::new(p, 0).expect("emulator");
        let w = d.take_witness().expect("witness");
        replay_effects(
            p,
            &a,
            &template,
            entry,
            seed,
            (&w, &d.live.succs),
            &effects,
            usize::MAX,
        )
    }

    /// Asserts that the text of the function at `entry` agrees with the
    /// emulator on the states of eight seeds, every block checked.
    ///
    /// # Arguments
    ///
    /// * `p` - The image.
    /// * `entry` - The function.
    fn agrees(p: &Program, entry: u64) {
        let a = Analysis::compute(p);
        let f = a.function(entry).expect("function");
        for seed in 1..=8 {
            let r = replay_function(p, &a, entry, seed);
            assert_eq!(claims(&r), [], "seed {seed}: {}", replay_tsv(&r));
            assert_eq!(r.checked, f.blocks.len(), "seed {seed}: {}", replay_tsv(&r));
        }
    }

    /// A value parked in a temporary while a reader of its variable was
    /// written out is written from the temporary.
    ///
    /// Before the call, `rbx = (rax + rbx) * 100` is written out, and first
    /// `rax = rax + rbx`, which reads `rbx`; that parks `rbx`'s value, which
    /// reads `rax`, in `tmp_1`. Writing the value read before all this
    /// gave `rax += rbx; rbx = (rax + rbx) * 100;`, which adds `rbx` twice.
    #[test]
    fn a_value_parked_for_its_reader_is_written_from_its_temporary() {
        let mut code = vec![
            0x53, // ASM: push rbx
            0x48, 0x83, 0xec, 0x20, // ASM: sub rsp, 0x20
            0x8b, 0x19, // ASM: mov ebx, [rcx]
            0xe8, 0xf4, 0x00, 0x00, 0x00, // ASM: call 0x1100
            0x01, 0xd8, // ASM: add eax, ebx
            0x6b, 0xd8, 0x64, // ASM: imul ebx, eax, 100
            0xba, 0x02, 0x00, 0x00, 0x00, // ASM: mov edx, 2
            0xb9, 0x07, 0x00, 0x00, 0x00, // ASM: mov ecx, 7
            0xe8, 0xf0, 0x00, 0x00, 0x00, // ASM: call 0x1110
            0x01, 0xd8, // ASM: add eax, ebx
            0x48, 0x83, 0xc4, 0x20, // ASM: add rsp, 0x20
            0x5b, // ASM: pop rbx
            0xc3, // ASM: ret
        ];
        code.resize(0x100, 0xcc);
        code.extend([
            0xb8, 0x05, 0x00, 0x00, 0x00, // ASM: mov eax, 5
            0xc3, // ASM: ret
        ]);
        code.resize(0x110, 0xcc);
        code.extend([
            0x8d, 0x04, 0x11, // ASM: lea eax, [rcx+rdx]
            0xc3, // ASM: ret
        ]);
        agrees(&Program::raw_x64(&code), 0x1000);
    }

    /// An argument holding a dead register's value passes that value, not
    /// the register: the register is not written out.
    ///
    /// `cmovne rbx, rax; mov rdx, rbx` passes the selection in `rdx`, and
    /// `rbx` is restored after the call. The argument was rewritten to read
    /// `rbx`, whose value was then dropped as dead, so the call passed the
    /// `rbx` from before the selection: `sub_1100(7, rbx)`.
    #[test]
    fn an_argument_holding_a_dead_register_s_value_passes_the_value() {
        let mut code = vec![
            0x53, // ASM: push rbx
            0x48, 0x83, 0xec, 0x20, // ASM: sub rsp, 0x20
            0xe8, 0x06, 0x01, 0x00, 0x00, // ASM: call 0x1110
            0x48, 0x89, 0xc3, // ASM: mov rbx, rax
            0xe8, 0xfe, 0x00, 0x00, 0x00, // ASM: call 0x1110
            0x48, 0x8b, 0x43, 0x30, // ASM: mov rax, [rbx+0x30]
            0x48, 0x85, 0xc0, // ASM: test rax, rax
            0x48, 0x0f, 0x45, 0xd8, // ASM: cmovne rbx, rax
            0x48, 0x89, 0xda, // ASM: mov rdx, rbx
            0xb9, 0x07, 0x00, 0x00, 0x00, // ASM: mov ecx, 7
            0xe8, 0xd6, 0x00, 0x00, 0x00, // ASM: call 0x1100
            0x48, 0x83, 0xc4, 0x20, // ASM: add rsp, 0x20
            0x5b, // ASM: pop rbx
            0xc3, // ASM: ret
        ];
        code.resize(0x100, 0xcc);
        code.extend([
            0x48, 0x8d, 0x04, 0x11, // ASM: lea rax, [rcx+rdx]
            0xc3, // ASM: ret
        ]);
        code.resize(0x110, 0xcc);
        code.extend([
            0x8b, 0x01, // ASM: mov eax, [rcx]
            0xc3, // ASM: ret
        ]);
        agrees(&Program::raw_x64(&code), 0x1000);
    }

    /// A 32-bit image of `code` at `0x1000`.
    ///
    /// # Arguments
    ///
    /// * `code` - The bytes.
    fn x86(code: &[u8]) -> Program {
        let mut p = Program::raw_x64(code);
        p.arch = Arch::X86;
        p.is_64 = false;
        p
    }

    /// Both halves of a widening multiply are computed from the operands
    /// as they were before either is written.
    ///
    /// The second `imul` writes `edx` out early for its size, and first
    /// `eax = ebx`, which reads the old `edx`; `eax`'s new value, held
    /// aside meanwhile, read `edx` too and so named the new one:
    /// `edx = smulhi32(x, y); eax = x * y;` with `x` reading `edx`.
    #[test]
    fn a_widening_multiply_reads_its_operands_before_either_half_is_written() {
        let code = [
            0x55, // ASM: push ebp
            0x8b, 0xec, // ASM: mov ebp, esp
            0x83, 0xec, 0x18, // ASM: sub esp, 0x18
            0x53, // ASM: push ebx
            0x57, // ASM: push edi
            0x8b, 0x4d, 0x08, // ASM: mov ecx, [ebp+8]
            0x8b, 0x55, 0x0c, // ASM: mov edx, [ebp+0xc]
            0x8b, 0x45, 0xf0, // ASM: mov eax, [ebp-0x10]
            0x8b, 0x5d, 0x08, // ASM: mov ebx, [ebp+8]
            0x8b, 0x5b, 0x0c, // ASM: mov ebx, [ebx+0xc]
            0x8b, 0x0c, 0x88, // ASM: mov ecx, [eax+ecx*4]
            0x8b, 0x04, 0x88, // ASM: mov eax, [eax+ecx*4]
            0x03, 0xc0, // ASM: add eax, eax
            0x8b, 0x54, 0xc2, 0x08, // ASM: mov edx, [edx+eax*8+8]
            0x8b, 0x04, 0xd3, // ASM: mov eax, [ebx+edx*8]
            0x2b, 0x45, 0x10, // ASM: sub eax, [ebp+0x10]
            0x8b, 0x5c, 0xd3, 0x04, // ASM: mov ebx, [ebx+edx*8+4]
            0xf7, 0x6d, 0x1c, // ASM: imul dword [ebp+0x1c]
            0x2b, 0x5d, 0x14, // ASM: sub ebx, [ebp+0x14]
            0x89, 0x45, 0xf8, // ASM: mov [ebp-8], eax
            0x8b, 0xfa, // ASM: mov edi, edx
            0x8b, 0xc3, // ASM: mov eax, ebx
            0xf7, 0x6d, 0x18, // ASM: imul dword [ebp+0x18]
            0x3b, 0xfa, // ASM: cmp edi, edx
            0x7c, 0x04, // ASM: jl 0x1045
            0x5f, // ASM: pop edi
            0x5b, // ASM: pop ebx
            0xc9, // ASM: leave
            0xc3, // ASM: ret
            0xb8, 0x01, 0x00, 0x00, 0x00, // ASM: mov eax, 1
            0x5f, // ASM: pop edi
            0x5b, // ASM: pop ebx
            0xc9, // ASM: leave
            0xc3, // ASM: ret
        ];
        agrees(&x86(&code), 0x1000);
    }

    /// A call's arguments read what the variables hold once the call has
    /// written out what it must, not what they held before.
    ///
    /// The counter whose address escaped is stored back before the call,
    /// which may read it; the argument, computed from the counter before
    /// the increment, was rendered before that store and so read the new
    /// count: `local_28 += 1; sub_1110(a1 + (local_28 << 6));`.
    #[test]
    fn an_argument_reads_the_slot_as_it_was_before_the_call_stores_it() {
        let mut code = vec![
            0x55, // ASM: push rbp
            0x48, 0x83, 0xec, 0x50, // ASM: sub rsp, 0x50
            0x48, 0x8d, 0x6c, 0x24, 0x50, // ASM: lea rbp, [rsp+0x50]
            0x48, 0x89, 0x4d, 0xd8, // ASM: mov [rbp-0x28], rcx
            0x48, 0x8d, 0x4d, 0xe0, // ASM: lea rcx, [rbp-0x20]
            0xe8, 0xe9, 0x00, 0x00, 0x00, // ASM: call 0x1100
            0x48, 0x8b, 0x45, 0xe0, // ASM: mov rax, [rbp-0x20]
            0x48, 0x8b, 0x4d, 0xd8, // ASM: mov rcx, [rbp-0x28]
            0x48, 0x89, 0xc2, // ASM: mov rdx, rax
            0x48, 0xc1, 0xe2, 0x06, // ASM: shl rdx, 6
            0x48, 0x01, 0xd1, // ASM: add rcx, rdx
            0x48, 0xff, 0xc0, // ASM: inc rax
            0x48, 0x89, 0x45, 0xe0, // ASM: mov [rbp-0x20], rax
            0xe8, 0xdb, 0x00, 0x00, 0x00, // ASM: call 0x1110
            0x48, 0x8b, 0x45, 0xe0, // ASM: mov rax, [rbp-0x20]
            0x48, 0x83, 0xc4, 0x50, // ASM: add rsp, 0x50
            0x5d, // ASM: pop rbp
            0xc3, // ASM: ret
        ];
        code.resize(0x100, 0xcc);
        code.extend([
            0x48, 0xc7, 0x01, 0x00, 0x00, 0x00, 0x00, // ASM: mov qword [rcx], 0
            0xc3, // ASM: ret
        ]);
        code.resize(0x110, 0xcc);
        code.extend([
            0x48, 0x8d, 0x41, 0x01, // ASM: lea rax, [rcx+1]
            0xc3, // ASM: ret
        ]);
        agrees(&Program::raw_x64(&code), 0x1000);
    }

    /// An argument register the callee keeps is written out before the call
    /// when its value reads memory, and the call then passes it by name.
    ///
    /// `movzx r9d, word [r9+4]` before a call that leaves `r9` alone is
    /// written out, the callee being free to change the memory it read;
    /// the arguments, rendered before that, read the new `r9`: `r9 =
    /// *(uint16_t*)(r9 + 4); sub_1100(.., *(uint16_t*)(r9 + 4), ..)`.
    #[test]
    fn an_argument_the_callee_keeps_is_passed_as_written_out() {
        let mut code = vec![
            0x53, // ASM: push rbx
            0x48, 0x83, 0xec, 0x30, // ASM: sub rsp, 0x30
            0x48, 0x89, 0xcb, // ASM: mov rbx, rcx
            0x85, 0xd2, // ASM: test edx, edx
            0x74, 0x03, // ASM: je 0x100f
            0x49, 0x89, 0xc9, // ASM: mov r9, rcx
            0x41, 0x0f, 0xb7, 0x41, 0x06, // ASM: movzx eax, word [r9+6]
            0x45, 0x0f, 0xb7, 0x49, 0x04, // ASM: movzx r9d, word [r9+4]
            0x66, 0x89, 0x44, 0x24, 0x20, // ASM: mov [rsp+0x20], ax
            0xe8, 0xdd, 0x00, 0x00, 0x00, // ASM: call 0x1100
            0x44, 0x01, 0xc8, // ASM: add eax, r9d
            0x01, 0xd8, // ASM: add eax, ebx
            0x48, 0x83, 0xc4, 0x30, // ASM: add rsp, 0x30
            0x5b, // ASM: pop rbx
            0xc3, // ASM: ret
        ];
        code.resize(0x100, 0xcc);
        code.extend([
            0x44, 0x89, 0xc8, // ASM: mov eax, r9d
            0x03, 0x44, 0x24, 0x28, // ASM: add eax, [rsp+0x28]
            0x01, 0xc8, // ASM: add eax, ecx
            0x01, 0xd0, // ASM: add eax, edx
            0x44, 0x01, 0xc0, // ASM: add eax, r8d
            0xc3, // ASM: ret
        ]);
        agrees(&Program::raw_x64(&code), 0x1000);
    }

    /// A call through a register calls what the register holds when a
    /// write-out before the call protects the readers of a variable the
    /// target was loaded through.
    ///
    /// `mov eax, [esi+0x1ac]; ...; mov dword [ebp+8], 0; mov eax, [eax+4];
    /// call eax` with `&a1` pushed: the store to the escaped `a1` is written
    /// out before the call, and `eax`, which read the old `a1`, was dropped
    /// as a register nothing reads after the call: `(*eax)(..)` called a
    /// register the text never set.
    #[test]
    fn a_call_through_a_register_keeps_the_register_s_value() {
        let code = [
            0x55, // ASM: push ebp
            0x8b, 0xec, // ASM: mov ebp, esp
            0x56, // ASM: push esi
            0x8b, 0x75, 0x08, // ASM: mov esi, [ebp+8]
            0x8b, 0x86, 0xac, 0x01, 0x00, 0x00, // ASM: mov eax, [esi+0x1ac]
            0x8d, 0x4d, 0x08, // ASM: lea ecx, [ebp+8]
            0x51, // ASM: push ecx
            0xc7, 0x45, 0x08, 0x00, 0x00, 0x00, 0x00, // ASM: mov dword [ebp+8], 0
            0x8b, 0x40, 0x04, // ASM: mov eax, [eax+4]
            0x56, // ASM: push esi
            0xff, 0xd0, // ASM: call eax
            0x83, 0xc4, 0x08, // ASM: add esp, 8
            0x8b, 0x45, 0x08, // ASM: mov eax, [ebp+8]
            0x5e, // ASM: pop esi
            0x5d, // ASM: pop ebp
            0xc3, // ASM: ret
        ];
        agrees(&x86(&code), 0x1000);
    }

    /// A value the dataflow held in one of its own temporaries does not
    /// reach a successor: the emission numbers its temporaries apart, so
    /// the successor would read a variable the text never sets.
    ///
    /// `xchg [rcx], al` parks the byte it reads in a temporary; both
    /// successors of the compare on it read `al`, and the one that stores
    /// it wrote `*(uint8_t*)rdx = tmp_1073741825;`.
    #[test]
    fn a_dataflow_temporary_stays_in_its_block() {
        let code = [
            0x31, 0xc0, // ASM: xor eax, eax
            0x86, 0x01, // ASM: xchg [rcx], al
            0x3c, 0x02, // ASM: cmp al, 2
            0x75, 0x03, // ASM: jne 0x100b
            0x88, 0x02, // ASM: mov [rdx], al
            0xc3, // ASM: ret
            0xfe, 0xc0, // ASM: inc al
            0xc3, // ASM: ret
        ];
        agrees(&Program::raw_x64(&code), 0x1000);
    }

    /// A store a successor reads part of through another offset is written
    /// out on the edge, not dropped as dead.
    ///
    /// The dword stored at `[rsp+8]` is read back as its top byte, at
    /// `[rsp+0xb]`, where three paths meet; slot liveness by offset saw no
    /// read of `[rsp+8]` there and dropped the store, still pending, on the
    /// two paths that skip the byte stores over it.
    #[test]
    fn a_store_read_through_another_offset_reaches_the_reader() {
        let code = [
            0xc7, 0x44, 0x24, 0x08, 0x00, 0x00, 0x00, 0x00, // ASM: mov dword [rsp+8], 0
            0x85, 0xc9, // ASM: test ecx, ecx
            0x74, 0x0e, // ASM: je 0x101a
            0x85, 0xd2, // ASM: test edx, edx
            0x74, 0x0a, // ASM: je 0x101a
            0xc6, 0x44, 0x24, 0x08, 0x01, // ASM: mov byte [rsp+8], 1
            0xc6, 0x44, 0x24, 0x0b, 0x02, // ASM: mov byte [rsp+0xb], 2
            0x0f, 0xb6, 0x44, 0x24, 0x0b, // ASM: movzx eax, byte [rsp+0xb]
            0xc3, // ASM: ret
        ];
        agrees(&Program::raw_x64(&code), 0x1000);
    }

    /// A bit count or byte swap of a 32-bit register counts or swaps 32
    /// bits, whatever the 64-bit variable holding it holds above them.
    ///
    /// `mov eax, 0x3f; bsr eax, ecx; xor eax, 0x1f` is the leading zeros of
    /// `ecx`, and `bswap eax` after `mov eax, ecx` swaps its four bytes; both
    /// read `rcx` whole: `lzcnt(a1)` counted from bit 63, `bswap(a1)` swapped
    /// eight bytes.
    #[test]
    fn a_count_or_swap_of_a_32_bit_register_works_on_32_bits() {
        let code = [
            0xb8, 0x3f, 0x00, 0x00, 0x00, // ASM: mov eax, 0x3f
            0x0f, 0xbd, 0xc1, // ASM: bsr eax, ecx
            0x83, 0xf0, 0x1f, // ASM: xor eax, 0x1f
            0x89, 0x02, // ASM: mov [rdx], eax
            0x89, 0xc8, // ASM: mov eax, ecx
            0x0f, 0xc8, // ASM: bswap eax
            0x89, 0x42, 0x04, // ASM: mov [rdx+4], eax
            0xc3, // ASM: ret
        ];
        agrees(&Program::raw_x64(&code), 0x1000);
    }

    /// A switch through a byte table switches on the index the table is
    /// read at, the offset the code took from the value included.
    ///
    /// `add eax, -2; cmp eax, 3; ja default; movzx eax, byte [eax+T]; jmp
    /// [eax*4+J]`: the byte read's address folds the `-2` into `T`, and
    /// taking the table's constant off the address left the switch on the
    /// value from before the `-2`, with cases that count from after it.
    #[test]
    fn a_switch_through_a_byte_table_keeps_the_index_s_offset() {
        let mut code = vec![
            0x8b, 0xc1, // ASM: mov eax, ecx
            0x90, // ASM: nop
            0x90, // ASM: nop
            0x83, 0xc0, 0xfe, // ASM: add eax, -2
            0x83, 0xf8, 0x03, // ASM: cmp eax, 3
            0x77, 0x1f, // ASM: ja 0x102b
            0xb9, 0x03, 0x00, 0x00, 0x00, // ASM: mov ecx, 3
            0x0f, 0xb6, 0x80, 0x38, 0x10, 0x00, 0x00, // ASM: movzx eax, byte [eax+0x1038]
            0xff, 0x24, 0x85, 0x30, 0x10, 0x00, 0x00, // ASM: jmp [eax*4+0x1030]
            0xb8, 0x0a, 0x00, 0x00, 0x00, // ASM: mov eax, 10
            0xc3, // ASM: ret
            0xb8, 0x14, 0x00, 0x00, 0x00, // ASM: mov eax, 20
            0xc3, // ASM: ret
            0x31, 0xc0, // ASM: xor eax, eax
            0xc3, // ASM: ret
        ];
        code.resize(0x30, 0xcc);
        code.extend([0x1f, 0x10, 0x00, 0x00, 0x25, 0x10, 0x00, 0x00]);
        code.extend([0x00, 0x01, 0x01, 0x00]);
        agrees(&x86(&code), 0x1000);
    }

    /// A switch through a byte table switches on the byte table's index
    /// when the byte it reads is written out for a case that reads it.
    ///
    /// One case returns the byte the dispatch read into `eax`, so the read
    /// is written out at the dispatch's end, `eax = *(uint8_t*)(eax + T)`,
    /// and the switch, which read that same value, was rewritten to read
    /// `eax`: `switch (eax)` on the byte, with cases that number the index.
    #[test]
    fn a_switch_through_a_byte_table_reads_the_index_not_the_byte() {
        let mut code = vec![
            0x8b, 0xc1, // ASM: mov eax, ecx
            0x90, // ASM: nop
            0x90, // ASM: nop
            0x83, 0xc0, 0xfe, // ASM: add eax, -2
            0x83, 0xf8, 0x03, // ASM: cmp eax, 3
            0x77, 0x19, // ASM: ja 0x1025
            0xb9, 0x03, 0x00, 0x00, 0x00, // ASM: mov ecx, 3
            0x0f, 0xb6, 0x80, 0x34, 0x10, 0x00, 0x00, // ASM: movzx eax, byte [eax+0x1034]
            0xff, 0x24, 0x85, 0x2c, 0x10, 0x00, 0x00, // ASM: jmp [eax*4+0x102c]
            0xb8, 0x0a, 0x00, 0x00, 0x00, // ASM: mov eax, 10
            0xc3, // ASM: ret
            0xc3, // ASM: ret
        ];
        code.resize(0x2c, 0xcc);
        code.extend([0x1f, 0x10, 0x00, 0x00, 0x25, 0x10, 0x00, 0x00]);
        code.extend([0x01, 0x00, 0x00, 0x01]);
        agrees(&x86(&code), 0x1000);
    }

    /// A value that reads a variable a predecessor writes out at its end is
    /// written out with it, not carried into the successor.
    ///
    /// The store over `a1` is written out at the block's end for the path
    /// that reads it, and so is `eax`, which read `a1` before the store;
    /// `ecx`, which read the `eax` from before that, was carried into the
    /// other successor as pending, where it read the new `eax`.
    #[test]
    fn a_reader_of_a_value_written_out_at_a_join_is_written_out_too() {
        let mut code = vec![
            0xe8, 0xfb, 0x00, 0x00, 0x00, // ASM: call 0x1100
            0x8b, 0x08, // ASM: mov ecx, [eax]
            0x8b, 0x44, 0x24, 0x04, // ASM: mov eax, [esp+4]
            0xc7, 0x44, 0x24, 0x04, 0x00, 0x00, 0x00, 0x00, // ASM: mov dword [esp+4], 0
            0x85, 0xc9, // ASM: test ecx, ecx
            0x74, 0x06, // ASM: je 0x101d
            0x01, 0xc8, // ASM: add eax, ecx
            0x89, 0x44, 0x24, 0x04, // ASM: mov [esp+4], eax
            0x8b, 0x44, 0x24, 0x04, // ASM: mov eax, [esp+4]
            0xc3, // ASM: ret
        ];
        code.resize(0x100, 0xcc);
        code.extend([
            0xb8, 0x00, 0x10, 0x00, 0x00, // ASM: mov eax, 0x1000
            0xc3, // ASM: ret
        ]);
        agrees(&x86(&code), 0x1000);
    }

    /// A value that reads one a predecessor writes out at its end only to
    /// keep it right is written out with it too, and not carried on.
    ///
    /// `ebx` is written out where the paths meet, and before it the store of
    /// the old `ebx` over `a2`, which reads it, and before that `edx`, which
    /// read `a2` before the store; `edx` was still carried into the join as
    /// pending, where it read the new `a2`: `*a2` for the `*edx` the code
    /// reads.
    #[test]
    fn a_value_written_out_for_a_reader_s_sake_is_not_carried_on() {
        let code = [
            0x55, // ASM: push ebp
            0x8b, 0xec, // ASM: mov ebp, esp
            0x8b, 0x55, 0x0c, // ASM: mov edx, [ebp+0xc]
            0x85, 0xd2, // ASM: test edx, edx
            0x74, 0x06, // ASM: je 0x1010
            0x89, 0x5d, 0x0c, // ASM: mov [ebp+0xc], ebx
            0x8b, 0x5d, 0x10, // ASM: mov ebx, [ebp+0x10]
            0x8b, 0x02, // ASM: mov eax, [edx]
            0x0f, 0xaf, 0xc3, // ASM: imul eax, ebx
            0x5d, // ASM: pop ebp
            0xc3, // ASM: ret
        ];
        agrees(&x86(&code), 0x1000);
    }

    /// A slot the text names reads at the width the text declares it.
    ///
    /// The byte stored at `[rsp+7]` is written out for the join that reads
    /// it, and the compare, which read the same byte, reads `local_11`, a
    /// `uint8_t`; read as a whole word, the variable held the seven bytes
    /// above it too and the branch went the other way.
    #[test]
    fn a_named_slot_reads_at_its_declared_width() {
        let code = [
            0x48, 0x83, 0xec, 0x18, // ASM: sub rsp, 0x18
            0xc6, 0x44, 0x24, 0x07, 0x09, // ASM: mov byte [rsp+7], 9
            0x4d, 0x85, 0xc0, // ASM: test r8, r8
            0x74, 0x0e, // ASM: je 0x101c
            0x8a, 0x01, // ASM: mov al, [rcx]
            0x88, 0x44, 0x24, 0x07, // ASM: mov [rsp+7], al
            0x0f, 0xb6, 0xc0, // ASM: movzx eax, al
            0x48, 0x39, 0xd0, // ASM: cmp rax, rdx
            0x73, 0x07, // ASM: jae 0x1023
            0x0f, 0xb6, 0x44, 0x24, 0x07, // ASM: movzx eax, byte [rsp+7]
            0xeb, 0x05, // ASM: jmp 0x1028
            0xb8, 0x05, 0x00, 0x00, 0x00, // ASM: mov eax, 5
            0x48, 0x83, 0xc4, 0x18, // ASM: add rsp, 0x18
            0xc3, // ASM: ret
        ];
        agrees(&Program::raw_x64(&code), 0x1000);
    }

    /// A slot the debug information names replays as the slot it names.
    ///
    /// The check binds a declared variable to its frame offset by the
    /// name's spelling, which `flag` carries none of; the function's own
    /// debug record states it, so the machine still runs on the slot the
    /// text means, at the width the text declares.
    #[test]
    fn a_debug_named_slot_still_checks_as_its_slot() {
        let code = [
            0x48, 0x83, 0xec, 0x18, // ASM: sub rsp, 0x18
            0xc6, 0x44, 0x24, 0x07, 0x09, // ASM: mov byte [rsp+7], 9
            0x4d, 0x85, 0xc0, // ASM: test r8, r8
            0x74, 0x0e, // ASM: je 0x101c
            0x8a, 0x01, // ASM: mov al, [rcx]
            0x88, 0x44, 0x24, 0x07, // ASM: mov [rsp+7], al
            0x0f, 0xb6, 0xc0, // ASM: movzx eax, al
            0x48, 0x39, 0xd0, // ASM: cmp rax, rdx
            0x73, 0x07, // ASM: jae 0x1023
            0x0f, 0xb6, 0x44, 0x24, 0x07, // ASM: movzx eax, byte [rsp+7]
            0xeb, 0x05, // ASM: jmp 0x1028
            0xb8, 0x05, 0x00, 0x00, 0x00, // ASM: mov eax, 5
            0x48, 0x83, 0xc4, 0x18, // ASM: add rsp, 0x18
            0xc3, // ASM: ret
        ];
        use super::super::decompile;
        let mut p = Program::raw_x64(&code);
        p.debug_functions.push(crate::dwarf::Subprogram {
            low_pc: 0x1000,
            name: "probe".to_owned(),
            parameters: Vec::new(),
            return_type: None,
            locals: [(-0x11i64, "flag".to_owned())].into_iter().collect(),
        });
        let a = Analysis::compute(&p);
        let text = decompile(&p, &a, &Overlay::default(), 0x1000).unwrap_or_default();
        assert!(text.contains("flag"), "the local does not render:\n{text}");
        assert!(
            !text.contains("local_11"),
            "the slot renders synthesized:\n{text}"
        );
        agrees(&p, 0x1000);
    }

    /// A branch on a value a block's end writes out reads it as it was,
    /// whatever order the write-outs take.
    ///
    /// `shl r8d, 16; or r11d, r8d; cmp r11d, 0xff`: the join writes out
    /// `r8` and `r11`, the compare was moved onto `r8` for `r8 << 16` ahead
    /// of `r8`'s write-out, and `r11`'s, which came first, parked it as
    /// `tmp_1 = r11 | r8` while `r8` was still the old one.
    #[test]
    fn a_branch_on_values_written_out_at_a_join_reads_them_as_they_were() {
        let code = [
            0x85, 0xc9, // ASM: test ecx, ecx
            0x74, 0x13, // ASM: je 0x1017
            0x41, 0xc1, 0xe0, 0x10, // ASM: shl r8d, 16
            0x45, 0x09, 0xc3, // ASM: or r11d, r8d
            0x41, 0x81, 0xfb, 0xff, 0x00, 0x00, 0x00, // ASM: cmp r11d, 0xff
            0x77, 0x03, // ASM: ja 0x1017
            0x31, 0xc0, // ASM: xor eax, eax
            0xc3, // ASM: ret
            0x4c, 0x89, 0xc0, // ASM: mov rax, r8
            0x4c, 0x01, 0xd8, // ASM: add rax, r11
            0xc3, // ASM: ret
        ];
        agrees(&Program::raw_x64(&code), 0x1000);
    }

    /// A register's save beside a store the successor reads is no claim of
    /// the text's.
    ///
    /// `push esi` saves `esi` at `[esp-4]`, and `push edi`, with `edi`
    /// written first, stores a value just below it that the successor
    /// reads; the slot of the save, named later where `ecx` is pushed over
    /// it, had its bytes held against the text as a store of the lifter's,
    /// because a store lay within a word below them.
    #[test]
    fn a_save_beside_a_live_store_is_no_claim_of_the_text() {
        let code = [
            0x8b, 0xff, // ASM: mov edi, edi
            0x56, // ASM: push esi
            0x57, // ASM: push edi
            0x85, 0xc9, // ASM: test ecx, ecx
            0x74, 0x01, // ASM: je 0x1009
            0x47, // ASM: inc edi
            0x5f, // ASM: pop edi
            0x5e, // ASM: pop esi
            0x51, // ASM: push ecx
            0x0f, 0xb6, 0x04, 0x24, // ASM: movzx eax, byte [esp]
            0x59, // ASM: pop ecx
            0xc3, // ASM: ret
        ];
        agrees(&x86(&code), 0x1000);
    }

    /// A call through a read-only pointer to a dispatch thunk calls what
    /// the thunk jumps through, and the check follows it there.
    ///
    /// `call [rip+X]` with `X` holding the address of `jmp rax` (the CFG
    /// dispatcher) is a call through `rax`, as the text says; the check
    /// knew the thunk only by a direct call's target, so it held the
    /// thunk's own address against the text's target.
    #[test]
    fn a_call_through_a_pointer_to_a_dispatch_thunk_is_checked_through_it() {
        use crate::program::Section;
        let mut bytes = vec![0xcc; 0x2000];
        let code = [
            0x48, 0x83, 0xec, 0x28, // ASM: sub rsp, 0x28
            0x48, 0x8b, 0x01, // ASM: mov rax, [rcx]
            0xff, 0x15, 0xf3, 0x0f, 0x00, 0x00, // ASM: call [rip+0xff3]
            0x48, 0x83, 0xc4, 0x28, // ASM: add rsp, 0x28
            0xc3, // ASM: ret
        ];
        bytes[..code.len()].copy_from_slice(&code);
        bytes[0x20..0x22].copy_from_slice(&[0xff, 0xe0]); // ASM: jmp rax
        bytes[0x1000..0x1008].copy_from_slice(&0x1020u64.to_le_bytes());
        let p = Program::raw(
            bytes,
            Arch::X86_64,
            0,
            Some(0x1000),
            vec![
                Section::mapped(".text", 0x1000, 0, 0x1000, false, true),
                Section::mapped(".rdata", 0x2000, 0x1000, 0x1000, false, false),
            ],
        );
        agrees(&p, 0x1000);
    }

    /// A structure's zero fill, a vector register zeroed and stored sixteen
    /// bytes wide, is checked, and so is its store pending at an edge.
    ///
    /// The block was outside the integer subset and the pending bytes
    /// unknown, so a text writing half the zeros the join reads half of
    /// passed.
    #[test]
    fn a_zero_fill_is_checked_where_it_is_pending() {
        let code = [
            0x48, 0x83, 0xec, 0x38, // ASM: sub rsp, 0x38
            0x0f, 0x57, 0xc0, // ASM: xorps xmm0, xmm0
            0x0f, 0x11, 0x44, 0x24, 0x20, // ASM: movups [rsp+0x20], xmm0
            0x85, 0xd2, // ASM: test edx, edx
            0x74, 0x05, // ASM: je 0x1015
            0x48, 0x89, 0x4c, 0x24, 0x20, // ASM: mov [rsp+0x20], rcx
            0x48, 0x8b, 0x44, 0x24, 0x28, // ASM: mov rax, [rsp+0x28]
            0x48, 0x83, 0xc4, 0x38, // ASM: add rsp, 0x38
            0xc3, // ASM: ret
        ];
        let p = Program::raw_x64(&code);
        agrees(&p, 0x1000);
        // the zeros written as a word: the join reads the half left out
        let r = replayed_with(&p, 0x1000, 1, |e| {
            if e.at == 0x100e
                && let EffectKind::Assign(_, _, bits @ 128) = &mut e.kind
            {
                *bits = 64;
            }
        });
        assert!(claims(&r).contains(&Claim::Slot), "{}", replay_tsv(&r));
    }

    /// A block entered from one side of a branch is tried only from states
    /// on that side.
    ///
    /// The text's `lzcnt(a1 - 1)` stands for `bsr` under the `a1 > 1` that
    /// leads to it, and from `a1 == 1`, which never gets there, the
    /// machine's `bsr` of zero left its destination as it was.
    #[test]
    fn a_block_runs_under_the_branch_into_it() {
        let code = [
            0x48, 0x83, 0xf9, 0x01, // ASM: cmp rcx, 1
            0x76, 0x0d, // ASM: jbe 0x1013
            0x48, 0x83, 0xe9, 0x01, // ASM: sub rcx, 1
            0x48, 0x0f, 0xbd, 0xc1, // ASM: bsr rax, rcx
            0x48, 0x83, 0xf0, 0x3f, // ASM: xor rax, 0x3f
            0xc3, // ASM: ret
            0x31, 0xc0, // ASM: xor eax, eax
            0xc3, // ASM: ret
        ];
        let p = Program::raw_x64(&code);
        let a = Analysis::compute(&p);
        // INVARIANT: the states reaching `a1 == 1` are rare; sixty-four
        // seeds draw one.
        for seed in 1..=64 {
            let r = replay_function(&p, &a, 0x1000, seed);
            assert_eq!(claims(&r), [], "seed {seed}: {}", replay_tsv(&r));
            assert_eq!(r.checked, 3, "seed {seed}: {}", replay_tsv(&r));
        }
    }

    /// The branch a block runs under is found through a block that only
    /// jumps to it: `cmp; jbe` falls into `jmp`, and the scan behind the
    /// jump runs where the compare let it.
    #[test]
    fn a_block_runs_under_the_branch_a_jump_passes_on() {
        let code = [
            0x48, 0x83, 0xf9, 0x01, // ASM: cmp rcx, 1
            0x76, 0x02, // ASM: jbe 0x1008
            0xeb, 0x03, // ASM: jmp 0x100b
            0x31, 0xc0, // ASM: xor eax, eax
            0xc3, // ASM: ret
            0x48, 0x83, 0xe9, 0x01, // ASM: sub rcx, 1
            0x48, 0x0f, 0xbd, 0xc1, // ASM: bsr rax, rcx
            0x48, 0x83, 0xf0, 0x3f, // ASM: xor rax, 0x3f
            0xc3, // ASM: ret
        ];
        let p = Program::raw_x64(&code);
        let a = Analysis::compute(&p);
        for seed in 1..=64 {
            let r = replay_function(&p, &a, 0x1000, seed);
            assert_eq!(claims(&r), [], "seed {seed}: {}", replay_tsv(&r));
        }
    }

    /// A forward bit scan of zero leaves its destination as it was, so the
    /// text's `bsf(a1)` of a zero `a1` says nothing, where it read as 64
    /// on the side of the branch only a nonzero `a1` takes.
    #[test]
    fn a_forward_bit_scan_of_zero_is_undefined() {
        let code = [
            0x48, 0x89, 0x4c, 0x24, 0x08, // ASM: mov [rsp+8], rcx
            0x48, 0x83, 0xec, 0x18, // ASM: sub rsp, 0x18
            0x48, 0x8b, 0x44, 0x24, 0x20, // ASM: mov rax, [rsp+0x20]
            0x48, 0x0f, 0xbc, 0xc0, // ASM: bsf rax, rax
            0x89, 0x04, 0x24, // ASM: mov [rsp], eax
            0x0f, 0x95, 0xc0, // ASM: setne al
            0x0f, 0xb6, 0xc0, // ASM: movzx eax, al
            0x85, 0xc0, // ASM: test eax, eax
            0x74, 0x0a, // ASM: je 0x1029
            0x8b, 0x04, 0x24, // ASM: mov eax, [rsp]
            0x48, 0x89, 0x44, 0x24, 0x08, // ASM: mov [rsp+8], rax
            0xeb, 0x09, // ASM: jmp 0x1032
            0x48, 0xc7, 0x44, 0x24, 0x08, 0x40, 0x00, 0x00,
            0x00, // ASM: mov qword [rsp+8], 0x40
            0x48, 0x8b, 0x44, 0x24, 0x08, // ASM: mov rax, [rsp+8]
            0x48, 0x83, 0xc4, 0x18, // ASM: add rsp, 0x18
            0xc3, // ASM: ret
        ];
        let p = Program::raw_x64(&code);
        let a = Analysis::compute(&p);
        for seed in 1..=64 {
            let r = replay_function(&p, &a, 0x1000, seed);
            assert_eq!(claims(&r), [], "seed {seed}: {}", replay_tsv(&r));
        }
    }

    /// A float store is compared, not counted as unreadable, and a lifted
    /// float with the wrong sign is flagged on every seed.
    ///
    /// `movss`/`addss` leave a single in `xmm0` whose store the text
    /// writes: the block was outside the checked subset and the store's
    /// value unreadable, so a text storing the negation of the sum passed.
    #[test]
    fn a_float_store_is_compared_and_a_wrong_one_flagged() {
        let p = Program::raw_x64(&[
            0xf3, 0x0f, 0x10, 0x01, // ASM: movss xmm0,[rcx]
            0xf3, 0x0f, 0x58, 0x41, 0x04, // ASM: addss xmm0,[rcx+4]
            0xf3, 0x0f, 0x11, 0x41, 0x08, // ASM: movss [rcx+8],xmm0
            0xc3, // ASM: ret
        ]);
        for seed in 1..=8 {
            let a = Analysis::compute(&p);
            let r = replay_function(&p, &a, 0x1000, seed);
            assert_eq!(claims(&r), [], "seed {seed}: {}", replay_tsv(&r));
            assert_eq!(r.checked, 1, "seed {seed}: {}", replay_tsv(&r));
            // A state whose drawn pointer sits at the top of the address
            // space stores nowhere comparable, so the count is of states.
            assert!(
                r.compared.get(&Claim::Memory).copied().unwrap_or(0) > 0,
                "seed {seed}: {}",
                replay_tsv(&r)
            );
            assert_eq!(
                r.unreadable.get(&Claim::Memory).copied().unwrap_or(0),
                0,
                "seed {seed}: {}",
                replay_tsv(&r)
            );
            let r = replayed_with(&p, 0x1000, seed, |e| {
                if let EffectKind::Store(s) = &mut e.kind {
                    s.2 = Expr::Un(UnOp::Neg, Box::new(s.2.clone()));
                }
            });
            assert_eq!(
                claims(&r),
                [Claim::Memory],
                "seed {seed}: {}",
                replay_tsv(&r)
            );
        }
    }

    /// A branch on a float compare goes the machine's way, and the
    /// successors reading the float register are compared at the width
    /// its expression computes at.
    ///
    /// `ucomiss` after a sum in `xmm0`, `ja` over two blocks that each
    /// store the single: unordered on a NaN, the compare takes `ja` the
    /// machine's way, and each successor's claim on `xmm0` reads the
    /// single the machine's own `addss` rounding left.
    #[test]
    fn a_branch_on_a_float_compare_agrees_with_the_machine() {
        let p = Program::raw_x64(&[
            0xf3, 0x0f, 0x10, 0x01, // ASM: movss xmm0,[rcx]
            0xf3, 0x0f, 0x58, 0x41, 0x04, // ASM: addss xmm0,[rcx+4]
            0x0f, 0x2e, 0x41, 0x08, // ASM: ucomiss xmm0,[rcx+8]
            0x77, 0x0a, // ASM: ja 0x1019
            0xf3, 0x0f, 0x11, 0x00, // ASM: movss [rax],xmm0
            0xb8, 0x01, 0x00, 0x00, 0x00, // ASM: mov eax,1
            0xc3, // ASM: ret
            0xf3, 0x0f, 0x11, 0x00, // ASM: movss [rax],xmm0
            0x31, 0xc0, // ASM: xor eax,eax
            0xc3, // ASM: ret
        ]);
        for seed in 1..=8 {
            let a = Analysis::compute(&p);
            let r = replay_function(&p, &a, 0x1000, seed);
            assert_eq!(claims(&r), [], "seed {seed}: {}", replay_tsv(&r));
            assert_eq!(r.checked, 3, "seed {seed}: {}", replay_tsv(&r));
            // A state whose drawn pointer sits at the top of the address
            // space compares past it, counted as unreadable.
            assert!(
                r.compared.get(&Claim::Branch).copied().unwrap_or(0) > 0,
                "seed {seed}: {}",
                replay_tsv(&r)
            );
        }
    }

    /// A float compare of parameters reads as float, although their
    /// variables carry no float type for the condition's operands to see.
    ///
    /// `ucomiss xmm0, xmm1; seta al; and al, 1` on two float arguments:
    /// the lifter writes `Cmp` over the two bare parameters, which as
    /// integers order differently than the floats the machine compares,
    /// and the `and` after the `setcc` sets flags of its own that the
    /// condition never read; the compare instruction is the witness.
    #[test]
    fn a_float_compare_of_parameters_reads_as_float() {
        let p = Program::raw_x64(&[
            0x0f, 0x2e, 0xc1, // ASM: ucomiss xmm0,xmm1
            0x0f, 0x97, 0xc0, // ASM: seta al
            0x24, 0x01, // ASM: and al,1
            0x0f, 0xb6, 0xc0, // ASM: movzx eax,al
            0xc3, // ASM: ret
        ]);
        for seed in 1..=8 {
            let a = Analysis::compute(&p);
            let r = replay_function(&p, &a, 0x1000, seed);
            assert_eq!(claims(&r), [], "seed {seed}: {}", replay_tsv(&r));
            assert_eq!(r.checked, 1, "seed {seed}: {}", replay_tsv(&r));
            assert!(
                r.compared.get(&Claim::Return).copied().unwrap_or(0) > 0,
                "seed {seed}: {}",
                replay_tsv(&r)
            );
            assert_eq!(
                r.unreadable.get(&Claim::Return).copied().unwrap_or(0),
                0,
                "seed {seed}: {}",
                replay_tsv(&r)
            );
        }
    }

    /// A one-block packed-integer fixture: its block is checked, not
    /// counted as float/vector, its vector store is compared, and a store
    /// of a lane the machine does not hold is flagged, on every seed.
    ///
    /// # Arguments
    ///
    /// * `code` - The function's bytes, at `0x1000`.
    fn packed_agrees(code: &[u8]) {
        let p = Program::raw_x64(code);
        for seed in 1..=8 {
            let a = Analysis::compute(&p);
            let r = replay_function(&p, &a, 0x1000, seed);
            assert_eq!(claims(&r), [], "seed {seed}: {}", replay_tsv(&r));
            assert_eq!(r.checked, 1, "seed {seed}: {}", replay_tsv(&r));
            assert!(
                r.compared.get(&Claim::Memory).copied().unwrap_or(0) > 0,
                "seed {seed}: {}",
                replay_tsv(&r)
            );
            let r = replayed_with(&p, 0x1000, seed, |e| {
                if let EffectKind::Store(s) = &mut e.kind {
                    s.2 = Expr::Call("pxor".to_owned(), vec![s.2.clone(), Expr::Const(1)]);
                }
            });
            assert_eq!(
                claims(&r),
                [Claim::Memory],
                "seed {seed}: {}",
                replay_tsv(&r)
            );
        }
    }

    /// A 128-bit vector move, sixteen bytes loaded and stored back through
    /// memory, is checked against the machine.
    #[test]
    fn a_vector_move_is_compared_and_a_wrong_one_flagged() {
        packed_agrees(&[
            0xf3, 0x0f, 0x6f, 0x01, // ASM: movdqu xmm0,[rcx]
            0xf3, 0x0f, 0x7f, 0x41, 0x10, // ASM: movdqu [rcx+0x10],xmm0
            0xc3, // ASM: ret
        ]);
    }

    /// The packed bitwise operations over whole lanes are checked against
    /// the machine.
    #[test]
    fn packed_logic_is_compared_and_a_wrong_one_flagged() {
        packed_agrees(&[
            0xf3, 0x0f, 0x6f, 0x01, // ASM: movdqu xmm0,[rcx]
            0xf3, 0x0f, 0x6f, 0x4a, 0x10, // ASM: movdqu xmm1,[rcx+0x10]
            0x66, 0x0f, 0xef, 0xc1, // ASM: pxor xmm0,xmm1
            0x66, 0x0f, 0xdb, 0xc1, // ASM: pand xmm0,xmm1
            0x66, 0x0f, 0xeb, 0xc1, // ASM: por xmm0,xmm1
            0xf3, 0x0f, 0x7f, 0x41, 0x20, // ASM: movdqu [rcx+0x20],xmm0
            0xc3, // ASM: ret
        ]);
    }

    /// Lane-wise packed addition and subtraction, at every lane width, are
    /// checked against the machine.
    #[test]
    fn packed_add_and_sub_are_compared_and_a_wrong_one_flagged() {
        packed_agrees(&[
            0xf3, 0x0f, 0x6f, 0x01, // ASM: movdqu xmm0,[rcx]
            0xf3, 0x0f, 0x6f, 0x4a, 0x10, // ASM: movdqu xmm1,[rcx+0x10]
            0x66, 0x0f, 0xfc, 0xc1, // ASM: paddb xmm0,xmm1
            0x66, 0x0f, 0xfd, 0xc1, // ASM: paddw xmm0,xmm1
            0x66, 0x0f, 0xfe, 0xc1, // ASM: paddd xmm0,xmm1
            0x66, 0x0f, 0xd4, 0xc1, // ASM: paddq xmm0,xmm1
            0x66, 0x0f, 0xf8, 0xc1, // ASM: psubb xmm0,xmm1
            0x66, 0x0f, 0xf9, 0xc1, // ASM: psubw xmm0,xmm1
            0x66, 0x0f, 0xfa, 0xc1, // ASM: psubd xmm0,xmm1
            0x66, 0x0f, 0xfb, 0xc1, // ASM: psubq xmm0,xmm1
            0xf3, 0x0f, 0x7f, 0x41, 0x20, // ASM: movdqu [rcx+0x20],xmm0
            0xc3, // ASM: ret
        ]);
    }

    /// The narrowing packs, signed and unsigned, are checked against the
    /// machine.
    #[test]
    fn packed_narrowing_packs_are_compared_and_a_wrong_one_flagged() {
        packed_agrees(&[
            0xf3, 0x0f, 0x6f, 0x01, // ASM: movdqu xmm0,[rcx]
            0xf3, 0x0f, 0x6f, 0x4a, 0x10, // ASM: movdqu xmm1,[rcx+0x10]
            0x66, 0x0f, 0x6b, 0xc1, // ASM: packssdw xmm0,xmm1
            0x66, 0x0f, 0x63, 0xc1, // ASM: packsswb xmm0,xmm1
            0x66, 0x0f, 0x67, 0xc1, // ASM: packuswb xmm0,xmm1
            0xf3, 0x0f, 0x7f, 0x41, 0x20, // ASM: movdqu [rcx+0x20],xmm0
            0xc3, // ASM: ret
        ]);
    }

    /// The unpacks, low and high at every lane width, are checked against
    /// the machine.
    #[test]
    fn packed_unpacks_are_compared_and_a_wrong_one_flagged() {
        packed_agrees(&[
            0xf3, 0x0f, 0x6f, 0x01, // ASM: movdqu xmm0,[rcx]
            0xf3, 0x0f, 0x6f, 0x4a, 0x10, // ASM: movdqu xmm1,[rcx+0x10]
            0x66, 0x0f, 0x60, 0xc1, // ASM: punpcklbw xmm0,xmm1
            0x66, 0x0f, 0x61, 0xc1, // ASM: punpcklwd xmm0,xmm1
            0x66, 0x0f, 0x62, 0xc1, // ASM: punpckldq xmm0,xmm1
            0x66, 0x0f, 0x6c, 0xc1, // ASM: punpcklqdq xmm0,xmm1
            0x66, 0x0f, 0x68, 0xc1, // ASM: punpckhbw xmm0,xmm1
            0x66, 0x0f, 0x69, 0xc1, // ASM: punpckhwd xmm0,xmm1
            0x66, 0x0f, 0x6a, 0xc1, // ASM: punpckhdq xmm0,xmm1
            0x66, 0x0f, 0x6d, 0xc1, // ASM: punpckhqdq xmm0,xmm1
            0xf3, 0x0f, 0x7f, 0x41, 0x20, // ASM: movdqu [rcx+0x20],xmm0
            0xc3, // ASM: ret
        ]);
    }

    /// A doubleword shuffle by immediate is checked against the machine.
    #[test]
    fn a_packed_shuffle_is_compared_and_a_wrong_one_flagged() {
        packed_agrees(&[
            0xf3, 0x0f, 0x6f, 0x0a, // ASM: movdqu xmm1,[rdx]
            0x66, 0x0f, 0x70, 0xc1, 0x1b, // ASM: pshufd xmm0,xmm1,0x1b
            0xf3, 0x0f, 0x7f, 0x41, 0x20, // ASM: movdqu [rcx+0x20],xmm0
            0xc3, // ASM: ret
        ]);
    }

    /// The lane shifts by immediate, logical, arithmetic and by whole
    /// bytes, are checked against the machine.
    #[test]
    fn packed_shifts_are_compared_and_a_wrong_one_flagged() {
        packed_agrees(&[
            0xf3, 0x0f, 0x6f, 0x01, // ASM: movdqu xmm0,[rcx]
            0x66, 0x0f, 0x71, 0xf0, 0x03, // ASM: psllw xmm0,3
            0x66, 0x0f, 0x72, 0xf0, 0x04, // ASM: pslld xmm0,4
            0x66, 0x0f, 0x73, 0xf0, 0x05, // ASM: psllq xmm0,5
            0x66, 0x0f, 0x71, 0xd0, 0x06, // ASM: psrlw xmm0,6
            0x66, 0x0f, 0x72, 0xd0, 0x07, // ASM: psrld xmm0,7
            0x66, 0x0f, 0x73, 0xd0, 0x08, // ASM: psrlq xmm0,8
            0x66, 0x0f, 0x71, 0xe0, 0x09, // ASM: psraw xmm0,9
            0x66, 0x0f, 0x72, 0xe0, 0x0a, // ASM: psrad xmm0,10
            0x66, 0x0f, 0x73, 0xf8, 0x02, // ASM: pslldq xmm0,2
            0x66, 0x0f, 0x73, 0xd8, 0x03, // ASM: psrldq xmm0,3
            0xf3, 0x0f, 0x7f, 0x41, 0x20, // ASM: movdqu [rcx+0x20],xmm0
            0xc3, // ASM: ret
        ]);
    }

    /// Three blocks: `cmp rcx, 1; jbe` to a `return 0` or a `return 1`.
    const THREE_BLOCKS: [u8; 15] = [
        0x48, 0x83, 0xf9, 0x01, // ASM: cmp rcx, 1
        0x76, 0x06, // ASM: jbe 0x100c
        0xb8, 0x01, 0x00, 0x00, 0x00, // ASM: mov eax, 1
        0xc3, // ASM: ret
        0x31, 0xc0, // ASM: xor eax, eax
        0xc3, // ASM: ret
    ];

    /// An answer says what of it was checked against the binary, on its
    /// second line, and the text every other reader parses says nothing.
    ///
    /// The check reads the decompilation the text comes from: one is built,
    /// its witness taken, and the memo keeps the text and the check.
    #[test]
    fn an_answer_says_what_of_it_was_checked() {
        use crate::analysis::decompile::{checked_header, decompile_named, with_header};
        let p = Program::raw_x64(&THREE_BLOCKS);
        let a = Analysis::compute(&p);
        let o = Overlay::default();
        let header = checked_header(&p, &a, &o, 0x1000).expect("checked");
        assert_eq!(
            header,
            "// checked vs binary: statements as emitted, 3/3 blocks x3 states; unchecked: C spelling, later text passes"
        );
        let text = decompile_named(&p, &a, &o, 0x1000).expect("text");
        assert!(!text.contains("checked vs binary"), "{text}");
        let shown = with_header(&text, Some(&header));
        assert_eq!(shown.lines().next(), text.lines().next());
        assert_eq!(shown.lines().nth(1), Some(header.as_str()));
        assert_eq!(shown.lines().count(), text.lines().count() + 1);
        assert_eq!(a.derived.held("plain_text"), 1);
        assert_eq!(a.derived.held("text_check"), 1);
        let memo = crate::analysis::decompiled_cached(&p, &a, &o, o.fingerprint(), 0x1000);
        let d = memo.as_ref().as_ref().expect("memoized");
        assert!(d.take_witness().is_none(), "the check took the witness");
    }

    /// A block whose compare reaches a condition the text writes over
    /// unknown flags is not counted as agreeing: the compare has no
    /// statement, so nothing of it was checked.
    ///
    /// `J2`'s `je` reads the zero flag of `cmp r9d, 9` on one edge and, past
    /// `J1`'s `jb`, of `cmp edx, 5` or `cmp r8d, 7` on the other.
    #[test]
    fn a_compare_whose_flags_the_text_loses_is_unchecked() {
        use crate::analysis::decompile::{checked_header, decompile_named};
        let p = Program::raw_x64(&[
            0x85, 0xc9, // ASM: test ecx, ecx
            0x78, 0x0f, // ASM: js P3
            0x74, 0x05, // ASM: je P2
            0x83, 0xfa, 0x05, // ASM: P1: cmp edx, 5
            0xeb, 0x04, // ASM: jmp J1
            0x41, 0x83, 0xf8, 0x07, // ASM: P2: cmp r8d, 7
            0x72, 0x0b, // ASM: J1: jb OUT1
            0xeb, 0x04, // ASM: jmp J2
            0x41, 0x83, 0xf9, 0x09, // ASM: P3: cmp r9d, 9
            0x74, 0x09, // ASM: J2: je OUT2
            0x31, 0xc0, // ASM: xor eax, eax
            0xc3, // ASM: ret
            0xb8, 0x01, 0x00, 0x00, 0x00, // ASM: OUT1: mov eax, 1
            0xc3, // ASM: ret
            0xb8, 0x02, 0x00, 0x00, 0x00, // ASM: OUT2: mov eax, 2
            0xc3, // ASM: ret
        ]);
        let a = Analysis::compute(&p);
        let o = Overlay::default();
        let text = decompile_named(&p, &a, &o, 0x1000).expect("text");
        let header = checked_header(&p, &a, &o, 0x1000).expect("checked");
        assert!(text.contains("FLAGS_UNKNOWN"), "{text}");
        assert!(header.contains("6 flags across blocks"), "{header}\n{text}");
    }

    /// A block reading the thread block is counted unchecked as what it is,
    /// not as a float or vector form.
    #[test]
    fn a_thread_block_read_is_no_float() {
        use crate::analysis::decompile::checked_header;
        let p = Program::raw_x64(&[
            0x65, 0x48, 0x8b, 0x04, 0x25, 0x30, 0x00, 0x00, 0x00, // ASM: mov rax, gs:[0x30]
            0xc3, // ASM: ret
        ]);
        let a = Analysis::compute(&p);
        let header = checked_header(&p, &a, &Overlay::default(), 0x1000).expect("checked");
        assert!(header.contains("1 fs/gs access"), "{header}");
        assert!(!header.contains("float/vector"), "{header}");
    }

    /// A statement the machine does not bear out is named in the header by
    /// its instruction, so a block compared and found wrong never reads as
    /// agreement; past a few, the rest are counted.
    #[test]
    fn the_header_names_the_statements_the_binary_contradicts() {
        let check = TextCheck {
            blocks: 8,
            checked: 8,
            unchecked: Vec::new(),
            disagree: vec![0x404171],
        };
        assert_eq!(
            check.header(),
            "// checked vs binary: statements as emitted, 8/8 blocks x3 states; disagree at 0x404171; unchecked: C spelling, later text passes"
        );
        let many = TextCheck {
            disagree: (0..6).map(|i| 0x401000 + i).collect(),
            unchecked: vec![("float/vector", 1)],
            ..check
        };
        assert_eq!(
            many.header(),
            "// checked vs binary: statements as emitted, 8/8 blocks x3 states; disagree at 0x401000, 0x401001, 0x401002, 0x401003 (+2 more); unchecked: 1 float/vector, C spelling, later text passes"
        );
    }

    /// A text memoized before any answer's check, without the lifter's
    /// witness, is checked all the same, and the check says the same.
    #[test]
    fn a_text_memoized_first_is_checked_the_same() {
        use crate::analysis::decompile::{checked_header, decompile_named};
        let p = Program::raw_x64(&THREE_BLOCKS);
        let o = Overlay::default();
        let first = Analysis::compute(&p);
        let header = checked_header(&p, &first, &o, 0x1000);
        let later = Analysis::compute(&p);
        assert!(decompile_named(&p, &later, &o, 0x1000).is_some());
        assert_eq!(checked_header(&p, &later, &o, 0x1000), header);
        assert!(header.is_some());
    }

    /// Blocks past the budget are counted unchecked, by that reason, and
    /// the blocks before it are tried.
    #[test]
    fn blocks_past_the_budget_are_counted_unchecked() {
        let p = Program::raw_x64(&THREE_BLOCKS);
        let a = Analysis::compute(&p);
        let f = a.function(0x1000).expect("function");
        let d = decompile_with(&p, &a, &Overlay::default(), 0x1000, true, &[], true).expect("text");
        let effects: Vec<Vec<Effect>> = f
            .blocks
            .iter()
            .enumerate()
            .map(|(i, b)| d.effects.block(i, b.start).expect("block"))
            .collect();
        let template = Emulator::new(&p, 0).expect("emulator");
        let w = d.take_witness().expect("witness");
        let r = replay_effects(
            &p,
            &a,
            &template,
            0x1000,
            1,
            (&w, &d.live.succs),
            &effects,
            1,
        );
        assert_eq!(
            TextCheck::of(&r).header(),
            "// checked vs binary: statements as emitted, 1/3 blocks x3 states; unchecked: 2 over budget, C spelling, later text passes"
        );
    }

    /// A jump through a table of offsets from the table's own address, its
    /// index unbounded, is a computed goto, not a tail call.
    ///
    /// `rcx` holds the table's entry, no argument, which the text passed as
    /// one, and a function returning nothing then dropped the call whole.
    #[test]
    fn an_unbounded_relative_jump_table_is_a_computed_goto() {
        let code = [
            0x48, 0x81, 0xec, 0x98, 0x00, 0x00, 0x00, // ASM: sub rsp, 0x98
            0x48, 0x8b, 0x09, // ASM: mov rcx, [rcx]
            0x48, 0x83, 0xe9, 0x02, // ASM: sub rcx, 2
            0xb8, 0x02, 0x00, 0x00, 0x00, // ASM: mov eax, 2
            0x48, 0x0f, 0x43, 0xc1, // ASM: cmovae rax, rcx
            0x48, 0x89, 0x84, 0x24, 0x88, 0x00, 0x00, 0x00, // ASM: mov [rsp+0x88], rax
            0x48, 0x8b, 0x8c, 0x24, 0x88, 0x00, 0x00, 0x00, // ASM: mov rcx, [rsp+0x88]
            0x48, 0x8d, 0x05, 0x26, 0x00, 0x00, 0x00, // ASM: lea rax, [rip+0x26]
            0x48, 0x63, 0x0c, 0x88, // ASM: movsxd rcx, dword [rax+rcx*4]
            0x48, 0x01, 0xc8, // ASM: add rax, rcx
            0xff, 0xe0, // ASM: jmp rax
            0xb8, 0x01, 0x00, 0x00, 0x00, // ASM: mov eax, 1
            0x48, 0x81, 0xc4, 0x98, 0x00, 0x00, 0x00, // ASM: add rsp, 0x98
            0xc3, // ASM: ret
            0xb8, 0x02, 0x00, 0x00, 0x00, // ASM: mov eax, 2
            0x48, 0x81, 0xc4, 0x98, 0x00, 0x00, 0x00, // ASM: add rsp, 0x98
            0xc3, // ASM: ret
            0xcc, 0xcc, 0xcc, // ASM: int3 (x3)
            0xe3, 0xff, 0xff, 0xff, // DATA: case 0 at -0x1d
            0xf0, 0xff, 0xff, 0xff, // DATA: case 1 at -0x10
        ];
        let p = Program::raw_x64(&code);
        let a = Analysis::compute(&p);
        let text = decompile(&p, &a, &Overlay::default(), 0x1000).expect("text");
        assert!(
            text.contains("goto *rax;") && !text.contains("return (*"),
            "{text}"
        );
        agrees(&p, 0x1000);
    }

    /// A computed goto's target, when more than a name or a number, is
    /// parenthesized: `goto *T + x;` reads as a jump to `T` plus something.
    #[test]
    fn a_computed_goto_parenthesizes_its_target() {
        let code = [
            0x48, 0x8d, 0x05, 0x19, 0x00, 0x00, 0x00, // ASM: lea rax, [rip+0x19]
            0x48, 0x63, 0x0c, 0x88, // ASM: movsxd rcx, dword [rax+rcx*4]
            0x48, 0x01, 0xc8, // ASM: add rax, rcx
            0xff, 0xe0, // ASM: jmp rax
            0xb8, 0x01, 0x00, 0x00, 0x00, // ASM: mov eax, 1
            0xc3, // ASM: ret
            0xb8, 0x02, 0x00, 0x00, 0x00, // ASM: mov eax, 2
            0xc3, // ASM: ret
            0xcc, 0xcc, 0xcc, 0xcc, // ASM: int3 (x4)
            0xf0, 0xff, 0xff, 0xff, // DATA: case 0 at -0x10
            0xf6, 0xff, 0xff, 0xff, // DATA: case 1 at -0xa
        ];
        let p = Program::raw_x64(&code);
        let a = Analysis::compute(&p);
        let text = decompile(&p, &a, &Overlay::default(), 0x1000).expect("text");
        assert!(text.contains("goto *(0x1020 + "), "{text}");
        agrees(&p, 0x1000);
    }

    /// A store pending at a block's start that no later read reaches is the
    /// text's to drop, even inside a wider slot the successor reads part of.
    ///
    /// The dword stored over the top half of the qword at `[rsp+0x10]` is
    /// pending where the paths meet, and the join reads only the low dword;
    /// the store's bytes were held against the text as bytes of the qword.
    #[test]
    fn a_dead_store_inside_a_wider_live_slot_is_the_text_s_to_drop() {
        let code = [
            0x48, 0x83, 0xec, 0x28, // ASM: sub rsp, 0x28
            0x4c, 0x89, 0x44, 0x24, 0x10, // ASM: mov [rsp+0x10], r8
            0x89, 0x4c, 0x24, 0x14, // ASM: mov [rsp+0x14], ecx
            0x85, 0xd2, // ASM: test edx, edx
            0x74, 0x05, // ASM: je 0x1016
            0x90, // ASM: nop
            0x90, // ASM: nop
            0x90, // ASM: nop
            0xeb, 0x08, // ASM: jmp 0x101e
            0xc7, 0x44, 0x24, 0x14, 0x07, 0x00, 0x00, 0x00, // ASM: mov dword [rsp+0x14], 7
            0x8b, 0x44, 0x24, 0x10, // ASM: mov eax, [rsp+0x10]
            0x48, 0x83, 0xc4, 0x28, // ASM: add rsp, 0x28
            0xc3, // ASM: ret
        ];
        agrees(&Program::raw_x64(&code), 0x1000);
    }

    /// A value read through a computed frame address is written out before
    /// a slot it may have read is.
    ///
    /// `mov ecx, [ebp+ebx*4-0x10]` reads an array of the frame that reaches
    /// `[ebp-4]`, stored right after it and written out where the paths
    /// meet; `ecx`, carried as pending, read the slot's new value where
    /// `ebx` indexes it.
    #[test]
    fn a_read_through_a_frame_address_is_written_out_before_the_slots_it_reads() {
        let code = [
            0x55, // ASM: push ebp
            0x8b, 0xec, // ASM: mov ebp, esp
            0x83, 0xec, 0x10, // ASM: sub esp, 0x10
            0xba, 0x03, 0x00, 0x00, 0x00, // ASM: mov edx, 3
            0x8b, 0x4c, 0x9d, 0xf0, // ASM: mov ecx, [ebp+ebx*4-0x10]
            0x83, 0x65, 0xfc, 0x00, // ASM: and dword [ebp-4], 0
            0x85, 0xc0, // ASM: test eax, eax
            0x74, 0x09, // ASM: je 0x1020
            0x8b, 0xc1, // ASM: mov eax, ecx
            0xc7, 0x45, 0xfc, 0x05, 0x00, 0x00, 0x00, // ASM: mov dword [ebp-4], 5
            0x03, 0x45, 0xfc, // ASM: add eax, [ebp-4]
            0xc9, // ASM: leave
            0xc3, // ASM: ret
        ];
        agrees(&x86(&code), 0x1000);
    }

    /// The text as written agrees with the emulator on every state, and a
    /// statement made false is flagged at its instruction.
    ///
    /// A store of a wrong value, a branch on the inverted condition, a
    /// return of the wrong value, a call passing a wrong argument.
    #[test]
    fn a_false_statement_is_flagged_where_it_stands() {
        let branchy = Program::raw_x64(&[
            0x89, 0x51, 0x08, // ASM: mov [rcx+8], edx
            0x83, 0xc2, 0x01, // ASM: add edx, 1
            0x83, 0xfa, 0x05, // ASM: cmp edx, 5
            0x7c, 0x03, // ASM: jl 0x100e
            0x31, 0xc0, // ASM: xor eax, eax
            0xc3, // ASM: ret
            0xb8, 0x01, 0x00, 0x00, 0x00, // ASM: mov eax, 1
            0xc3, // ASM: ret
        ]);
        let mut code = vec![
            0x48, 0x83, 0xec, 0x28, // ASM: sub rsp, 0x28
            0x8d, 0x4a, 0x07, // ASM: lea ecx, [rdx+7]
            0xe8, 0x14, 0x00, 0x00, 0x00, // ASM: call 0x1020
            0x48, 0x83, 0xc4, 0x28, // ASM: add rsp, 0x28
            0xc3, // ASM: ret
        ];
        code.resize(0x20, 0xcc);
        code.extend([
            0x8d, 0x41, 0x01, // ASM: lea eax, [rcx+1]
            0xc3, // ASM: ret
        ]);
        let caller = Program::raw_x64(&code);
        let a = Analysis::compute(&branchy);
        for seed in 1..=8 {
            for p in [&branchy, &caller] {
                let a = Analysis::compute(p);
                let r = replay_function(p, &a, 0x1000, seed);
                assert_eq!(claims(&r), [], "seed {seed}: {}", replay_tsv(&r));
                assert!(r.checked >= 2, "seed {seed}: {}", replay_tsv(&r));
            }
            let r = replay_function(&branchy, &a, 0x1000, seed);
            for claim in [Claim::Memory, Claim::Branch, Claim::Return] {
                assert!(
                    r.compared.get(&claim).copied().unwrap_or(0) > 0,
                    "seed {seed}: {}",
                    replay_tsv(&r)
                );
            }
            let not = |e: &Expr| Expr::Un(UnOp::Not, Box::new(e.clone()));
            let r = replayed_with(&branchy, 0x1000, seed, |e| {
                if let EffectKind::Store(s) = &mut e.kind {
                    s.2 = not(&s.2);
                }
            });
            assert_eq!(
                claims(&r),
                [Claim::Memory],
                "seed {seed}: {}",
                replay_tsv(&r)
            );
            assert_eq!(r.disagreements[0].at, 0x1000);
            let r = replayed_with(&branchy, 0x1000, seed, |e| {
                if let EffectKind::Branch(c) = &mut e.kind {
                    *c = c.invert();
                }
            });
            assert_eq!(
                claims(&r),
                [Claim::Branch],
                "seed {seed}: {}",
                replay_tsv(&r)
            );
            assert_eq!(r.disagreements[0].at, 0x1009);
            let r = replayed_with(&branchy, 0x1000, seed, |e| {
                if let EffectKind::Return(Some(v)) = &mut e.kind {
                    *v = not(v);
                }
            });
            assert_eq!(
                claims(&r),
                [Claim::Return, Claim::Return],
                "seed {seed}: {}",
                replay_tsv(&r)
            );
            let r = replayed_with(&caller, 0x1000, seed, |e| {
                if let EffectKind::Call(c) = &mut e.kind {
                    for (at, v) in &mut c.args {
                        if *at == ArgAt::Reg(Register::RCX) {
                            *v = Expr::Bin(
                                crate::analysis::decompile::expr::Op::Add,
                                Box::new(v.clone()),
                                Box::new(Expr::Const(1)),
                            );
                        }
                    }
                }
            });
            assert_eq!(
                claims(&r),
                [Claim::Argument],
                "seed {seed}: {}",
                replay_tsv(&r)
            );
            assert_eq!(r.disagreements[0].at, 0x1007);
        }
    }
}
