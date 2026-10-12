//! The instruction sets the decompiler lifts, behind the one trait its
//! pipeline is written against.
//!
//! [`decompile_with`] runs the same pipeline for every
//! instruction set: decode the blocks, read the parameters, compute register
//! liveness, run the dataflow, structure and emit. What differs is how a
//! block's instructions are decoded and executed, which registers an
//! instruction reads and writes, how flags cross blocks and which reads are
//! parameters, and that is what [`Lifter`] names. [`X86`] hands every
//! question to the x86 functions the pipeline called before it was generic,
//! so the compiled x86 path is the same code; [`A64`] hands it to the arm64
//! lifter ([`lift_a64`]) and the arm64 procedure call standard.

use super::*;
use crate::isa::a64;

/// What the decompiler's pipeline asks of an instruction set.
///
/// The pipeline holds a function's blocks as `Vec<Vec<Self::Insn>>`, one
/// vector per block in block order, and reads them only through these
/// functions; the state between them ([`Ctx`], [`Env`], [`Live`]) is the
/// instruction set's own business only where a method says so.
pub(super) trait Lifter {
    /// One decoded instruction.
    type Insn: Copy;

    /// Decodes every block of a function, in block order.
    ///
    /// # Arguments
    ///
    /// * `ctx` - The function's context, for the image.
    /// * `f` - The function.
    ///
    /// # Returns
    ///
    /// Each block's instructions; a block stops at the first address that
    /// does not decode.
    fn decode_blocks(ctx: &Ctx<'_>, f: &Function) -> Vec<Vec<Self::Insn>>;

    /// Returns an instruction's address.
    ///
    /// # Arguments
    ///
    /// * `i` - The instruction.
    fn start(i: &Self::Insn) -> u64;

    /// Executes one block from `env` over the symbolic environment.
    ///
    /// # Arguments
    ///
    /// * `ctx` - Per-function state.
    /// * `instrs` - The block's instructions.
    /// * `prev` - The block before it in address order, where a jump
    ///   table's index may be computed.
    /// * `env` - State at the block's entry; updated to the state at its
    ///   exit.
    /// * `pass` - Record text or only compute state.
    /// * `phi` - Values the block writes out at its end, and the liveness
    ///   oracle used while doing so.
    /// * `facts` - What the block's neighbours and the function say about
    ///   it.
    ///
    /// # Returns
    ///
    /// The lines and the block's branch, jump, switch and slot facts.
    fn exec_block(
        ctx: &mut Ctx<'_>,
        instrs: &[Self::Insn],
        prev: Option<&[Self::Insn]>,
        env: &mut Env,
        pass: lift::Pass,
        phi: Option<(&lift::PhiFn<'_>, &lift::LiveFn<'_>)>,
        facts: BlockFacts<'_>,
    ) -> BlockOut;

    /// Tells whether a block reads flags before it sets any, so depends on
    /// flags a predecessor left.
    ///
    /// # Arguments
    ///
    /// * `instrs` - The block's instructions.
    fn reads_inherited_flags(instrs: &[Self::Insn]) -> bool;

    /// Returns the condition the first reader of a block's inherited flags
    /// tests.
    ///
    /// # Arguments
    ///
    /// * `instrs` - The block's instructions.
    ///
    /// # Returns
    ///
    /// The condition, or `None` when the block reads no inherited flags or
    /// reads them some other way.
    fn join_reader_cc(instrs: &[Self::Insn]) -> Option<Cc>;

    /// Computes the registers live at each block's entry, with the lane
    /// width needed.
    ///
    /// # Arguments
    ///
    /// * `ctx` - The convention and the function's state.
    /// * `code` - Each block's instructions.
    /// * `succs` - Successor block indices per block.
    ///
    /// # Returns
    ///
    /// For every block, the registers live at its entry.
    fn live_in(
        ctx: &Ctx<'_>,
        code: &[Vec<Self::Insn>],
        succs: &[Vec<usize>],
    ) -> Vec<FxHashMap<Key, u8>>;

    /// Computes, for every instruction of a block, the registers a later
    /// instruction reads once it has executed.
    ///
    /// # Arguments
    ///
    /// * `ctx` - The convention and the function's state.
    /// * `instrs` - The block's instructions.
    /// * `out` - Registers live at the block's exit.
    ///
    /// # Returns
    ///
    /// One need map per instruction, indexed like `instrs`.
    fn need_after(
        ctx: &Ctx<'_>,
        instrs: &[Self::Insn],
        out: &FxHashMap<Key, u8>,
    ) -> Vec<FxHashMap<Key, u8>>;

    /// Returns the first instruction of a block a call ending its
    /// predecessor returns into, for the call to see what reads its result.
    ///
    /// # Arguments
    ///
    /// * `code` - Each block's instructions.
    /// * `s` - The successor block.
    ///
    /// # Returns
    ///
    /// The x86 instruction ([`BlockFacts::after`]), `None` when the block is
    /// empty or the instruction set reads results some other way.
    fn after(code: &[Vec<Self::Insn>], s: usize) -> Option<Instruction>;

    /// Tells whether block `b` is where the prologue saves registers.
    ///
    /// # Arguments
    ///
    /// * `ctx` - The function's state, for its entry block.
    /// * `code` - Each block's instructions.
    /// * `b` - The block.
    fn prologue_block(ctx: &Ctx<'_>, code: &[Vec<Self::Insn>], b: usize) -> bool;

    /// Counts the instructions of a block that render as statements, which
    /// the structurer weighs copying a block by.
    ///
    /// # Arguments
    ///
    /// * `instrs` - The block's instructions.
    fn body_len(instrs: &[Self::Insn]) -> usize;

    /// Tells whether the function runs under a structured exception handler
    /// whose bookkeeping renders as nothing.
    ///
    /// # Arguments
    ///
    /// * `ctx` - Names, for a frame helper.
    /// * `code` - Each block's instructions.
    fn seh_frame(ctx: &Ctx<'_>, code: &[Vec<Self::Insn>]) -> bool;

    /// Finds a Go function's stack-growth check, which the lifter folds.
    ///
    /// # Arguments
    ///
    /// * `ctx` - The function's names.
    /// * `entry` - The function's entry.
    /// * `code` - Each block's instructions.
    /// * `idx` - Block index by start address.
    ///
    /// # Returns
    ///
    /// The check's branch and the header's note of it, or `None`.
    fn go_check(
        ctx: &Ctx<'_>,
        entry: u64,
        code: &[Vec<Self::Insn>],
        idx: &BTreeMap<u64, usize>,
    ) -> Option<(u64, String)>;

    /// Reads what the function takes, once per function and overlay where
    /// the memo has it.
    ///
    /// # Arguments
    ///
    /// * `ctx` - The function's context; its convention is set to the one
    ///   the parameters show.
    /// * `f` - The function.
    /// * `code` - Each block's instructions.
    /// * `succs` - Successor block indices per block.
    /// * `entry` - Index of the entry block.
    ///
    /// # Returns
    ///
    /// The function's parameters ([`Shape`]).
    fn shape(
        ctx: &mut Ctx<'_>,
        f: &Function,
        code: &[Vec<Self::Insn>],
        succs: &[Vec<usize>],
        entry: usize,
    ) -> std::sync::Arc<Shape>;

    /// Returns the state at the function's entry: its parameters in their
    /// registers, and what a scenario fixes.
    ///
    /// # Arguments
    ///
    /// * `ctx` - The convention, the parameters and the scenario.
    fn entry_env(ctx: &Ctx<'_>) -> Env;

    /// Tells whether an instruction other than a call writes the register a
    /// result comes back in.
    ///
    /// # Arguments
    ///
    /// * `ctx` - The function's state.
    /// * `code` - Each block's instructions.
    fn writes_result(ctx: &Ctx<'_>, code: &[Vec<Self::Insn>]) -> bool;

    /// Returns the width in bits of the value a return hands back.
    ///
    /// # Arguments
    ///
    /// * `code` - Each block's instructions.
    /// * `succs` - Successor block indices per block.
    /// * `declared` - The signature's return type when one is known.
    /// * `analysis` - The functions a jump out of the function may enter.
    fn ret_lane(
        code: &[Vec<Self::Insn>],
        succs: &[Vec<usize>],
        declared: Option<&str>,
        analysis: &Analysis,
    ) -> u8;

    /// Infers the pointer and floating-point parameters from how the body
    /// reads them.
    ///
    /// # Arguments
    ///
    /// * `ctx` - The function's state, its parameters among it.
    /// * `code` - Each block's instructions.
    /// * `succs` - Successor block indices per block.
    /// * `entry` - Index of the entry block.
    ///
    /// # Returns
    ///
    /// The C type per parameter position, for the positions the body shows
    /// a type for.
    fn param_types(
        ctx: &Ctx<'_>,
        code: &[Vec<Self::Insn>],
        succs: &[Vec<usize>],
        entry: usize,
    ) -> BTreeMap<usize, String>;

    /// Wraps a function's blocks for the check of its text ([`replay`]).
    ///
    /// # Arguments
    ///
    /// * `code` - Each block's instructions.
    fn witness(code: Vec<Vec<Self::Insn>>) -> replay::Code;

    /// Names the registers a result and a second result come back in, as
    /// the text names them.
    ///
    /// # Arguments
    ///
    /// * `bitness` - The register width: 32 or 64.
    fn result_names(bitness: u32) -> (&'static str, &'static str);
}

/// x86 and x86-64, decoded by iced-x86 and lifted by [`lift`].
pub(super) struct X86;

impl Lifter for X86 {
    type Insn = Instruction;

    fn decode_blocks(ctx: &Ctx<'_>, f: &Function) -> Vec<Vec<Instruction>> {
        decode_blocks(ctx, f)
    }

    fn start(i: &Instruction) -> u64 {
        i.ip()
    }

    fn exec_block(
        ctx: &mut Ctx<'_>,
        instrs: &[Instruction],
        prev: Option<&[Instruction]>,
        env: &mut Env,
        pass: lift::Pass,
        phi: Option<(&lift::PhiFn<'_>, &lift::LiveFn<'_>)>,
        facts: BlockFacts<'_>,
    ) -> BlockOut {
        exec_block(ctx, instrs, prev, env, pass, phi, facts)
    }

    fn reads_inherited_flags(instrs: &[Instruction]) -> bool {
        reads_inherited_flags(instrs)
    }

    fn join_reader_cc(instrs: &[Instruction]) -> Option<Cc> {
        join_reader_cc(instrs)
    }

    fn live_in(
        ctx: &Ctx<'_>,
        code: &[Vec<Instruction>],
        succs: &[Vec<usize>],
    ) -> Vec<FxHashMap<Key, u8>> {
        lift::live_in(ctx, code, succs)
    }

    fn need_after(
        ctx: &Ctx<'_>,
        instrs: &[Instruction],
        out: &FxHashMap<Key, u8>,
    ) -> Vec<FxHashMap<Key, u8>> {
        lift::need_after(ctx, instrs, out)
    }

    fn after(code: &[Vec<Instruction>], s: usize) -> Option<Instruction> {
        code.get(s)?.first().copied()
    }

    fn prologue_block(ctx: &Ctx<'_>, code: &[Vec<Instruction>], b: usize) -> bool {
        prologue_block(ctx, code, b)
    }

    fn body_len(instrs: &[Instruction]) -> usize {
        body_len(instrs)
    }

    fn seh_frame(ctx: &Ctx<'_>, code: &[Vec<Instruction>]) -> bool {
        seh_frame(ctx, code)
    }

    fn go_check(
        ctx: &Ctx<'_>,
        entry: u64,
        code: &[Vec<Instruction>],
        idx: &BTreeMap<u64, usize>,
    ) -> Option<(u64, String)> {
        go_stack_check(ctx, entry, code, idx)
    }

    fn shape(
        ctx: &mut Ctx<'_>,
        f: &Function,
        code: &[Vec<Instruction>],
        succs: &[Vec<usize>],
        entry: usize,
    ) -> std::sync::Arc<Shape> {
        callee_shape(ctx, f.entry)
            .unwrap_or_else(|| std::sync::Arc::new(shape_of(ctx, f, code, succs, entry)))
    }

    fn entry_env(ctx: &Ctx<'_>) -> Env {
        entry_env(ctx)
    }

    fn writes_result(ctx: &Ctx<'_>, code: &[Vec<Instruction>]) -> bool {
        writes_rax(ctx, code)
    }

    fn ret_lane(
        code: &[Vec<Instruction>],
        succs: &[Vec<usize>],
        declared: Option<&str>,
        analysis: &Analysis,
    ) -> u8 {
        lift::ret_lane(code, succs, declared, analysis)
    }

    fn param_types(
        ctx: &Ctx<'_>,
        code: &[Vec<Instruction>],
        succs: &[Vec<usize>],
        entry: usize,
    ) -> BTreeMap<usize, String> {
        param_types(ctx, code, succs, entry)
    }

    fn witness(code: Vec<Vec<Instruction>>) -> replay::Code {
        replay::Code::X86(code)
    }

    fn result_names(bitness: u32) -> (&'static str, &'static str) {
        if bitness == 64 {
            ("rax", "rdx")
        } else {
            ("eax", "edx")
        }
    }
}

/// AArch64, decoded by [`crate::isa::a64`] and lifted by [`lift_a64`]
/// under the arm64 procedure call standard.
pub(super) struct A64;

impl Lifter for A64 {
    type Insn = a64::Insn;

    fn decode_blocks(ctx: &Ctx<'_>, f: &Function) -> Vec<Vec<a64::Insn>> {
        lift_a64::decode_blocks(ctx, f)
    }

    fn start(i: &a64::Insn) -> u64 {
        i.va
    }

    fn exec_block(
        ctx: &mut Ctx<'_>,
        instrs: &[a64::Insn],
        _prev: Option<&[a64::Insn]>,
        env: &mut Env,
        pass: lift::Pass,
        phi: Option<(&lift::PhiFn<'_>, &lift::LiveFn<'_>)>,
        facts: BlockFacts<'_>,
    ) -> BlockOut {
        lift_a64::exec_block_a64(ctx, instrs, env, pass, phi, facts)
    }

    fn reads_inherited_flags(instrs: &[a64::Insn]) -> bool {
        lift_a64::reads_inherited_flags(instrs)
    }

    fn join_reader_cc(_instrs: &[a64::Insn]) -> Option<Cc> {
        None
    }

    fn live_in(
        ctx: &Ctx<'_>,
        code: &[Vec<a64::Insn>],
        succs: &[Vec<usize>],
    ) -> Vec<FxHashMap<Key, u8>> {
        let effects: Vec<Vec<lift::Effects>> = code
            .iter()
            .map(|b| b.iter().map(|i| lift_a64::effects(ctx, i)).collect())
            .collect();
        lift::live_from(&effects, succs)
    }

    fn need_after(
        ctx: &Ctx<'_>,
        instrs: &[a64::Insn],
        out: &FxHashMap<Key, u8>,
    ) -> Vec<FxHashMap<Key, u8>> {
        let effects: Vec<lift::Effects> =
            instrs.iter().map(|i| lift_a64::effects(ctx, i)).collect();
        lift::need_from(&effects, out)
    }

    fn after(_code: &[Vec<a64::Insn>], _s: usize) -> Option<Instruction> {
        None
    }

    fn prologue_block(ctx: &Ctx<'_>, _code: &[Vec<a64::Insn>], b: usize) -> bool {
        b == ctx.entry_block
    }

    fn body_len(instrs: &[a64::Insn]) -> usize {
        lift_a64::body_len(instrs)
    }

    fn seh_frame(_ctx: &Ctx<'_>, _code: &[Vec<a64::Insn>]) -> bool {
        false
    }

    fn go_check(
        _ctx: &Ctx<'_>,
        _entry: u64,
        _code: &[Vec<a64::Insn>],
        _idx: &BTreeMap<u64, usize>,
    ) -> Option<(u64, String)> {
        None
    }

    fn shape(
        ctx: &mut Ctx<'_>,
        f: &Function,
        code: &[Vec<a64::Insn>],
        succs: &[Vec<usize>],
        entry: usize,
    ) -> std::sync::Arc<Shape> {
        lift_a64::callee_shape(ctx, f.entry)
            .unwrap_or_else(|| std::sync::Arc::new(lift_a64::shape(ctx, f, code, succs, entry)))
    }

    fn entry_env(ctx: &Ctx<'_>) -> Env {
        lift_a64::entry_env(ctx)
    }

    fn writes_result(ctx: &Ctx<'_>, code: &[Vec<a64::Insn>]) -> bool {
        lift_a64::writes_result(ctx, code)
    }

    fn ret_lane(
        code: &[Vec<a64::Insn>],
        succs: &[Vec<usize>],
        declared: Option<&str>,
        _analysis: &Analysis,
    ) -> u8 {
        lift_a64::ret_lane(code, succs, declared)
    }

    fn param_types(
        ctx: &Ctx<'_>,
        code: &[Vec<a64::Insn>],
        _succs: &[Vec<usize>],
        entry: usize,
    ) -> BTreeMap<usize, String> {
        lift_a64::param_types(ctx, code, entry)
    }

    fn witness(code: Vec<Vec<a64::Insn>>) -> replay::Code {
        replay::Code::A64(code)
    }

    fn result_names(_bitness: u32) -> (&'static str, &'static str) {
        ("x0", "x1")
    }
}
