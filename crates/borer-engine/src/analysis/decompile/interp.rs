//! The printed text run as C: a function's decompiled pseudo-C executed on
//! the inputs the binary runs on, so the two answers can be compared.
//!
//! The text is read as the C it claims to be, on the machine the binary
//! runs on. A register-named variable is a C variable that starts with
//! what the register held at entry. A stack slot (`local_N`, `home_N`,
//! `arg_N`) and a parameter passed on the stack live in memory at their
//! frame offset, so two that overlap share bytes, as the text's overlap
//! notes say they do. A global declared `// @ addr` lives at that address,
//! `p->field_0xN` is the bytes N past `p` at the width the layout line
//! gives, and a string literal is where the image holds those bytes.
//! Expressions follow C: the integer promotions, the usual conversions,
//! a pointer stepped by its pointee's size (a `void *` by bytes, as GNU C
//! steps one), a comparison giving `int`. The integer operators are the
//! lifter's own ([`fold`], [`unary`]) at the width C computes at, so the
//! text and the lifter agree on what `>>` and `/` do.
//!
//! A call runs the callee on the same memory in the emulator, from a frame
//! below the text's, with the arguments the text passes and every other
//! register what the text's variable of its name holds, or zero: an
//! import's stub answers it as it answers the binary, and an argument
//! register the text does not pass is not passed. What this cannot
//! run (a vector value, an intrinsic it does not model, a virtual call, a
//! field the layout does not size) stops the run and says which line it
//! was, rather than guessing: the answer is then unchecked, never wrong.
//!
//! In ISO mode ([`Mode::Iso`]) the text is read as ISO C instead, with no
//! machine leaking into its meaning. Each local stack slot (`local_N`, a
//! named local) is an object of its own, away from the frame, so two that
//! overlap no longer share bytes and a pointer past one reads nothing. A
//! variable no line set, and a byte of a local no line wrote, is poison:
//! reading it ends the run as [`End::Refused`], as does a name the text
//! never declares (a register, a parameter the signature does not list).
//! A callee gets the arguments the text passes and nothing of the text's
//! registers. The operators, conversions and builtins are the same.

use std::collections::BTreeMap;

use crate::isa::x86::Register;

use super::ctext::{
    Ast, Base, Bin, CTy, Tok, Un, closing, expression, float_bits, float_of, split_top, tokens,
};
use super::expr::{Expr, Op, TEB_FIELDS, Ty, UnOp, abs_bits, fold, unary};
use super::floats::integer_to_float;
use super::helper::{Helper, Operands, Yields, defines};
use super::line::is_param_name;
use super::signature::{Passing, Signature, passing, poke_word, printed};
use super::traces::{INTRINSICS, Stmt, blank, statements};
use crate::analysis::{Analysis, BlockTerm, Overlay, bare_name, name_of};
use crate::emulate::{Emulator, Stop};
use crate::fxmap::{FxHashMap, FxHashSet};
use crate::num::from_usize;
use crate::program::{Program, SymbolKind};

mod compile;

use compile::Compiler;

/// The return address a call from the text pushes: the emulator stops when
/// the callee returns to it, before fetching anything there.
const SENTINEL_64: u64 = 0x0000_5fff_0000_0000;

/// The return address of a call from the text on a 32-bit target.
const SENTINEL_32: u64 = 0x5fff_0000;

/// Bytes left between the text's lowest frame slot and a callee's frame.
const CALL_GAP: u64 = 0x100;

/// Most bytes a modeled `memset`, `memcpy` or `strlen` touches.
const BUILTIN_MAX: u64 = 1 << 20;

/// Most steps the closure check ([`Script::unset_reads`]) takes before it
/// gives up and flags nothing.
const UNSET_ROUNDS: usize = 1 << 20;

/// Steps the two verification runs of a solved constraint are given.
const SOLVE_BUDGET: usize = 50_000;

/// Where ISO mode places the first local object on a 64-bit target: memory
/// no image or stack takes, below the vector variables.
const ISO_BASE_64: u64 = 0x0000_5ffd_0000_0000;

/// Where ISO mode places the first local object on a 32-bit target.
const ISO_BASE_32: u64 = 0x5f00_0000;

/// Bytes between two local objects in ISO mode: room for the largest local
/// array, and a gap after it no other object starts in.
const ISO_STRIDE: u64 = 0x1000;

/// Where the blocks the text's `alloca` calls hand out start on a 64-bit
/// target: memory no image, stack or local object takes.
const ALLOCA_BASE_64: u64 = 0x0000_5ffc_0000_0000;

/// Where the text's `alloca` blocks start on a 32-bit target.
const ALLOCA_BASE_32: u64 = 0x5e00_0000;

/// Bytes left between two `alloca` blocks, past the alignment each starts
/// at.
const ALLOCA_GAP: u64 = 0x100;

/// How a script reads the text.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum Mode {
    /// As the machine runs it: slots share the frame, registers start as
    /// the machine's, a callee sees the text's registers.
    Machine,
    /// As ISO C: locals are objects of their own, a read of what no line
    /// set and a name no line declares are refused.
    Iso,
}

/// Bytes below a callee's frame its own stack reaches: a read there that
/// nothing set is the leftovers of earlier calls, not an argument.
const STACK_REACH: u64 = 1 << 20;

/// Where a name the text uses holds its value.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Slot {
    /// A C variable: its index among the run's values.
    Var(usize),
    /// Memory at this address.
    Mem(u64),
}

/// A name the text gives a value: a declared variable, a parameter, a
/// global.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Variable {
    /// Its type.
    ty: CTy,
    /// Where its value is.
    slot: Slot,
}

/// A name the text uses that is neither variable nor parameter, resolved
/// once against the binary ([`resolve_names`]).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Known {
    /// A function: the name's value is its entry.
    Code(u64),
    /// A table or symbol named by its address (`crc_32_table`,
    /// `__ImageBase`): the name's value is that address.
    Address(u64),
    /// An import the text calls by name: the name's value is what its
    /// slot holds, the stub the machine answers it with.
    Slot(u64),
}

/// What one step of the compiled body does.
#[derive(Debug, Clone, PartialEq)]
enum Step {
    /// Evaluates an expression statement.
    Eval(Ast),
    /// Jumps to a label when the condition is false.
    Test(Ast, usize),
    /// Jumps to a label.
    Jump(usize),
    /// Jumps to the label of the case the value matches, else the default.
    Switch(Ast, Vec<(u64, usize)>, usize),
    /// Returns, with the value if any.
    Return(Option<Ast>),
    /// Ends the path: a trap.
    Halt,
    /// Leaves the function by a jump the text does not follow, `goto *x;`:
    /// what runs next is not in the text, so nothing past it is checked.
    Leave,
    /// A line this reader could not read, and why: reaching it stops the
    /// run unchecked.
    Unreadable(String),
}

/// One compiled step and the 1-based line it comes from.
#[derive(Debug, Clone, PartialEq)]
struct Op1 {
    /// The line.
    line: usize,
    /// The step.
    step: Step,
}

/// The register a variable is named after, for the full-width general
/// registers the emulator knows.
///
/// # Arguments
///
/// * `name` - The variable's name.
fn named_register(name: &str) -> Option<Register> {
    Some(match name {
        "rax" | "eax" => Register::RAX,
        "rbx" | "ebx" => Register::RBX,
        "rcx" | "ecx" => Register::RCX,
        "rdx" | "edx" => Register::RDX,
        "rsi" | "esi" => Register::RSI,
        "rdi" | "edi" => Register::RDI,
        "rbp" | "ebp" => Register::RBP,
        "rsp" | "esp" => Register::RSP,
        "r8" => Register::R8,
        "r9" => Register::R9,
        "r10" => Register::R10,
        "r11" => Register::R11,
        "r12" => Register::R12,
        "r13" => Register::R13,
        "r14" => Register::R14,
        "r15" => Register::R15,
        _ => return None,
    })
}

/// Returns the width of the byte or word a function hands back, as the
/// lifter reads a call to it.
///
/// Its declared signature's, else the width its callers and its exits
/// agree on ([`Function::ret_width`](crate::analysis::Function::ret_width)).
///
/// # Arguments
///
/// * `analysis` - The functions.
/// * `target` - The callee's entry.
///
/// # Returns
///
/// 8 or 16, or `None` when the result fills the register or nothing is
/// known of it.
fn returned_bits(analysis: &Analysis, target: u64) -> Option<u8> {
    let f = analysis.function(target).filter(|f| f.entry == target)?;
    let bits = match &f.signature {
        Some(sig) => super::lift::declared_bits(&sig.ret),
        None => f.ret_width?,
    };
    (bits <= 16).then_some(bits)
}

/// The emulator's name of the full general register a register lives in.
///
/// # Arguments
///
/// * `r` - The register, any width.
fn full_register_name(r: Register) -> Option<&'static str> {
    Some(match r.full_register() {
        Register::RAX => "rax",
        Register::RBX => "rbx",
        Register::RCX => "rcx",
        Register::RDX => "rdx",
        Register::RSI => "rsi",
        Register::RDI => "rdi",
        Register::RBP => "rbp",
        Register::R8 => "r8",
        Register::R9 => "r9",
        Register::R10 => "r10",
        Register::R11 => "r11",
        Register::R12 => "r12",
        Register::R13 => "r13",
        Register::R14 => "r14",
        Register::R15 => "r15",
        _ => return None,
    })
}

/// A mask of the low `bits`.
///
/// # Arguments
///
/// * `bits` - The width.
fn mask(bits: u8) -> u64 {
    if bits >= 64 {
        u64::MAX
    } else {
        (1u64 << bits) - 1
    }
}

/// Sign-extends the low `bits` of a value.
///
/// # Arguments
///
/// * `v` - The value.
/// * `bits` - The width, 1 to 64.
fn sext(v: u64, bits: u8) -> u64 {
    if bits == 0 || bits >= 64 {
        return v;
    }
    let shift = 64 - u32::from(bits);
    ((v << shift).cast_signed() >> shift).cast_unsigned()
}

/// The integer a double converts to: toward zero, and to the integer
/// indefinite the processor gives (the most negative value) when it is a
/// NaN or does not fit.
///
/// An 8-bit, 16-bit or 32-bit destination uses that width's signed range.
/// A wider one uses the signed 64-bit range, then keeps the low `bits`.
///
/// # Arguments
///
/// * `f` - The double.
/// * `bits` - The integer's width.
#[expect(
    clippy::cast_possible_truncation,
    clippy::cast_precision_loss,
    reason = "the range check guarantees the truncated value fits, and a power-of-two bound converts exactly"
)]
fn float_to_int(f: f64, bits: u8) -> u64 {
    let t = f.trunc();
    let bits = bits.clamp(1, 64);
    if matches!(bits, 8 | 16 | 32) {
        let shift = u32::from(bits) - 1;
        let top = (1u64 << shift) as f64;
        if t.is_nan() || t < -top || t >= top {
            return 1u64 << shift;
        }
    } else if t.is_nan()
        || !(-9_223_372_036_854_775_808.0..9_223_372_036_854_775_808.0).contains(&t)
    {
        if bits < 2 {
            return 1;
        }
        return 1u64 << (u32::from(bits) - 1);
    }
    (t as i64).cast_unsigned() & mask(bits)
}

/// A value and its C type; an integer's bits are masked to its width, a
/// float's are its IEEE-754 encoding.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Val {
    /// The bits.
    bits: u64,
    /// The type.
    ty: CTy,
}

/// Why a run of the text ended.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum End {
    /// A `return`, with its value at the return type's width, `None` for a
    /// function that returns nothing.
    Returned(Option<u64>),
    /// The text ends the path: a trap, or a jump through a pointer.
    Trap,
    /// A read or a write of memory nothing backs.
    Fault(u64),
    /// The step budget ran out.
    Budget,
    /// A callee did not return: its name and how it stopped.
    Callee(String, Stop),
    /// Something this reader does not run.
    Unchecked(String),
    /// A read ISO C does not define, in [`Mode::Iso`]: a variable or a
    /// local's byte no line set, or a name the text never declares.
    Refused(String),
}

/// What running the text on one input did.
#[derive(Debug)]
pub(crate) struct TextRun<'p> {
    /// Why it ended.
    pub(crate) end: End,
    /// The 1-based line it ended at.
    pub(crate) line: usize,
    /// Statements run, and steps the callees took.
    pub(crate) steps: usize,
    /// The machine as the text left it: its memory and the imports called.
    pub(crate) emu: Emulator<'p>,
    /// The last line that wrote each byte, a call's line for what its
    /// callee wrote.
    pub(crate) writers: BTreeMap<u64, usize>,
    /// For a return, each variable its value read and the line that last
    /// set it, zero for a variable no line set.
    pub(crate) sources: Vec<(String, usize)>,
    /// The stack pointer the text was entered with, the base of its frame.
    pub(crate) entry_sp: u64,
    /// The addresses the text's string literals were given: the first copy
    /// of their bytes, which need not be the copy the binary uses.
    pub(crate) literals: Vec<u64>,
    /// The width the returned value was held at before its conversion to
    /// the declared return type, when that is a byte or a word.
    pub(crate) ret_lane: Option<u8>,
}

/// A function's text, read once and run on any number of inputs.
#[derive(Debug)]
pub(crate) struct Script<'p> {
    /// The loaded image.
    program: &'p Program,
    /// Its functions.
    analysis: &'p Analysis,
    /// The machine word in bits.
    word: u8,
    /// The compiled body.
    ops: Vec<Op1>,
    /// Each label's step.
    targets: Vec<usize>,
    /// The names that hold values, with where.
    vars: FxHashMap<String, Variable>,
    /// The variables declared as arrays: their name is their address.
    arrays: FxHashSet<String>,
    /// Each C variable's name and the register it starts as, by index.
    cells: Vec<(String, Option<Register>, CTy)>,
    /// Field widths by base and offset, from the layout lines.
    layouts: FxHashMap<String, FxHashMap<u64, CTy>>,
    /// The names that are neither variables nor parameters, resolved.
    known: FxHashMap<String, Known>,
    /// Enumerator names the function's own `// enum` header lists, and the
    /// constants they stand for. A `case` of one is that constant.
    enumerators: FxHashMap<String, u64>,
    /// Each string literal's address in the image, `None` when the image
    /// does not hold it as written.
    literals: FxHashMap<Vec<u8>, Option<u64>>,
    /// The signature the text prints.
    sig: Signature,
    /// How the function takes its arguments.
    passing: Passing,
    /// How each callee the text names takes its arguments.
    callees: FxHashMap<u64, Passing>,
    /// The stack pointer at entry, the base of the frame offsets.
    entry_sp: u64,
    /// The lowest frame address a declared slot stands at: reads of the
    /// frame this side of it the machine answers with the fresh stack's
    /// zeros, and the text does too.
    frame_low: u64,
    /// The thread block the machine plants, which `NtCurrentTeb()` is.
    teb: u64,
    /// The memory of each 128-bit register variable, zero at entry.
    wide: Vec<u64>,
    /// The stack pointer a call from the text enters its callee with.
    call_sp: u64,
    /// How the text is read.
    mode: Mode,
    /// Per C variable, whether it holds an input at entry (a parameter,
    /// the stack pointer) rather than poison.
    inputs: Vec<bool>,
    /// The addresses ISO mode's local objects take, start included and end
    /// excluded; empty in [`Mode::Machine`].
    objects: (u64, u64),
}

/// The tokens of the parenthesized group after the keyword `word` in a
/// line, without the parentheses.
///
/// # Arguments
///
/// * `toks` - The line's tokens.
/// * `word` - `if`, `while`, `switch` or `for`.
fn group_after<'t>(toks: &'t [Tok], word: &str) -> Option<&'t [Tok]> {
    let at = toks
        .iter()
        .position(|t| matches!(t, Tok::Name(n) if n == word))?;
    let open = at + 1;
    if toks.get(open) != Some(&Tok::Punct("(")) {
        return None;
    }
    let close = closing(toks, open)?;
    toks.get(open + 1..close)
}

/// A statement's tokens without what structures it on its line: a leading
/// `if (c)` whose arm it is, and the `case` and `default` labels of a
/// switch arm it starts.
///
/// # Arguments
///
/// * `toks` - The line's tokens.
fn statement_part(toks: &[Tok]) -> &[Tok] {
    let mut rest = toks;
    if matches!(rest.first(), Some(Tok::Name(n)) if n == "if")
        && let Some(close) = closing(rest, 1)
    {
        rest = rest.get(close + 1..).unwrap_or(&[]);
    }
    loop {
        match rest.first() {
            Some(Tok::Name(n)) if n == "case" => {
                let colon = rest
                    .iter()
                    .position(|t| *t == Tok::Punct(":"))
                    .unwrap_or(rest.len());
                rest = rest.get(colon + 1..).unwrap_or(&[]);
            }
            Some(Tok::Name(n)) if n == "default" && rest.get(1) == Some(&Tok::Punct(":")) => {
                rest = rest.get(2..).unwrap_or(&[]);
            }
            _ => return rest,
        }
    }
}

/// The value of a constant case label: a literal, negated or cast.
///
/// # Arguments
///
/// * `e` - The label's expression.
fn constant(e: &Ast) -> Option<u64> {
    match e {
        Ast::Int(v, _) => Some(*v),
        Ast::Un(Un::Neg, inner) => constant(inner).map(u64::wrapping_neg),
        Ast::Un(Un::Plus, inner) | Ast::Cast(_, inner) => constant(inner),
        _ => None,
    }
}

/// The frame offset a stack slot's name stands for: `local_N` below the
/// return address, `retaddr` at it, `home_N` and `arg_N` past it.
///
/// # Arguments
///
/// * `name` - The name.
/// * `word` - The stack word in bytes.
fn slot_offset(name: &str, word: u64) -> Option<i64> {
    let hex = |h: &str| {
        u64::from_str_radix(h, 16)
            .ok()
            .and_then(|v| i64::try_from(v).ok())
    };
    if name == "retaddr" {
        return Some(0);
    }
    if let Some(h) = name.strip_prefix("local_") {
        return hex(h).map(i64::wrapping_neg);
    }
    let h = name
        .strip_prefix("home_")
        .or_else(|| name.strip_prefix("arg_"))?;
    hex(h).map(|v| v.wrapping_add(i64::try_from(word).unwrap_or(8)))
}

/// The frame offset a debug-named local stands for, read back from the
/// function's own record: the name carries no offset the way a synthesized
/// one does, so the record states where it sits.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `entry` - The function the text decompiled.
/// * `name` - The declared name.
///
/// # Returns
///
/// The slot offset the debug information states for the name, or `None`
/// when the function's record names no local so.
fn debug_local(program: &Program, entry: u64, name: &str) -> Option<i64> {
    program
        .debug_functions
        .iter()
        .find(|d| d.low_pc == entry)
        .and_then(|d| {
            d.locals
                .iter()
                .find(|(_, n)| n.as_str() == name)
                .map(|(off, _)| *off)
        })
}

/// The frame offset a local an agent named stands for
/// ([`Overlay::vars`]), read back from the overlay the text was written
/// under, as [`debug_local`] reads a debug-named one.
///
/// # Arguments
///
/// * `overlay` - The overlay the text was written under.
/// * `entry` - The function the text decompiled.
/// * `name` - The declared name.
///
/// # Returns
///
/// The slot offset, or `None` when no stated variable of the function is
/// a stack slot so named.
fn stated_local(overlay: &Overlay, entry: u64, name: &str) -> Option<i64> {
    overlay
        .vars
        .get(&entry)?
        .iter()
        .find_map(|(key, var)| match key {
            crate::analysis::protos::VarKey::Slot(off) if var.name == name => Some(*off),
            crate::analysis::protos::VarKey::Param(_)
            | crate::analysis::protos::VarKey::Slot(_) => None,
        })
}

/// The type a layout line's width letter spells.
///
/// # Arguments
///
/// * `letter` - `u8` .. `u128`, `i8` .. `i64`, `f32` or `f64`.
fn layout_letter(letter: &str) -> Option<CTy> {
    Some(match letter {
        "u8" => CTy::int(8, false),
        "u16" => CTy::int(16, false),
        "u32" => CTy::int(32, false),
        "u64" => CTy::int(64, false),
        "i8" => CTy::int(8, true),
        "i16" => CTy::int(16, true),
        "i32" => CTy::int(32, true),
        "i64" => CTy::int(64, true),
        "f32" => CTy::of(Base::Float(32)),
        "f64" => CTy::of(Base::Float(64)),
        "u128" => CTy::of(Base::Wide),
        _ => return None,
    })
}

/// The address and type a global's generated name spells: `g32_1800c1230`
/// is the 32-bit value at `0x1800c1230`.
///
/// # Arguments
///
/// * `name` - The name.
fn global_name(name: &str) -> Option<(u64, CTy)> {
    let (bits, hex) = name.strip_prefix('g')?.split_once('_')?;
    let ty = match bits {
        "8" => CTy::int(8, false),
        "16" => CTy::int(16, false),
        "32" => CTy::int(32, false),
        "64" => CTy::int(64, false),
        "128" => CTy::of(Base::Wide),
        _ => return None,
    };
    Some((u64::from_str_radix(hex, 16).ok()?, ty))
}

/// The bytes a 128-bit value takes.
const WIDE_BYTES: u64 = 16;

/// Where the 128-bit register variables live: memory no image or stack
/// takes, one [`WIDE_BYTES`] apart, so a copy of one is a copy of bytes.
const WIDE_BASE_64: u64 = 0x0000_5ffe_0000_0000;

/// Where the 128-bit register variables live on a 32-bit target.
const WIDE_BASE_32: u64 = 0x5ffe_0000;

/// Tells whether evaluating an expression has no effect: no assignment,
/// step or call in it, so it may be evaluated twice.
///
/// # Arguments
///
/// * `e` - The expression.
fn pure(e: &Ast) -> bool {
    match e {
        Ast::Assign(..) | Ast::Step(..) | Ast::Call(..) => false,
        Ast::Int(..) | Ast::Float(..) | Ast::Str(_) | Ast::Name(_) => true,
        Ast::Un(_, a) | Ast::Cast(_, a) | Ast::Arrow(a, _) => pure(a),
        Ast::Bin(_, a, b) | Ast::Logic(_, a, b) | Ast::Index(a, b) => pure(a) && pure(b),
        Ast::Pick(c, m, o) => pure(c) && m.as_deref().is_none_or(pure) && pure(o),
    }
}

/// The pieces of a decompiled function's header the run needs beside its
/// signature.
#[derive(Debug, Default)]
struct Header {
    /// Declared names: type, and the address a global's `// @` gives.
    declared: Vec<(String, CTy, Option<u64>)>,
    /// The declared names that are arrays (`uint32_t local_28[8]`), whose
    /// name reads as the address of their first element.
    arrays: FxHashSet<String>,
    /// Field widths by base and offset.
    layouts: FxHashMap<String, FxHashMap<u64, CTy>>,
}

/// Reads the header of a decompiled function beside its signature: its
/// layout lines and its declarations, the lines before the first blank.
///
/// # Arguments
///
/// * `lines` - The header's lines.
/// * `word` - The machine word in bits.
///
/// # Errors
///
/// When a declaration does not tokenize.
fn header(lines: &[&str], word: u8) -> Result<Header, String> {
    let mut h = Header::default();
    let mut layout_base: Option<String> = None;
    for raw in lines {
        let t = raw.trim();
        let layout = t
            .strip_prefix("// layout ")
            .and_then(|l| l.split_once(':'))
            .map(|(base, rest)| (Some(base.trim().to_owned()), rest))
            .or_else(|| {
                t.strip_prefix("//  ")
                    .filter(|_| layout_base.is_some())
                    .map(|rest| (None, rest))
            });
        if let Some((base, rest)) = layout {
            if let Some(b) = base {
                layout_base = Some(b);
            }
            let Some(b) = layout_base.clone() else {
                continue;
            };
            for item in rest.split(',') {
                let mut words = item.split_whitespace();
                let (Some(off), Some(letter)) = (words.next(), words.next()) else {
                    continue;
                };
                let Some(off) = crate::analysis::parse_addr(off) else {
                    continue;
                };
                if let Some(ty) = layout_letter(letter) {
                    h.layouts.entry(b.clone()).or_default().insert(off, ty);
                }
            }
            continue;
        }
        layout_base = None;
        if t.starts_with("//") || t.is_empty() {
            continue;
        }
        let at = t
            .split_once("// @ ")
            .and_then(|(_, a)| crate::analysis::parse_addr(a.trim()));
        let toks = tokens(t)?;
        let Some((base, used)) = super::ctext::leading_type(&toks, word) else {
            continue;
        };
        for decl in split_top(toks.get(used..).unwrap_or(&[]), ",") {
            let stars = decl
                .iter()
                .take_while(|t| matches!(t, Tok::Punct("*")))
                .count();
            if let Some(Tok::Name(n)) = decl.get(stars) {
                let ty = (0..stars).fold(base, |t, _| t.to());
                if matches!(decl.get(stars + 1), Some(Tok::Punct("["))) {
                    h.arrays.insert(n.clone());
                }
                h.declared.push((n.clone(), ty, at));
            }
        }
    }
    Ok(h)
}

/// Every name an expression reads, in order.
///
/// # Arguments
///
/// * `e` - The expression.
/// * `out` - Collects the names.
fn names_in<'e>(e: &'e Ast, out: &mut Vec<&'e str>) {
    match e {
        Ast::Name(n) => out.push(n),
        Ast::Int(..) | Ast::Float(..) | Ast::Str(_) => {}
        Ast::Un(_, a) | Ast::Cast(_, a) | Ast::Arrow(a, _) | Ast::Step(_, _, a) => names_in(a, out),
        Ast::Bin(_, a, b) | Ast::Logic(_, a, b) | Ast::Index(a, b) | Ast::Assign(_, a, b) => {
            names_in(a, out);
            names_in(b, out);
        }
        Ast::Pick(c, m, o) => {
            names_in(c, out);
            if let Some(m) = m {
                names_in(m, out);
            }
            names_in(o, out);
        }
        Ast::Call(f, args) => {
            names_in(f, out);
            for a in args {
                names_in(a, out);
            }
        }
    }
}

/// Every string literal an expression holds.
///
/// # Arguments
///
/// * `e` - The expression.
/// * `out` - Collects them.
fn strings_in<'e>(e: &'e Ast, out: &mut Vec<&'e [u8]>) {
    match e {
        Ast::Str(s) => out.push(s),
        Ast::Name(_) | Ast::Int(..) | Ast::Float(..) => {}
        Ast::Un(_, a) | Ast::Cast(_, a) | Ast::Arrow(a, _) | Ast::Step(_, _, a) => {
            strings_in(a, out);
        }
        Ast::Bin(_, a, b) | Ast::Logic(_, a, b) | Ast::Index(a, b) | Ast::Assign(_, a, b) => {
            strings_in(a, out);
            strings_in(b, out);
        }
        Ast::Pick(c, m, o) => {
            strings_in(c, out);
            if let Some(m) = m {
                strings_in(m, out);
            }
            strings_in(o, out);
        }
        Ast::Call(f, args) => {
            strings_in(f, out);
            for a in args {
                strings_in(a, out);
            }
        }
    }
}

/// Longest literal the index of an image's literals keys, in bytes.
const LITERAL_MAX: usize = 512;

/// Each string literal an image holds outside code, by its bytes with the
/// terminator, and the address of its first copy.
///
/// A literal starts where a section does or after a zero, narrow ones at
/// any byte and wide ones at an even offset, and runs over the bytes a
/// literal can spell to its terminator; the decompiler prints the literal
/// an address starts, which is one of these unless it points into the
/// middle of one.
///
/// # Arguments
///
/// * `program` - The loaded image.
fn literals(program: &Program) -> FxHashMap<Vec<u8>, u64> {
    let mut out: FxHashMap<Vec<u8>, u64> = FxHashMap::default();
    for s in program.sections.iter().filter(|s| !s.executable) {
        let Some(bytes) = program.read_va_upto(s.va.0, usize::try_from(s.file_size).unwrap_or(0))
        else {
            continue;
        };
        for (at, &b) in bytes.iter().enumerate() {
            let starts = at == 0 || bytes.get(at - 1) == Some(&0);
            if starts && crate::strings::literal_byte(b) {
                let run = bytes.get(at..).unwrap_or(&[]);
                if let Some(end) = run.iter().take(LITERAL_MAX).position(|c| *c == 0)
                    && let Some(key) = run.get(..=end)
                    && key
                        .iter()
                        .take(end)
                        .copied()
                        .all(crate::strings::literal_byte)
                {
                    out.entry(key.to_vec())
                        .or_insert(s.va.0.wrapping_add(from_usize(at)));
                }
            }
            let wide_starts = at % 2 == 0 && (at == 0 || bytes.get(at - 2..at) == Some(&[0, 0]));
            if wide_starts && crate::strings::literal_byte(b) && bytes.get(at + 1) == Some(&0) {
                let run = bytes.get(at..).unwrap_or(&[]);
                let units = run.chunks_exact(2).take(LITERAL_MAX / 2);
                if let Some(end) = units.clone().position(|u| u == [0, 0])
                    && let Some(key) = run.get(..end * 2 + 2)
                    && units.take(end).all(|u| {
                        u.get(1) == Some(&0)
                            && u.first().is_some_and(|c| crate::strings::literal_byte(*c))
                    })
                {
                    out.entry(key.to_vec())
                        .or_insert(s.va.0.wrapping_add(from_usize(at)));
                }
            }
        }
    }
    out
}

/// Where the image holds a string literal's bytes, terminator included,
/// in memory that is no code.
///
/// The index of the image's literals ([`literals`]) answers, built once per
/// analysis; a literal it lacks, one the decompiler printed from an address
/// inside another, is searched for and the answer kept.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Its analysis, holding the memo.
/// * `bytes` - The literal's bytes.
fn literal_address(program: &Program, analysis: &Analysis, bytes: &[u8]) -> Option<u64> {
    let index = analysis
        .derived
        .get_or_build("text_literals", (), || literals(program));
    if let Some(at) = index.get(bytes) {
        return Some(*at);
    }
    *analysis
        .derived
        .get_or_build("text_literal", bytes.to_vec(), || {
            let pattern: Vec<Option<u8>> = bytes.iter().map(|b| Some(*b)).collect();
            crate::search::find_bytes(program, &pattern, 0)
                .hits
                .iter()
                .filter_map(|h| h.va)
                .find(|va| program.section_at(*va).is_some_and(|s| !s.executable))
        })
}

impl<'p> Script<'p> {
    /// Reads a function's decompiled text into a program to run.
    ///
    /// # Arguments
    ///
    /// * `program` - The loaded image.
    /// * `analysis` - Its functions.
    /// * `overlay` - The names the text was written under.
    /// * `entry` - The function's entry.
    /// * `text` - Its text, header first, as a decompile entry point wrote
    ///   it.
    ///
    /// # Errors
    ///
    /// When the header has no signature or the body does not nest. A line
    /// that does not read is no error here: it stops a run that reaches it.
    pub(crate) fn read(
        program: &'p Program,
        analysis: &'p Analysis,
        overlay: &Overlay,
        entry: u64,
        text: &str,
    ) -> Result<Self, String> {
        Self::read_as(program, analysis, overlay, entry, text, Mode::Machine)
    }

    /// Reads a function's decompiled text into a program to run as ISO C
    /// ([`Mode::Iso`]).
    ///
    /// # Arguments
    ///
    /// * `program` - The loaded image.
    /// * `analysis` - Its functions.
    /// * `overlay` - The names the text was written under.
    /// * `entry` - The function's entry.
    /// * `text` - Its text, header first.
    ///
    /// # Errors
    ///
    /// As [`Script::read`].
    pub(crate) fn read_iso(
        program: &'p Program,
        analysis: &'p Analysis,
        overlay: &Overlay,
        entry: u64,
        text: &str,
    ) -> Result<Self, String> {
        Self::read_as(program, analysis, overlay, entry, text, Mode::Iso)
    }

    /// Reads a function's decompiled text in one [`Mode`].
    ///
    /// # Arguments
    ///
    /// * `program` - The loaded image.
    /// * `analysis` - Its functions.
    /// * `overlay` - The names the text was written under.
    /// * `entry` - The function's entry.
    /// * `text` - Its text, header first.
    /// * `mode` - How to read it.
    ///
    /// # Errors
    ///
    /// As [`Script::read`].
    fn read_as(
        program: &'p Program,
        analysis: &'p Analysis,
        overlay: &Overlay,
        entry: u64,
        text: &str,
        mode: Mode,
    ) -> Result<Self, String> {
        let word = u8::try_from(program.arch.bitness().unwrap_or(64)).unwrap_or(64);
        let all: Vec<&str> = text
            .lines()
            .map(|l| if defines(l) { "//" } else { l })
            .collect();
        let base = all
            .iter()
            .position(|l| l.trim().is_empty())
            .map_or(0, |i| i + 1);
        let sig = printed(text, word)?;
        let head = header(all.get(..base).unwrap_or(&[]), word)?;
        let pass = passing(program, analysis, overlay, entry);
        let entry_sp = Emulator::entry_sp(program).ok_or("this architecture is not emulated")?;
        let mut vars: FxHashMap<String, Variable> = FxHashMap::default();
        let mut cells: Vec<(String, Option<Register>, CTy)> = Vec::new();
        let mut frame_low = entry_sp;
        let wbytes = u64::from(word / 8);
        for (i, (name, ty)) in sig.params.iter().enumerate() {
            let slot = if i < pass.regs.len() {
                cells.push((name.clone(), pass.regs.get(i).copied(), *ty));
                Slot::Var(cells.len() - 1)
            } else {
                Slot::Mem(entry_sp.wrapping_add(pass.stack_offset(i)))
            };
            vars.insert(name.clone(), Variable { ty: *ty, slot });
        }
        let wide_base = if program.is_64 {
            WIDE_BASE_64
        } else {
            WIDE_BASE_32
        };
        let mut wide: Vec<u64> = Vec::new();
        let iso_base = if program.is_64 {
            ISO_BASE_64
        } else {
            ISO_BASE_32
        };
        let mut objects = (iso_base, iso_base);
        for (name, ty, at) in &head.declared {
            let slot = if let Some(addr) = at {
                Slot::Mem(*addr)
            } else if let Some(off) = slot_offset(name, wbytes)
                .or_else(|| stated_local(overlay, entry, name))
                .or_else(|| debug_local(program, entry, name))
            {
                if mode == Mode::Iso && off < 0 {
                    let addr = objects.1;
                    objects.1 = objects.1.wrapping_add(ISO_STRIDE);
                    Slot::Mem(addr)
                } else {
                    let addr = entry_sp.wrapping_add_signed(off);
                    frame_low = frame_low.min(addr);
                    Slot::Mem(addr)
                }
            } else if *ty == CTy::of(Base::Wide) {
                let addr = wide_base.wrapping_add(from_usize(wide.len()).wrapping_mul(WIDE_BYTES));
                wide.push(addr);
                Slot::Mem(addr)
            } else {
                cells.push((name.clone(), named_register(name), *ty));
                Slot::Var(cells.len() - 1)
            };
            vars.insert(name.clone(), Variable { ty: *ty, slot });
        }
        let values = |n: &str| vars.contains_key(n) || is_param_name(n);
        let enumerators: FxHashMap<String, u64> = super::listed_enum(text)
            .map(|e| e.members.into_iter().map(|(k, n)| (n, k)).collect())
            .unwrap_or_default();
        let body: Vec<String> = all
            .get(base..)
            .unwrap_or(&[])
            .iter()
            .map(|l| {
                if l.trim_start().starts_with("/* asm") {
                    "__asm;".to_owned()
                } else {
                    blank(l)
                }
            })
            .collect();
        let stmts = statements(&body, base).map_err(str::to_owned)?;
        let toks: Vec<Result<Vec<Tok>, String>> = all
            .iter()
            .enumerate()
            .map(|(k, l)| {
                if k >= base && l.trim_start().starts_with("/* asm") {
                    tokens("__asm;")
                } else {
                    tokens(l)
                }
            })
            .collect();
        let mut c = Compiler {
            toks,
            values: &values,
            enumerators: &enumerators,
            word,
            ops: Vec::new(),
            labels: Vec::new(),
            blocks: FxHashMap::default(),
        };
        c.run(&stmts, None, None);
        c.emit(all.len(), Step::Return(None));
        let unplaced = c.ops.len();
        c.emit(
            all.len(),
            Step::Unreadable("a goto to a label the text lacks".to_owned()),
        );
        let Compiler { ops, labels, .. } = c;
        let targets = labels
            .iter()
            .map(|l| l.unwrap_or(unplaced))
            .collect::<Vec<_>>();
        let mut read: Vec<&str> = Vec::new();
        let mut strings: Vec<&[u8]> = Vec::new();
        for op in &ops {
            let e = match &op.step {
                Step::Eval(e)
                | Step::Test(e, _)
                | Step::Switch(e, _, _)
                | Step::Return(Some(e)) => e,
                Step::Return(None)
                | Step::Jump(_)
                | Step::Halt
                | Step::Leave
                | Step::Unreadable(_) => continue,
            };
            names_in(e, &mut read);
            strings_in(e, &mut strings);
        }
        let wanted: std::collections::BTreeSet<&str> = read
            .into_iter()
            .filter(|n| !vars.contains_key(*n) && !enumerators.contains_key(*n))
            .collect();
        let known = resolve_names(program, analysis, overlay, entry, &wanted);
        let literals = strings
            .into_iter()
            .map(|s| (s.to_vec(), literal_address(program, analysis, s)))
            .collect();
        let callees = known
            .values()
            .filter_map(|k| match k {
                Known::Code(at) => Some((*at, passing(program, analysis, overlay, *at))),
                Known::Address(_) | Known::Slot(_) => None,
            })
            .collect();
        let call_sp = (frame_low.wrapping_sub(CALL_GAP) & !0xf).wrapping_sub(wbytes);
        let teb = *analysis
            .derived
            .get_or_build("thread_block", (), || thread_block(program));
        let teb = teb.ok_or("the thread block does not read")?;
        let inputs = cells
            .iter()
            .map(|(name, reg, _)| {
                *reg == Some(Register::RSP) || sig.params.iter().any(|(p, _)| p == name)
            })
            .collect();
        Ok(Self {
            program,
            analysis,
            word,
            ops,
            targets,
            vars,
            arrays: head.arrays,
            cells,
            layouts: head.layouts,
            known,
            enumerators,
            literals,
            sig,
            passing: pass,
            callees,
            entry_sp,
            frame_low,
            teb,
            wide,
            call_sp,
            mode,
            inputs,
            objects,
        })
    }

    /// Runs the text on one input.
    ///
    /// # Arguments
    ///
    /// * `args` - The argument values, in order.
    /// * `pokes` - Memory to set up first, as `(address, bytes)`.
    /// * `budget` - Most statements, callee steps included.
    ///
    /// # Returns
    ///
    /// How the run ended and what it left; `None` when the architecture is
    /// not emulated.
    pub(crate) fn run(
        &self,
        args: &[u64],
        pokes: &[(u64, Vec<u8>)],
        budget: usize,
    ) -> Option<TextRun<'p>> {
        let mut emu = Emulator::with_imports(self.program, self.analysis, budget)?;
        for (at, bytes) in pokes {
            for (k, b) in bytes.iter().enumerate() {
                emu.poke(at.wrapping_add(from_usize(k)), *b);
            }
        }
        self.passing.place(&mut emu, self.entry_sp, args);
        for at in &self.wide {
            for k in 0..WIDE_BYTES {
                emu.poke(at.wrapping_add(k), 0);
            }
        }
        let entry_value = |r: Option<Register>| -> u64 {
            let Some(r) = r else { return 0 };
            if r == Register::RSP {
                return self.entry_sp;
            }
            self.passing
                .regs
                .iter()
                .position(|p| p.full_register() == r)
                .and_then(|i| args.get(i))
                .copied()
                .unwrap_or(0)
        };
        let mut vals = Vec::with_capacity(self.cells.len());
        for (_, reg, ty) in &self.cells {
            let bits = ty.bits(self.word).unwrap_or(64);
            let v = entry_value(*reg);
            vals.push(if ty.signed() {
                sext(v, bits) & mask(bits)
            } else {
                v & mask(bits)
            });
        }
        for (i, (name, ty)) in self.sig.params.iter().enumerate() {
            if let Some(Variable {
                slot: Slot::Var(k), ..
            }) = self.vars.get(name)
                && let (Some(v), Some(slot)) = (args.get(i), vals.get_mut(*k))
            {
                *slot = *v & mask(ty.bits(self.word).unwrap_or(64));
            }
        }
        let mut run = Running {
            s: self,
            emu,
            vals,
            set_at: vec![0; self.cells.len()],
            writers: BTreeMap::new(),
            fuel: budget,
            second_result: false,
            ret_lane: None,
            called: false,
            call_memo: None,
            steps: 0,
            line: 0,
            args: args.to_vec(),
            handed: None,
            alloca: if self.program.is_64 {
                ALLOCA_BASE_64
            } else {
                ALLOCA_BASE_32
            },
        };
        let (end, sources) = run.go();
        Some(TextRun {
            end,
            line: run.line,
            steps: run.steps,
            emu: run.emu,
            writers: run.writers,
            sources,
            entry_sp: self.entry_sp,
            literals: self.literals.values().flatten().copied().collect(),
            ret_lane: run.ret_lane,
        })
    }

    /// Solves for one parameter the first constraint the compiled body
    /// tests, by inverting the chain it computes.
    ///
    /// The check shapes a key validator and a crackme take - `f(a1) ==
    /// 0x1337`, a `switch (f(a1))` - hold the answer in the arithmetic
    /// between the parameter and the constant: every step of a bijective
    /// chain (`+`, `-`, `^`, a complement, a negation, a multiplication
    /// by an odd constant, a truncating cast or a left shift that keeps
    /// its bits) has an inverse, so walking the chain from the constant
    /// back to the bare parameter states the input that satisfies it. The
    /// candidate is then run: only one the run answers differently from a
    /// zero argument is reported, so a misread chain says nothing rather
    /// than something wrong. A chain step without an inverse - an `&`, an
    /// `|`, a shift right, a multiplication by an even constant, another
    /// variable - ends the search.
    ///
    /// # Arguments
    ///
    /// * `slot` - The parameter's position from zero.
    ///
    /// # Returns
    ///
    /// The candidate that satisfies the constraint, the 1-based line the
    /// constraint's comparison sits on, and what the run of it and of a
    /// zero argument each answered; `None` when no comparison names the
    /// parameter, its chain does not invert, or the candidate answers the
    /// same as zero.
    pub(crate) fn solve_for(&self, slot: usize) -> Option<(u64, usize, String, String)> {
        /// Whether an expression names the parameter.
        fn mentions(e: &Ast, param: &str) -> bool {
            match e {
                Ast::Name(n) => n == param,
                Ast::Int(..) | Ast::Float(..) | Ast::Str(_) => false,
                Ast::Un(_, a) | Ast::Cast(_, a) => mentions(a, param),
                Ast::Bin(_, a, b) | Ast::Logic(_, a, b) => mentions(a, param) || mentions(b, param),
                Ast::Pick(a, b, c) => {
                    mentions(a, param)
                        || b.as_ref().is_some_and(|b| mentions(b, param))
                        || mentions(c, param)
                }
                _ => false,
            }
        }
        /// Inverts a chain expression, from the value it must take back
        /// to the parameter's value.
        fn invert(e: &Ast, want: u64, param: &str, word: u8, depth: u8) -> Option<u64> {
            let m = mask(word);
            if depth == 0 {
                return None;
            }
            match e {
                Ast::Name(n) if n == param => Some(want & m),
                Ast::Un(Un::Neg, a) => invert(a, want.wrapping_neg() & m, param, word, depth - 1),
                Ast::Un(Un::Plus, a) => invert(a, want, param, word, depth - 1),
                Ast::Un(Un::Not, a) => invert(a, want ^ m, param, word, depth - 1),
                Ast::Cast(ty, a) => {
                    let bits = ty.bits(word).unwrap_or(word);
                    if ty.float().is_some() || bits > word {
                        return None;
                    }
                    invert(a, want & mask(bits), param, word, depth - 1)
                }
                Ast::Bin(op, a, b) => {
                    let (a, b) = (a.as_ref(), b.as_ref());
                    let k = |e: &Ast| match e {
                        Ast::Int(v, _) => Some(*v & m),
                        _ => None,
                    };
                    match op {
                        Bin::Add => k(b)
                            .and_then(|k| invert(a, want.wrapping_sub(k), param, word, depth - 1))
                            .or_else(|| {
                                k(a).and_then(|k| {
                                    invert(b, want.wrapping_sub(k), param, word, depth - 1)
                                })
                            }),
                        Bin::Sub => k(b)
                            .and_then(|k| invert(a, want.wrapping_add(k), param, word, depth - 1))
                            .or_else(|| {
                                k(a).and_then(|k| {
                                    invert(b, k.wrapping_sub(want), param, word, depth - 1)
                                })
                            }),
                        Bin::Xor => k(b)
                            .and_then(|k| invert(a, want ^ k, param, word, depth - 1))
                            .or_else(|| {
                                k(a).and_then(|k| invert(b, want ^ k, param, word, depth - 1))
                            }),
                        Bin::Mul => {
                            let odd = |e: &Ast| k(e).filter(|c| c & 1 == 1);
                            let inv = |c: u64| {
                                let mut x = 1u64;
                                for _ in 0..6 {
                                    x = x.wrapping_mul(2u64.wrapping_sub(c.wrapping_mul(x)));
                                }
                                x
                            };
                            odd(b)
                                .map(inv)
                                .and_then(|i| {
                                    invert(a, want.wrapping_mul(i) & m, param, word, depth - 1)
                                })
                                .or_else(|| {
                                    odd(a).map(inv).and_then(|i| {
                                        invert(b, want.wrapping_mul(i) & m, param, word, depth - 1)
                                    })
                                })
                        }
                        Bin::Shl => k(b).and_then(|s| {
                            let s = s & 63;
                            (want & mask(u8::try_from(s).unwrap_or(64)) == 0)
                                .then(|| invert(a, want >> s, param, word, depth - 1))
                                .flatten()
                        }),
                        Bin::And => {
                            let width =
                                |k: u64| (k & m).checked_add(1).filter(|p| p.is_power_of_two());
                            k(b).and_then(width)
                                .and_then(|p| u8::try_from(p.ilog2()).ok())
                                .and_then(|bits| {
                                    invert(a, want & mask(bits), param, word, depth - 1)
                                })
                        }
                        _ => None,
                    }
                }
                _ => None,
            }
        }
        /// The equality targets inside an expression: each `chain ==
        /// constant` or `chain != constant` whose chain names the
        /// parameter, and each constant of a switch on such a chain.
        fn targets<'e>(e: &'e Ast, param: &str, out: &mut Vec<(u64, &'e Ast)>, depth: u8) {
            if depth == 0 || out.len() >= 8 {
                return;
            }
            match e {
                Ast::Bin(Bin::Eq | Bin::Ne, a, b) => {
                    let k = |x: &Ast| match x {
                        Ast::Int(v, _) => Some(*v),
                        _ => None,
                    };
                    for (chain, want) in [(a.as_ref(), k(b.as_ref())), (b.as_ref(), k(a.as_ref()))]
                    {
                        if let Some(want) = want
                            && mentions(chain, param)
                        {
                            out.push((want, chain));
                        }
                    }
                }
                Ast::Un(_, a) | Ast::Cast(_, a) => targets(a, param, out, depth - 1),
                Ast::Bin(_, a, b) | Ast::Logic(_, a, b) => {
                    targets(a, param, out, depth - 1);
                    targets(b, param, out, depth - 1);
                }
                Ast::Pick(a, b, c) => {
                    targets(a, param, out, depth - 1);
                    if let Some(b) = b {
                        targets(b, param, out, depth - 1);
                    }
                    targets(c, param, out, depth - 1);
                }
                _ => {}
            }
        }
        let word = self.word;
        let param = self.sig.params.get(slot)?.0.as_str();
        let mut found: Vec<(u64, &Ast)> = Vec::new();
        let mut line = 0;
        for op in &self.ops {
            let read = match &op.step {
                Step::Test(c, _) | Step::Eval(c) => Some(c),
                Step::Switch(v, ..) => Some(v),
                Step::Return(Some(v)) => Some(v),
                _ => None,
            };
            if let Some(read) = read
                && mentions(read, param)
            {
                targets(read, param, &mut found, 8);
                if let Step::Switch(_, cases, _) = &op.step {
                    found.extend(cases.iter().take(8).map(|(k, _)| (*k, read)));
                }
                if !found.is_empty() {
                    line = op.line;
                    break;
                }
            }
        }
        let depth = 24;
        let candidate = found
            .iter()
            .find_map(|&(want, chain)| invert(chain, want, param, word, depth))?;
        let args_of = |v: u64| {
            (0..self.sig.params.len())
                .map(|i| if i == slot { v } else { 0 })
                .collect::<Vec<u64>>()
        };
        let zero = self.run(&args_of(0), &[], SOLVE_BUDGET)?;
        let solved = self.run(&args_of(candidate), &[], SOLVE_BUDGET)?;
        let say = |r: &TextRun<'_>| match r.end {
            End::Returned(v) => format!(
                "returns {}",
                v.map_or_else(|| "void".to_owned(), |v| format!("{v:#x}"))
            ),
            ref other => format!("{other:?}"),
        };
        (solved.end != zero.end).then(|| (candidate, line, say(&zero), say(&solved)))
    }

    /// The reads of a variable that no line of the text sets before them
    /// on any path: each line and the names it reads so.
    ///
    /// The text's closure: every value it reads must come from a line of
    /// it or be an input, a parameter or a global. A register variable
    /// that no line sets holds only what its register held at entry, so a
    /// read of one that is no parameter shows a value the text lost: whoami
    /// read `a1 - r10 + 1` where the `mov r10d,eax` setting it was dropped.
    /// A forward pass over the compiled body keeps the variables some path
    /// sets; a read outside that set is flagged. Taking a variable's
    /// address sets it (a callee may write it), and a line this reader does
    /// not read sets them all, so a flag is never a guess. Only variables
    /// held as C values are read so (register names, temporaries), never a
    /// stack slot or a global, which live in memory others may write; a
    /// register the text names without declaring it is one too.
    ///
    /// # Returns
    ///
    /// The 1-based lines in order, each with the names it reads unset, in
    /// the order read.
    pub(crate) fn unset_reads(&self) -> Vec<(usize, Vec<String>)> {
        let mut named: Vec<&str> = Vec::new();
        for op in &self.ops {
            match &op.step {
                Step::Eval(e)
                | Step::Test(e, _)
                | Step::Switch(e, _, _)
                | Step::Return(Some(e)) => {
                    names_in(e, &mut named);
                }
                Step::Jump(_)
                | Step::Return(None)
                | Step::Unreadable(_)
                | Step::Halt
                | Step::Leave => {}
            }
        }
        let mut undeclared: Vec<String> = named
            .into_iter()
            .filter(|n| {
                !self.vars.contains_key(*n) && named_register(n).is_some_and(|r| r != Register::RSP)
            })
            .map(str::to_owned)
            .collect();
        undeclared.sort_unstable();
        undeclared.dedup();
        let undeclared = undeclared.as_slice();
        let cells = self.cells.len() + undeclared.len();
        let mut given: Vec<bool> = self
            .cells
            .iter()
            .map(|(name, reg, _)| {
                *reg == Some(Register::RSP) || self.sig.params.iter().any(|(p, _)| p == name)
            })
            .collect();
        given.resize(cells, false);
        let target = |l: &usize| self.targets.get(*l).copied().unwrap_or(usize::MAX);
        let mut ins: Vec<Option<Vec<bool>>> = vec![None; self.ops.len()];
        let Some(first) = ins.first_mut() else {
            return Vec::new();
        };
        *first = Some(given);
        let mut todo: Vec<usize> = vec![0];
        let mut flags: BTreeMap<usize, Vec<String>> = BTreeMap::new();
        let mut rounds = 0usize;
        while let Some(pc) = todo.pop() {
            rounds += 1;
            if rounds > UNSET_ROUNDS {
                return Vec::new();
            }
            let (Some(op), Some(Some(state))) = (self.ops.get(pc), ins.get(pc)) else {
                continue;
            };
            let mut set = state.clone();
            let next: Vec<usize> = match &op.step {
                Step::Eval(e) => {
                    self.reads(e, undeclared, &mut set, &mut |_| {});
                    vec![pc + 1]
                }
                Step::Test(c, l) => {
                    self.reads(c, undeclared, &mut set, &mut |_| {});
                    vec![pc + 1, target(l)]
                }
                Step::Jump(l) => vec![target(l)],
                Step::Switch(v, cases, default) => {
                    self.reads(v, undeclared, &mut set, &mut |_| {});
                    cases
                        .iter()
                        .map(|(_, l)| target(l))
                        .chain([target(default)])
                        .collect()
                }
                Step::Return(e) => {
                    if let Some(e) = e {
                        self.reads(e, undeclared, &mut set, &mut |_| {});
                    }
                    Vec::new()
                }
                Step::Unreadable(_) => {
                    set = vec![true; cells];
                    vec![pc + 1]
                }
                Step::Halt | Step::Leave => Vec::new(),
            };
            for n in next {
                let Some(slot) = ins.get_mut(n) else { continue };
                let grew = match slot {
                    None => {
                        *slot = Some(set.clone());
                        true
                    }
                    Some(old) => {
                        let mut grew = false;
                        for (o, s) in old.iter_mut().zip(&set) {
                            if *s && !*o {
                                *o = true;
                                grew = true;
                            }
                        }
                        grew
                    }
                };
                if grew {
                    todo.push(n);
                }
            }
        }
        for (op, state) in self.ops.iter().zip(&ins) {
            let Some(state) = state else { continue };
            let mut set = state.clone();
            let mut found: Vec<String> = Vec::new();
            let mut note = |n: &str| {
                if !found.iter().any(|f| f == n) {
                    found.push(n.to_owned());
                }
            };
            match &op.step {
                Step::Eval(e)
                | Step::Test(e, _)
                | Step::Switch(e, _, _)
                | Step::Return(Some(e)) => {
                    self.reads(e, undeclared, &mut set, &mut note);
                }
                Step::Jump(_)
                | Step::Return(None)
                | Step::Unreadable(_)
                | Step::Halt
                | Step::Leave => {}
            }
            if !found.is_empty() {
                let at = flags.entry(op.line).or_default();
                for n in found {
                    if !at.contains(&n) {
                        at.push(n);
                    }
                }
            }
        }
        flags.into_iter().collect()
    }

    /// Walks an expression in evaluation order: notes each C variable it
    /// reads that `set` does not hold, and adds each it sets.
    ///
    /// # Arguments
    ///
    /// * `e` - The expression.
    /// * `undeclared` - The register names the text reads without declaring
    ///   them, sorted: each is a cell past the declared ones.
    /// * `set` - The variables some path has set, by cell; updated.
    /// * `note` - Called with each name read unset.
    fn reads(&self, e: &Ast, undeclared: &[String], set: &mut [bool], note: &mut dyn FnMut(&str)) {
        let cell = |n: &str| match self.vars.get(n) {
            Some(Variable {
                slot: Slot::Var(k), ..
            }) => Some(*k),
            Some(_) => None,
            None => undeclared
                .binary_search_by(|u| u.as_str().cmp(n))
                .ok()
                .map(|k| self.cells.len() + k),
        };
        let define = |set: &mut [bool], k: usize| {
            if let Some(s) = set.get_mut(k) {
                *s = true;
            }
        };
        match e {
            Ast::Name(n) => {
                if let Some(k) = cell(n)
                    && set.get(k) == Some(&false)
                {
                    note(n);
                }
            }
            Ast::Int(..) | Ast::Float(..) | Ast::Str(_) => {}
            Ast::Un(Un::Addr, a) => match a.as_ref() {
                Ast::Name(n) if cell(n).is_some() => {
                    if let Some(k) = cell(n) {
                        define(set, k);
                    }
                }
                other => self.reads(other, undeclared, set, note),
            },
            Ast::Un(_, a) | Ast::Cast(_, a) | Ast::Arrow(a, _) => {
                self.reads(a, undeclared, set, note);
            }
            Ast::Bin(_, a, b) | Ast::Index(a, b) | Ast::Logic(_, a, b) => {
                self.reads(a, undeclared, set, note);
                self.reads(b, undeclared, set, note);
            }
            Ast::Pick(c, m, o) => {
                self.reads(c, undeclared, set, note);
                let mut other = set.to_vec();
                if let Some(m) = m {
                    self.reads(m, undeclared, set, note);
                }
                self.reads(o, undeclared, &mut other, note);
                for (s, o) in set.iter_mut().zip(other) {
                    *s |= o;
                }
            }
            Ast::Call(f, args) => {
                self.reads(f, undeclared, set, note);
                for a in args {
                    self.reads(a, undeclared, set, note);
                }
            }
            Ast::Assign(op, lhs, rhs) => {
                let target = match lhs.as_ref() {
                    Ast::Name(n) => cell(n),
                    _ => None,
                };
                if op.is_some() || target.is_none() {
                    self.reads(lhs, undeclared, set, note);
                }
                self.reads(rhs, undeclared, set, note);
                if let Some(k) = target {
                    define(set, k);
                }
            }
            Ast::Step(_, _, a) => {
                self.reads(a, undeclared, set, note);
                if let Ast::Name(n) = a.as_ref()
                    && let Some(k) = cell(n)
                {
                    define(set, k);
                }
            }
        }
    }
}

/// The address of the thread block a machine over the program plants,
/// read the way code reads it: through the segment its self pointer is in.
///
/// # Arguments
///
/// * `program` - The loaded image.
fn thread_block(program: &Program) -> Option<u64> {
    let mut emu = Emulator::new(program, 2)?;
    let (at, code): (u64, &[u8]) = if program.is_64 {
        (
            SENTINEL_64 - 0x1000,
            &[
                0x65, 0x48, 0x8b, 0x04, 0x25, 0x30, 0x00, 0x00,
                0x00, // ASM: mov rax,gs:[0x30]
                0xc3, // ASM: ret
            ],
        )
    } else {
        (
            SENTINEL_32 - 0x1000,
            &[
                0x64, 0xa1, 0x18, 0x00, 0x00, 0x00, // ASM: mov eax,fs:[0x18]
                0xc3, // ASM: ret
            ],
        )
    };
    for (k, b) in code.iter().enumerate() {
        emu.poke(at.wrapping_add(from_usize(k)), *b);
    }
    matches!(emu.run(at).stop, Stop::Returned).then(|| emu.register("rax"))?
}

/// Every name a text may give something of the binary, with everything it
/// is.
///
/// The image base, the functions (in address order, where several share a
/// name), the vtables, the known tables and the symbols, in that order of
/// precedence; an import's slot also answers to its linker name
/// `__imp_name`, which a wrapper of the same name calls it by.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Its functions.
/// * `overlay` - User names.
fn names(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
) -> FxHashMap<String, Vec<Known>> {
    let mut out: FxHashMap<String, Vec<Known>> = FxHashMap::default();
    out.insert(
        "__ImageBase".to_owned(),
        vec![Known::Address(program.image_base)],
    );
    for f in &analysis.functions {
        let full = name_of(analysis, overlay, f.entry);
        out.entry(bare_name(&full).to_owned())
            .or_default()
            .push(Known::Code(f.entry));
    }
    for (at, class) in &analysis.classes.vtables {
        out.entry(format!("{class}::vftable"))
            .or_default()
            .push(Known::Address(*at));
    }
    for (at, n) in &analysis.crypto {
        out.entry(crate::crypto::identifier(n))
            .or_default()
            .push(Known::Address(*at));
    }
    for s in program.symbols.iter().filter(|s| s.addr != 0) {
        let n = crate::search::demangled_name(&s.name);
        if s.kind == SymbolKind::Import {
            for name in [bare_name(&n).to_owned(), format!("__imp_{}", bare_name(&n))] {
                out.entry(name).or_default().push(Known::Slot(s.addr));
            }
        } else {
            out.entry(n).or_default().push(Known::Address(s.addr));
        }
    }
    out
}

/// Resolves the names the text uses that it does not declare, through the
/// table of [`names`] built once per set of names in force.
///
/// The table reads the names alone, so it is keyed without the passes and
/// choice points ([`Overlay::names_key`]): the texts a repair search builds
/// under other passes and choices share it, where each of them built the
/// whole table again.
///
/// Where several things share a name (overloads of one C++ name), the one
/// the function refers to is meant, else the first. A name the text also
/// gives an instruction (`memcpy` for a `rep movs`) is the function or the
/// import only where the function refers to it; elsewhere it is the
/// instruction, and left out to run as the builtin.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Its functions.
/// * `overlay` - User names.
/// * `entry` - The function whose text it is.
/// * `wanted` - The names.
///
/// # Returns
///
/// Each name that is a function, a known table or a symbol, with what it
/// is; a name left out is a parameter by position or an intrinsic.
fn resolve_names(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    entry: u64,
    wanted: &std::collections::BTreeSet<&str>,
) -> FxHashMap<String, Known> {
    if wanted.is_empty() {
        return FxHashMap::default();
    }
    let table = analysis
        .derived
        .get_or_build_named("text_names", overlay.names_key(), (), || {
            names(program, analysis, overlay)
        });
    let referred = |k: &Known| {
        let (Known::Code(at) | Known::Address(at) | Known::Slot(at)) = *k;
        analysis
            .xrefs_to(at)
            .iter()
            .any(|r| r.from_entry == Some(entry))
    };
    wanted
        .iter()
        .filter_map(|n| {
            let all = table.get(*n)?;
            let mine = all.iter().copied().find(|k| referred(k));
            let known = if INTRINSICS.contains(n) {
                mine?
            } else {
                mine.or_else(|| all.first().copied())?
            };
            Some(((*n).to_owned(), known))
        })
        .collect()
}

/// Tells whether an expression is the call `NtCurrentTeb()`, whose fields
/// the text names.
///
/// # Arguments
///
/// * `e` - The expression.
fn is_teb(e: &Ast) -> bool {
    matches!(e, Ast::Call(f, args) if args.is_empty() && matches!(&**f, Ast::Name(n) if n == "NtCurrentTeb"))
}

/// An lvalue: where an assignment writes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Place {
    /// A C variable, by index, and its type.
    Var(usize, CTy),
    /// Memory at an address, of a type.
    Mem(u64, CTy),
}

/// One run of a script in progress.
struct Running<'s, 'p> {
    /// The script.
    s: &'s Script<'p>,
    /// The machine whose memory the text reads and writes, and its callees
    /// run on.
    emu: Emulator<'p>,
    /// Each C variable's value.
    vals: Vec<u64>,
    /// The line that last set each C variable, zero for none.
    set_at: Vec<usize>,
    /// The line that last wrote each byte.
    writers: BTreeMap<u64, usize>,
    /// Steps left.
    fuel: usize,
    /// Steps taken.
    steps: usize,
    /// The 1-based line being run.
    line: usize,
    /// The argument values, for a parameter the signature does not list.
    args: Vec<u64>,
    /// The lowest address of the text's frame a call that reached an
    /// import was handed: the emulator answers an import without filling
    /// what it points at, so a read there that nothing set is no answer.
    handed: Option<u64>,
    /// The call being evaluated wants the callee's second result, the one
    /// in `rdx`: set while a `__rdx`-suffixed call name is unwound to the
    /// function it names.
    second_result: bool,
    /// The width the returned value was held at before its conversion to
    /// the declared return type, when that is a byte or a word.
    ret_lane: Option<u8>,
    /// Whether any callee has run on the machine, so the emulator's rax and
    /// rdx hold a call's leftovers rather than the entry's own state.
    called: bool,
    /// The last call a statement ran: its target, its argument values, and
    /// what it left in `rax` and `rdx`. A `__rdx` call of the same target
    /// and arguments is that call's second half, answered from here without
    /// running the callee again, whose side effects the machine would then
    /// see twice.
    call_memo: Option<(u64, Vec<u64>, u64, u64)>,
    /// Where the next `alloca` block starts.
    alloca: u64,
}

/// The result of evaluating one piece of the text.
type Eval<T> = Result<T, End>;

/// A refusal to run something this reader does not model.
///
/// # Arguments
///
/// * `why` - What it is.
///
/// # Errors
///
/// Always: [`End::Unchecked`] with the reason.
fn unchecked<T>(why: impl Into<String>) -> Eval<T> {
    Err(End::Unchecked(why.into()))
}

impl Running<'_, '_> {
    /// Runs the body from its first step.
    ///
    /// # Returns
    ///
    /// How it ended, and for a return each variable its value read with
    /// the line that last set it.
    fn go(&mut self) -> (End, Vec<(String, usize)>) {
        let s = self.s;
        let target = |l: &usize| s.targets.get(*l).copied().unwrap_or(usize::MAX);
        let mut pc = 0usize;
        loop {
            let Some(op) = s.ops.get(pc) else {
                return (End::Returned(None), Vec::new());
            };
            self.line = op.line;
            if self.fuel == 0 {
                return (End::Budget, Vec::new());
            }
            self.fuel -= 1;
            self.steps += 1;
            pc += 1;
            let outcome: Eval<Option<usize>> = match &op.step {
                Step::Eval(e) => self.value(e).map(|_| None),
                Step::Test(c, l) => self.truth(c).map(|t| (!t).then(|| target(l))),
                Step::Jump(l) => Ok(Some(target(l))),
                Step::Switch(v, cases, default) => self.value(v).map(|v| {
                    let key = sext(v.bits, v.ty.bits(self.s.word).unwrap_or(64));
                    let hit = cases
                        .iter()
                        .find(|(c, _)| *c == key || *c == v.bits)
                        .map_or(default, |(_, l)| l);
                    Some(target(hit))
                }),
                Step::Return(e) => {
                    let mut sources = Vec::new();
                    let end = match e {
                        None => Ok(End::Returned(None)),
                        Some(e) => {
                            let mut names = Vec::new();
                            names_in(e, &mut names);
                            for n in names {
                                if sources.iter().any(|(m, _)| m == n) {
                                    continue;
                                }
                                if let Some(at) = self.last_set(n) {
                                    sources.push((n.to_owned(), at));
                                } else if self.never_set(n) {
                                    sources.push((n.to_owned(), 0));
                                }
                            }
                            self.value(e).and_then(|v| match s.sig.ret {
                                None => Ok(End::Returned(None)),
                                Some(ty) => {
                                    if v.ty.bits(self.s.word).is_some_and(|b| {
                                        b <= 16 && b < ty.bits(self.s.word).unwrap_or(64)
                                    }) {
                                        self.ret_lane = v.ty.bits(self.s.word);
                                    }
                                    let r = self.convert(v, ty)?;
                                    Ok(End::Returned(Some(r.bits)))
                                }
                            })
                        }
                    };
                    return match end {
                        Ok(end) => (end, sources),
                        Err(end) => (end, Vec::new()),
                    };
                }
                Step::Halt => return (End::Trap, Vec::new()),
                Step::Leave => {
                    return (
                        End::Unchecked(
                            "the text jumps out of the function, to code it does not show"
                                .to_owned(),
                        ),
                        Vec::new(),
                    );
                }
                Step::Unreadable(why) => Err(End::Unchecked(format!("cannot read it: {why}"))),
            };
            match outcome {
                Ok(Some(next)) => pc = next,
                Ok(None) => {}
                Err(end) => return (end, Vec::new()),
            }
        }
    }

    /// The line that last set a variable, zero-free: `None` when nothing
    /// in the text set it.
    ///
    /// # Arguments
    ///
    /// * `name` - The variable.
    fn last_set(&self, name: &str) -> Option<usize> {
        let v = self.s.vars.get(name)?;
        match v.slot {
            Slot::Var(k) => self.set_at.get(k).copied().filter(|l| *l > 0),
            Slot::Mem(at) => self.writers.get(&at).copied(),
        }
    }

    /// Tells whether a name is a variable of the text, no parameter, that
    /// no line has set: it holds only what its register held at entry.
    ///
    /// # Arguments
    ///
    /// * `name` - The name.
    fn never_set(&self, name: &str) -> bool {
        matches!(self.s.vars.get(name), Some(Variable { slot: Slot::Var(k), .. })
            if self.set_at.get(*k) == Some(&0))
            && !self.s.sig.params.iter().any(|(p, _)| p == name)
    }

    /// The machine word in bits.
    fn word(&self) -> u8 {
        self.s.word
    }

    /// An integer value of a type, its bits masked to the type's width.
    ///
    /// # Arguments
    ///
    /// * `bits` - The value.
    /// * `ty` - Its type.
    fn int(&self, bits: u64, ty: CTy) -> Val {
        Val {
            bits: bits & mask(ty.bits(self.word()).unwrap_or(64)),
            ty,
        }
    }

    /// Converts a value to a type, as C's assignment and cast convert.
    ///
    /// An integer converted to a float is its low bits when unsigned, and
    /// sign-extended first when signed. Anything other than a single is
    /// held as a double.
    ///
    /// # Arguments
    ///
    /// * `v` - The value.
    /// * `to` - The type.
    ///
    /// # Errors
    ///
    /// Unchecked for a vector type, which nothing here computes with.
    fn convert(&self, v: Val, to: CTy) -> Eval<Val> {
        if to.ptr == 0 && to.base == Base::Void {
            return Ok(Val { bits: 0, ty: to });
        }
        let (Some(from_bits), Some(to_bits)) = (v.ty.bits(self.word()), to.bits(self.word()))
        else {
            return unchecked("a 128-bit vector value");
        };
        Ok(match (v.ty.float(), to.float()) {
            (Some(fb), Some(tb)) => Val {
                bits: float_bits(float_of(v.bits, fb), tb),
                ty: to,
            },
            (None, Some(tb)) => {
                let wide = if v.ty.signed() {
                    sext(v.bits, from_bits)
                } else {
                    v.bits & mask(from_bits)
                };
                let dest = if tb == 32 { Ty::F32 } else { Ty::F64 };
                Val {
                    bits: integer_to_float(wide, v.ty.signed(), dest),
                    ty: to,
                }
            }
            (Some(fb), None) => self.int(float_to_int(float_of(v.bits, fb), to_bits), to),
            (None, None) => {
                let wide = if v.ty.signed() {
                    sext(v.bits, from_bits)
                } else {
                    v.bits
                };
                self.int(wide, to)
            }
        })
    }

    /// A float cast of a bitwise operation, or `None` when `e` is not one.
    ///
    /// A cut of a float keeps the bits, zero above a single. Converting
    /// them would be the integer the bits happen to be, which is not the
    /// float a wider operation reads. A cut of two integers is that
    /// integer converted, and it is evaluated once.
    ///
    /// # Arguments
    ///
    /// * `to` - The type the cast names.
    /// * `e` - The cast's operand.
    ///
    /// # Errors
    ///
    /// Unchecked when an operand of the cut cannot be read.
    fn encoding_cast(&mut self, to: &CTy, e: &Ast) -> Eval<Option<Val>> {
        let Some(width) = to.float() else {
            return Ok(None);
        };
        let Ast::Bin(op @ (Bin::And | Bin::Or | Bin::Xor), l, r) = e else {
            return Ok(None);
        };
        let (x, y) = (self.value(l)?, self.value(r)?);
        if x.ty.float().is_none() && y.ty.float().is_none() {
            let combined = self.binary(*op, x, y)?;
            return Ok(Some(self.convert(combined, *to)?));
        }
        let bits = match op {
            Bin::And => x.bits & y.bits,
            Bin::Or => x.bits | y.bits,
            Bin::Xor => x.bits ^ y.bits,
            _ => return Ok(None),
        };
        let bits = if width == 32 { bits & mask(32) } else { bits };
        Ok(Some(Val { bits, ty: *to }))
    }

    /// The type C promotes an operand to: a narrower integer to `int`.
    ///
    /// # Arguments
    ///
    /// * `ty` - The operand's type.
    fn promote(&self, ty: CTy) -> CTy {
        if ty.ptr > 0 {
            return ty;
        }
        match ty.base {
            Base::Int(bits, _) if bits < 32 => CTy::int(32, true),
            Base::Opaque => CTy::int(self.word(), false),
            _ => ty,
        }
    }

    /// The type two arithmetic operands convert to: a float if either is,
    /// else C's usual arithmetic conversions on the promoted integers, a
    /// pointer counting as the unsigned word.
    ///
    /// # Arguments
    ///
    /// * `a` - One operand's type.
    /// * `b` - The other's.
    fn common(&self, a: CTy, b: CTy) -> CTy {
        let word = CTy::int(self.word(), false);
        let a = if a.is_ptr() { word } else { self.promote(a) };
        let b = if b.is_ptr() { word } else { self.promote(b) };
        match (a.float(), b.float()) {
            (Some(x), Some(y)) => return CTy::of(Base::Float(x.max(y))),
            (Some(_), None) => return a,
            (None, Some(_)) => return b,
            (None, None) => {}
        }
        let (Base::Int(ab, asg), Base::Int(bb, bsg)) = (a.base, b.base) else {
            return word;
        };
        if asg == bsg {
            return CTy::int(ab.max(bb), asg);
        }
        let ((ub, _), (sb, _)) = if asg {
            ((bb, bsg), (ab, asg))
        } else {
            ((ab, asg), (bb, bsg))
        };
        if ub >= sb {
            CTy::int(ub, false)
        } else {
            CTy::int(sb, true)
        }
    }

    /// The type C gives an expression, read off the text without running
    /// it: what a conditional's arms convert to before one is picked.
    ///
    /// # Arguments
    ///
    /// * `e` - The expression.
    ///
    /// # Returns
    ///
    /// The type, or `None` when the text does not say (a field no layout
    /// line sizes, a dereference of no pointer).
    fn type_of(&self, e: &Ast) -> Option<CTy> {
        let word = CTy::int(self.word(), false);
        Some(match e {
            Ast::Int(_, ty) | Ast::Float(_, ty) | Ast::Cast(ty, _) => *ty,
            Ast::Str(_) => CTy::int(8, true).to(),
            Ast::Name(n) => match self.s.vars.get(n) {
                Some(v) => v.ty,
                None => global_name(n).map_or(word, |(_, ty)| ty),
            },
            Ast::Un(Un::Deref, a) | Ast::Index(a, _) => self.type_of(a)?.pointee()?,
            Ast::Un(Un::Addr, a) => self.type_of(a)?.to(),
            Ast::Un(Un::LogNot, _) | Ast::Logic(..) => CTy::int(32, true),
            Ast::Un(Un::Neg | Un::Not | Un::Plus, a) => {
                let ty = self.type_of(a)?;
                if ty.float().is_some() {
                    ty
                } else {
                    self.promote(ty)
                }
            }
            Ast::Bin(op, _, _) if op.compares() => CTy::int(32, true),
            Ast::Bin(Bin::Shl | Bin::Shr, a, _) => self.promote(self.type_of(a)?),
            Ast::Bin(op, a, b) => {
                let (x, y) = (self.type_of(a)?, self.type_of(b)?);
                match (x.is_ptr(), y.is_ptr(), op) {
                    (true, true, Bin::Sub) => CTy::int(self.word(), true),
                    (true, false, Bin::Add | Bin::Sub) => x,
                    (false, true, Bin::Add) => y,
                    _ => self.common(x, y),
                }
            }
            Ast::Pick(c, m, o) => {
                let x = self.type_of(m.as_deref().unwrap_or(c))?;
                let y = self.type_of(o)?;
                if x.is_ptr() {
                    x
                } else if y.is_ptr() {
                    y
                } else {
                    self.common(x, y)
                }
            }
            Ast::Call(..) => word,
            Ast::Arrow(a, field) => {
                let off = field
                    .strip_prefix("field_0x")
                    .and_then(|h| u64::from_str_radix(h, 16).ok())?;
                let Ast::Name(base) = &**a else { return None };
                *self.s.layouts.get(base)?.get(&off)?
            }
            Ast::Assign(_, t, _) | Ast::Step(_, _, t) => self.type_of(t)?,
        })
    }

    /// Tells whether a value is true, as a condition reads it.
    ///
    /// # Arguments
    ///
    /// * `e` - The condition.
    ///
    /// # Errors
    ///
    /// As [`Running::value`].
    fn truth(&mut self, e: &Ast) -> Eval<bool> {
        let v = self.value(e)?;
        Ok(match v.ty.float() {
            Some(fb) => float_of(v.bits, fb) != 0.0,
            None => v.bits != 0,
        })
    }

    /// A truth value as C gives it: an `int` of 0 or 1.
    ///
    /// # Arguments
    ///
    /// * `t` - The truth.
    fn boolean(t: bool) -> Val {
        Val {
            bits: u64::from(t),
            ty: CTy::int(32, true),
        }
    }

    /// Evaluates an expression for its value.
    ///
    /// # Arguments
    ///
    /// * `e` - The expression.
    ///
    /// # Errors
    ///
    /// Why the run stops here: a fault, a callee that did not return, the
    /// budget, or something this reader does not model.
    fn value(&mut self, e: &Ast) -> Eval<Val> {
        match e {
            Ast::Int(v, ty) => Ok(self.int(*v, *ty)),
            Ast::Float(v, ty) => Ok(Val {
                bits: float_bits(*v, ty.float().unwrap_or(64)),
                ty: *ty,
            }),
            Ast::Str(s) if s.iter().all(|b| *b == 0) => unchecked(
                "an empty string literal, which stands for an address the text does not give",
            ),
            Ast::Str(s) => match self.s.literals.get(s) {
                Some(Some(at)) => Ok(self.int(*at, CTy::int(8, true).to())),
                _ => unchecked("a string literal the image does not hold as written"),
            },
            Ast::Name(n) => self.name(n),
            Ast::Un(op, a) => self.unary(*op, a),
            Ast::Cast(ty, a) => {
                if let Some(v) = self.encoding_cast(ty, a)? {
                    return Ok(v);
                }
                let v = self.value(a)?;
                self.convert(v, *ty)
            }
            Ast::Bin(op @ (Bin::Eq | Bin::Ne), a, b) if pure(a) && pure(b) => {
                if let Some(x) = self.wide_place(a)? {
                    let right = match &**b {
                        Ast::Int(0, _) => vec![0; 16],
                        other => match self.wide_place(other)? {
                            Some(y) => self.wide_bytes(y)?,
                            None => return unchecked("a 128-bit value compared with a narrow one"),
                        },
                    };
                    let same = self.wide_bytes(x)? == right;
                    return Ok(Self::boolean(same == (*op == Bin::Eq)));
                }
                let (x, y) = (self.value(a)?, self.value(b)?);
                self.binary(*op, x, y)
            }
            Ast::Bin(op, a, b) => {
                let (x, y) = (self.value(a)?, self.value(b)?);
                self.binary(*op, x, y)
            }
            Ast::Logic(and, a, b) => {
                let left = self.truth(a)?;
                if left != *and {
                    return Ok(Self::boolean(left));
                }
                let right = self.truth(b)?;
                Ok(Self::boolean(right))
            }
            Ast::Pick(c, middle, other) => {
                let test = self.value(c)?;
                let truth = match test.ty.float() {
                    Some(fb) => float_of(test.bits, fb) != 0.0,
                    None => test.bits != 0,
                };
                let picked = match (truth, middle) {
                    (true, None) => test,
                    (true, Some(m)) => self.value(m)?,
                    (false, _) => self.value(other)?,
                };
                match self.type_of(e) {
                    Some(ty) if !ty.is_ptr() && !picked.ty.is_ptr() => self.convert(picked, ty),
                    _ => Ok(picked),
                }
            }
            Ast::Call(f, args) => self.call(f, args),
            Ast::Index(..) | Ast::Arrow(..) => {
                let p = self.place(e)?;
                self.read(p)
            }
            Ast::Assign(op, target, source) => self.assign(*op, target, source),
            Ast::Step(prefix, up, target) => {
                let p = self.place(target)?;
                let old = self.read(p)?;
                let one = Val {
                    bits: 1,
                    ty: CTy::int(32, true),
                };
                let new = self.binary(if *up { Bin::Add } else { Bin::Sub }, old, one)?;
                let written = self.write(p, new)?;
                Ok(if *prefix { written } else { old })
            }
        }
    }

    /// The value a name holds.
    ///
    /// # Arguments
    ///
    /// * `n` - The name.
    ///
    /// # Errors
    ///
    /// Unchecked for a name nothing resolves; a fault for a global nothing
    /// backs.
    fn name(&mut self, n: &str) -> Eval<Val> {
        if let Some(v) = self.s.vars.get(n).copied() {
            if self.s.arrays.contains(n)
                && let Slot::Mem(at) = v.slot
            {
                return Ok(self.int(at, v.ty.to()));
            }
            return self.read(Self::slot_place(v));
        }
        if let Some(&v) = self.s.enumerators.get(n) {
            return Ok(self.int(v, CTy::int(32, true)));
        }
        match self.s.known.get(n) {
            Some(Known::Code(at) | Known::Address(at)) => {
                return Ok(self.int(*at, CTy::of(Base::Void).to()));
            }
            Some(Known::Slot(at)) => {
                let ty = CTy::int(self.word(), false);
                return self.read(Place::Mem(*at, ty));
            }
            None => {}
        }
        if let Some((at, ty)) = global_name(n) {
            return self.read(Place::Mem(at, ty));
        }
        if let Some(i) = n
            .strip_prefix('a')
            .and_then(|d| d.parse::<usize>().ok())
            .and_then(|k| k.checked_sub(1))
        {
            return self.parameter(i);
        }
        match n {
            "NAN" => Ok(Val {
                bits: f64::NAN.to_bits(),
                ty: CTy::of(Base::Float(64)),
            }),
            "INFINITY" => Ok(Val {
                bits: f64::INFINITY.to_bits(),
                ty: CTy::of(Base::Float(64)),
            }),
            _ if named_register(n).is_some() || n.starts_with("xmm") || n.starts_with("st") => {
                let why = format!("`{n}` is read, and the text never declares or sets it");
                match self.s.mode {
                    Mode::Machine => unchecked(why),
                    Mode::Iso => Err(End::Refused(why)),
                }
            }
            "NULL" | "nullptr" => Ok(self.int(0, CTy::int(self.word(), false))),
            _ => match (
                crate::winconst::value(n),
                crate::analysis::typelib::value_of(n, self.s.program.format),
            ) {
                (Some(code), _) => Ok(self.int(u64::from(code), CTy::int(32, true))),
                (None, Some(v)) => Ok(self.int(v, CTy::int(self.word(), false))),
                (None, None) => unchecked(format!("`{n}` names nothing this can read")),
            },
        }
    }

    /// A parameter the signature does not list, by its position: the value
    /// the convention passes there.
    ///
    /// # Arguments
    ///
    /// * `i` - Its position from zero.
    ///
    /// # Errors
    ///
    /// A fault when its stack slot is unbacked.
    fn parameter(&mut self, i: usize) -> Eval<Val> {
        if self.s.mode == Mode::Iso {
            return Err(End::Refused(format!(
                "`a{}` is read, and the signature does not list it",
                i + 1
            )));
        }
        let word = CTy::int(self.word(), false);
        if i < self.s.passing.regs.len() {
            return Ok(self.int(self.args.get(i).copied().unwrap_or(0), word));
        }
        let at = self.s.entry_sp.wrapping_add(self.s.passing.stack_offset(i));
        self.read(Place::Mem(at, word))
    }

    /// The place a variable's value is.
    ///
    /// # Arguments
    ///
    /// * `v` - The variable.
    fn slot_place(v: Variable) -> Place {
        match v.slot {
            Slot::Var(k) => Place::Var(k, v.ty),
            Slot::Mem(at) => Place::Mem(at, v.ty),
        }
    }

    /// Reads a place, its address wrapping at the machine word as the
    /// machine's addresses do.
    ///
    /// # Arguments
    ///
    /// * `p` - The place.
    ///
    /// # Errors
    ///
    /// A fault for memory nothing backs; unchecked for a type without a
    /// value.
    fn read(&mut self, p: Place) -> Eval<Val> {
        match p {
            Place::Var(k, ty) => {
                if self.s.mode == Mode::Iso
                    && self.set_at.get(k) == Some(&0)
                    && self.s.inputs.get(k) == Some(&false)
                {
                    let name = self.s.cells.get(k).map_or("?", |c| c.0.as_str());
                    return Err(End::Refused(format!(
                        "`{name}` is read before any line sets it"
                    )));
                }
                Ok(Val {
                    bits: self.vals.get(k).copied().unwrap_or(0),
                    ty,
                })
            }
            Place::Mem(at, ty) => {
                let Some(n) = ty.bits(self.word()).map(|b| u64::from(b / 8)) else {
                    return unchecked("a load of a type without a value");
                };
                let mut v = 0u64;
                for k in (0..n).rev() {
                    let a = at.wrapping_add(k) & mask(self.word());
                    let b = match self.emu.byte_stated(a) {
                        Some(b) => b,
                        None => {
                            if a >= self.s.objects.0 && a < self.s.objects.1 {
                                return Err(End::Refused(format!(
                                    "a byte of a local at {a:#x} is read before any line writes it"
                                )));
                            }
                            if self.handed.is_some_and(|h| a >= h && a < self.s.entry_sp) {
                                return unchecked(
                                    "a read of memory the text handed to an import, which the emulator does not fill",
                                );
                            }
                            if a >= self.s.frame_low && a < self.s.entry_sp {
                                0
                            } else {
                                return Err(End::Fault(a));
                            }
                        }
                    };
                    v = (v << 8) | u64::from(b);
                }
                Ok(Val { bits: v, ty })
            }
        }
    }

    /// Writes a value to a place, converted to the place's type, its
    /// address wrapping at the machine word.
    ///
    /// # Arguments
    ///
    /// * `p` - The place.
    /// * `v` - The value.
    ///
    /// # Returns
    ///
    /// The value as written.
    ///
    /// # Errors
    ///
    /// Unchecked for a type without a value.
    fn write(&mut self, p: Place, v: Val) -> Eval<Val> {
        match p {
            Place::Var(k, ty) => {
                let w = self.convert(v, ty)?;
                if let Some(slot) = self.vals.get_mut(k) {
                    *slot = w.bits;
                }
                if let Some(slot) = self.set_at.get_mut(k) {
                    *slot = self.line;
                }
                Ok(w)
            }
            Place::Mem(at, ty) => {
                let w = self.convert(v, ty)?;
                let Some(n) = ty.bits(self.word()).map(|b| u64::from(b / 8)) else {
                    return unchecked("a store of a type without a value");
                };
                let at = at & mask(self.word());
                poke_word(&mut self.emu, at, w.bits, n);
                for k in 0..n {
                    self.writers.insert(at.wrapping_add(k), self.line);
                }
                Ok(w)
            }
        }
    }

    /// The place an lvalue names.
    ///
    /// # Arguments
    ///
    /// * `e` - The lvalue.
    ///
    /// # Errors
    ///
    /// Unchecked for an expression that is no place this models.
    fn place(&mut self, e: &Ast) -> Eval<Place> {
        match e {
            Ast::Name(n) => match self.s.vars.get(n).copied() {
                Some(v) => Ok(Self::slot_place(v)),
                None => match global_name(n) {
                    Some((at, ty)) => Ok(Place::Mem(at, ty)),
                    None => match n
                        .strip_prefix('a')
                        .and_then(|d| d.parse::<usize>().ok())
                        .and_then(|k| k.checked_sub(1))
                    {
                        Some(i) if i >= self.s.passing.regs.len() => Ok(Place::Mem(
                            self.s.entry_sp.wrapping_add(self.s.passing.stack_offset(i)),
                            CTy::int(self.word(), false),
                        )),
                        _ => unchecked(format!("`{n}` is no place this can write")),
                    },
                },
            },
            Ast::Un(Un::Deref, a) => {
                let p = self.value(a)?;
                let Some(ty) = p.ty.pointee() else {
                    return unchecked("a dereference of a value that is no pointer");
                };
                Ok(Place::Mem(p.bits, ty))
            }
            Ast::Index(a, i) => {
                let base = self.value(a)?;
                let index = self.value(i)?;
                let Some(ty) = base.ty.pointee() else {
                    return unchecked("an index into a value that is no pointer");
                };
                let ty = if ty == CTy::of(Base::Void) {
                    CTy::int(8, false)
                } else {
                    ty
                };
                let Some(size) = ty.size(self.word()) else {
                    return unchecked("an index into a type of no known size");
                };
                let i = self.convert(index, CTy::int(64, true))?;
                Ok(Place::Mem(
                    base.bits.wrapping_add(i.bits.wrapping_mul(size)),
                    ty,
                ))
            }
            Ast::Arrow(a, field) if is_teb(a) => {
                let wide = self.word() == 64;
                let Some(&(_, at32, at64)) = TEB_FIELDS.iter().find(|(n, ..)| n == field) else {
                    return unchecked(format!("the thread block field `{field}`"));
                };
                let ty = if field == "LastErrorValue" {
                    CTy::int(32, false)
                } else {
                    CTy::int(self.word(), false)
                };
                Ok(Place::Mem(
                    self.s.teb.wrapping_add(if wide { at64 } else { at32 }),
                    ty,
                ))
            }
            Ast::Arrow(a, field) => {
                let Some(off) = field
                    .strip_prefix("field_0x")
                    .and_then(|h| u64::from_str_radix(h, 16).ok())
                else {
                    return unchecked(format!(
                        "the field `{field}`, whose offset the text does not give"
                    ));
                };
                let base_name = match &**a {
                    Ast::Name(n) => Some(n.as_str()),
                    _ => None,
                };
                let Some(ty) = base_name
                    .and_then(|n| self.s.layouts.get(n))
                    .and_then(|l| l.get(&off))
                    .copied()
                else {
                    return unchecked(format!(
                        "the field `{field}`, whose width no layout line gives"
                    ));
                };
                let base = self.value(a)?;
                Ok(Place::Mem(base.bits.wrapping_add(off), ty))
            }
            _ => unchecked("an assignment to something that is no place"),
        }
    }

    /// Evaluates an assignment, plain or compound.
    ///
    /// # Arguments
    ///
    /// * `op` - The compound operator, `None` for `=`.
    /// * `target` - The lvalue.
    /// * `source` - The value.
    ///
    /// # Errors
    ///
    /// As [`Running::value`].
    fn assign(&mut self, op: Option<Bin>, target: &Ast, source: &Ast) -> Eval<Val> {
        let p = self.place(target)?;
        if let Place::Mem(at, ty) = p
            && ty == CTy::of(Base::Wide)
        {
            if op.is_some() {
                return unchecked("a compound assignment of a 128-bit value");
            }
            let bytes = match source {
                Ast::Int(0, _) => vec![0; 16],
                other => match self.wide_place(other)? {
                    Some(from) => self.wide_bytes(from)?,
                    None => return unchecked("a 128-bit value this does not compute"),
                },
            };
            self.store(at, bytes);
            return Ok(Val { bits: at, ty });
        }
        let v = self.value(source)?;
        let v = match op {
            None => v,
            Some(op) => {
                let old = self.read(p)?;
                self.binary(op, old, v)?
            }
        };
        self.write(p, v)
    }

    /// The address of a 128-bit value an expression names: a variable, a
    /// field or a load of that type, or an assignment to one, which is made.
    ///
    /// # Arguments
    ///
    /// * `e` - The expression.
    ///
    /// # Returns
    ///
    /// The address, or `None` when the expression is no 128-bit place.
    ///
    /// # Errors
    ///
    /// As [`Running::value`].
    fn wide_place(&mut self, e: &Ast) -> Eval<Option<u64>> {
        let wide = CTy::of(Base::Wide);
        match e {
            Ast::Assign(None, t, s) if pure(t) => match self.place(t)? {
                Place::Mem(at, ty) if ty == wide => {
                    self.assign(None, t, s)?;
                    Ok(Some(at))
                }
                _ => Ok(None),
            },
            Ast::Name(_) | Ast::Arrow(..) | Ast::Un(Un::Deref, _) | Ast::Index(..) if pure(e) => {
                match self.place(e) {
                    Ok(Place::Mem(at, ty)) if ty == wide => Ok(Some(at)),
                    Ok(_) | Err(End::Unchecked(_)) => Ok(None),
                    Err(other) => Err(other),
                }
            }
            _ => Ok(None),
        }
    }

    /// The sixteen bytes of a 128-bit value in memory.
    ///
    /// # Arguments
    ///
    /// * `at` - Its address.
    ///
    /// # Errors
    ///
    /// A fault for a byte nothing backs.
    fn wide_bytes(&self, at: u64) -> Eval<Vec<u8>> {
        (0..WIDE_BYTES)
            .map(|k| self.byte(at.wrapping_add(k)))
            .collect()
    }

    /// The byte at an address.
    ///
    /// # Arguments
    ///
    /// * `at` - The address.
    ///
    /// # Errors
    ///
    /// A fault for a byte nothing backs.
    fn byte(&self, at: u64) -> Eval<u8> {
        self.emu.byte_at(at).ok_or(End::Fault(at))
    }

    /// Writes bytes from an address on, each recorded as this line's.
    ///
    /// # Arguments
    ///
    /// * `at` - The address of the first byte; later ones follow it.
    /// * `bytes` - The bytes, in address order.
    fn store(&mut self, at: u64, bytes: impl IntoIterator<Item = u8>) {
        for (k, b) in (0u64..).zip(bytes) {
            let to = at.wrapping_add(k);
            self.emu.poke(to, b);
            self.writers.insert(to, self.line);
        }
    }

    /// Applies a unary operator.
    ///
    /// # Arguments
    ///
    /// * `op` - The operator.
    /// * `a` - Its operand.
    ///
    /// # Errors
    ///
    /// As [`Running::value`].
    fn unary(&mut self, op: Un, a: &Ast) -> Eval<Val> {
        match op {
            Un::Addr => {
                if let Ast::Name(n) = a
                    && !self.s.vars.contains_key(n)
                    && let Some(Known::Code(at) | Known::Address(at) | Known::Slot(at)) =
                        self.s.known.get(n)
                {
                    return Ok(self.int(*at, CTy::of(Base::Void).to()));
                }
                match self.place(a)? {
                    Place::Mem(at, ty) => Ok(self.int(at, ty.to())),
                    Place::Var(..) => unchecked("the address of a register variable"),
                }
            }
            Un::Deref => {
                let p = self.place(&Ast::Un(Un::Deref, Box::new(a.clone())))?;
                self.read(p)
            }
            Un::LogNot => {
                let t = self.truth(a)?;
                Ok(Self::boolean(!t))
            }
            Un::Plus | Un::Neg | Un::Not => {
                let v = self.value(a)?;
                if let Some(fb) = v.ty.float() {
                    return match op {
                        Un::Plus => Ok(v),
                        Un::Neg => Ok(Val {
                            bits: float_bits(-float_of(v.bits, fb), fb),
                            ty: v.ty,
                        }),
                        _ => unchecked("`~` of a float"),
                    };
                }
                let ty = self.promote(v.ty);
                let v = self.convert(v, ty)?;
                let bits = ty.bits(self.word()).unwrap_or(64);
                let r = match op {
                    Un::Plus => return Ok(v),
                    Un::Neg => unary(UnOp::Neg, Expr::Const(v.bits), bits),
                    _ => unary(UnOp::Not, Expr::Const(v.bits), bits),
                };
                match r {
                    Expr::Const(c) => Ok(self.int(c, ty)),
                    _ => unchecked("an operator the lifter does not fold"),
                }
            }
        }
    }

    /// Applies a binary operator to two values, as C does.
    ///
    /// A bitwise operator with a float operand cuts the encoding, not the
    /// number, and the result is an unsigned integer. That is the low bits
    /// of a float stored at another width. C has no such operator; shifting
    /// a float stays unchecked.
    ///
    /// # Arguments
    ///
    /// * `op` - The operator.
    /// * `x` - The left value.
    /// * `y` - The right value.
    ///
    /// # Errors
    ///
    /// Unchecked for a pointer step of no known size or a division by
    /// zero.
    fn binary(&mut self, op: Bin, x: Val, y: Val) -> Eval<Val> {
        let word = self.word();
        if matches!(op, Bin::Add | Bin::Sub) && (x.ty.is_ptr() || y.ty.is_ptr()) {
            return self.pointer_step(op, x, y);
        }
        if matches!(op, Bin::And | Bin::Or | Bin::Xor)
            && (x.ty.float().is_some() || y.ty.float().is_some())
        {
            let c = match op {
                Bin::And => x.bits & y.bits,
                Bin::Or => x.bits | y.bits,
                Bin::Xor => x.bits ^ y.bits,
                _ => return unchecked("an integer operator on a float"),
            };
            return Ok(self.int(c, CTy::int(word, false)));
        }
        if matches!(op, Bin::Shl | Bin::Shr) {
            if x.ty.float().is_some() || y.ty.float().is_some() {
                return unchecked("a shift of a float");
            }
            let ty = if x.ty.is_ptr() {
                CTy::int(word, false)
            } else {
                self.promote(x.ty)
            };
            let a = self.convert(x, ty)?;
            let count = self.convert(y, CTy::int(64, false))?.bits;
            let bits = ty.bits(word).unwrap_or(64);
            let lop = match (op, ty.signed()) {
                (Bin::Shl, _) => Op::Shl,
                (_, true) => Op::Sar,
                (_, false) => Op::Shr,
            };
            return match fold(lop, Expr::Const(a.bits), Expr::Const(count), bits) {
                Expr::Const(c) => Ok(self.int(c, ty)),
                _ => unchecked("a shift the lifter does not fold"),
            };
        }
        let ty = self.common(x.ty, y.ty);
        let (a, b) = (self.convert(x, ty)?, self.convert(y, ty)?);
        if let Some(fb) = ty.float() {
            let (l, r) = (float_of(a.bits, fb), float_of(b.bits, fb));
            let v = match op {
                Bin::Add => l + r,
                Bin::Sub => l - r,
                Bin::Mul => l * r,
                Bin::Div => l / r,
                Bin::Lt => return Ok(Self::boolean(l < r)),
                Bin::Le => return Ok(Self::boolean(l <= r)),
                Bin::Gt => return Ok(Self::boolean(l > r)),
                Bin::Ge => return Ok(Self::boolean(l >= r)),
                Bin::Eq => return Ok(Self::boolean(l == r)),
                Bin::Ne => return Ok(Self::boolean(l != r)),
                Bin::Rem | Bin::And | Bin::Xor | Bin::Or | Bin::Shl | Bin::Shr => {
                    return unchecked("an integer operator on a float");
                }
            };
            return Ok(Val {
                bits: float_bits(v, fb),
                ty,
            });
        }
        let bits = ty.bits(word).unwrap_or(64);
        if op.compares() {
            let unsigned = !ty.signed();
            let t = if unsigned {
                match op {
                    Bin::Lt => a.bits < b.bits,
                    Bin::Le => a.bits <= b.bits,
                    Bin::Gt => a.bits > b.bits,
                    Bin::Ge => a.bits >= b.bits,
                    Bin::Eq => a.bits == b.bits,
                    _ => a.bits != b.bits,
                }
            } else {
                let (l, r) = (
                    sext(a.bits, bits).cast_signed(),
                    sext(b.bits, bits).cast_signed(),
                );
                match op {
                    Bin::Lt => l < r,
                    Bin::Le => l <= r,
                    Bin::Gt => l > r,
                    Bin::Ge => l >= r,
                    Bin::Eq => a.bits == b.bits,
                    _ => a.bits != b.bits,
                }
            };
            return Ok(Self::boolean(t));
        }
        let signed = ty.signed();
        let lop = match op {
            Bin::Mul => Op::Mul,
            Bin::Div if signed => Op::SDiv,
            Bin::Div => Op::Div,
            Bin::Rem if signed => Op::SRem,
            Bin::Rem => Op::Rem,
            Bin::Add => Op::Add,
            Bin::Sub => Op::Sub,
            Bin::And => Op::And,
            Bin::Xor => Op::Xor,
            Bin::Or => Op::Or,
            Bin::Shl | Bin::Shr | Bin::Lt | Bin::Le | Bin::Gt | Bin::Ge | Bin::Eq | Bin::Ne => {
                return unchecked("an operator out of place");
            }
        };
        match fold(lop, Expr::Const(a.bits), Expr::Const(b.bits), bits) {
            Expr::Const(c) => Ok(self.int(c, ty)),
            _ => unchecked("a division by zero"),
        }
    }

    /// Adds to or subtracts from a pointer, or subtracts two pointers.
    ///
    /// A pointer steps by its pointee's size, a `void *` by bytes. An
    /// integer minus a pointer, which is no C, is read as the byte
    /// difference its text means.
    ///
    /// # Arguments
    ///
    /// * `op` - `+` or `-`.
    /// * `x` - The left value.
    /// * `y` - The right value.
    ///
    /// # Errors
    ///
    /// Unchecked for a pointee of no known size.
    fn pointer_step(&mut self, op: Bin, x: Val, y: Val) -> Eval<Val> {
        let word = self.word();
        let size = |v: Val| v.ty.pointee().and_then(|t| t.size(word));
        if x.ty.is_ptr() && y.ty.is_ptr() {
            if op == Bin::Add {
                return unchecked("a sum of two pointers");
            }
            let Some(n) = size(x).filter(|n| *n > 0) else {
                return unchecked("a difference of pointers to a type of no known size");
            };
            let diff = x.bits.wrapping_sub(y.bits).cast_signed() / n.cast_signed();
            return Ok(self.int(diff.cast_unsigned(), CTy::int(word, true)));
        }
        let (p, i, swapped) = if x.ty.is_ptr() {
            (x, y, false)
        } else {
            (y, x, true)
        };
        if swapped && op == Bin::Sub {
            let ty = CTy::int(word, false);
            let a = self.convert(x, ty)?;
            return Ok(self.int(a.bits.wrapping_sub(p.bits), ty));
        }
        let opaque =
            p.ty.pointee()
                .is_some_and(|t| t.ptr == 0 && t.base == Base::Opaque);
        let Some(n) = size(p).or(opaque.then_some(1)) else {
            return unchecked("a step of a pointer to a type of no known size");
        };
        let k = self.convert(i, CTy::int(64, true))?.bits.wrapping_mul(n);
        let bits = if op == Bin::Add {
            p.bits.wrapping_add(k)
        } else {
            p.bits.wrapping_sub(k)
        };
        Ok(self.int(bits, p.ty))
    }

    /// Evaluates a call: a builtin by its name, else the callee run on the
    /// machine.
    ///
    /// # Arguments
    ///
    /// * `f` - The callee as written.
    /// * `args` - The arguments.
    ///
    /// # Errors
    ///
    /// As [`Running::value`], and a callee that does not return.
    fn call(&mut self, f: &Ast, args: &[Ast]) -> Eval<Val> {
        if let Ast::Name(n) = f
            && !self.s.vars.contains_key(n)
            && let Some(done) = self.literal_copy(n, args)
        {
            return done;
        }
        if let Ast::Name(n) = f
            && !self.s.vars.contains_key(n)
            && !self.s.known.contains_key(n)
        {
            if let Some(base) = n.strip_suffix("__rdx").filter(|b| !b.is_empty()) {
                let values = self.arg_values(args)?;
                let callee = self.value(&Ast::Name(base.to_owned()))?;
                let target = callee.bits & mask(self.word());
                let rdx = if let Some((t, a, _, rdx)) = &self.call_memo
                    && *t == target
                    && *a == values
                {
                    *rdx
                } else {
                    self.second_result = true;
                    let out = self.run_callee(target, &values, base);
                    self.second_result = false;
                    out?
                };
                self.emu.set_register("rax", rdx);
                return Ok(self.int(rdx, CTy::int(self.word(), false)));
            }
            if let [Ast::Name(m)] = args
                && let Some(code) = crate::winconst::value(&format!("{n}({m})"))
            {
                return Ok(self.int(u64::from(code), CTy::int(32, true)));
            }
            return self.builtin(n, args);
        }
        if matches!(f, Ast::Arrow(..)) {
            return unchecked("a call through an object");
        }
        let callee = match f {
            Ast::Un(Un::Deref, inner) => self.value(inner)?,
            other => self.value(other)?,
        };
        let values = self.arg_values(args)?;
        let name = match f {
            Ast::Name(n) => n.clone(),
            _ => format!("{:#x}", callee.bits),
        };
        let target = callee.bits & mask(self.word());
        let code = self
            .s
            .program
            .section_at(target)
            .is_some_and(|sec| sec.executable);
        if code && self.s.analysis.function(target).is_none() {
            return unchecked(
                "a call to code no function starts at: an indirect jump the text prints as a call",
            );
        }
        let rax = self.run_callee(target, &values, &name)?;
        Ok(match returned_bits(self.s.analysis, target) {
            Some(bits) => self.int(rax, CTy::int(bits, false)),
            None => self.int(rax, CTy::int(self.word(), false)),
        })
    }

    /// Evaluates a call's arguments to the machine's words.
    ///
    /// # Arguments
    ///
    /// * `args` - The argument expressions.
    ///
    /// # Errors
    ///
    /// When one does not evaluate, or is floating, which a call does not
    /// pass.
    fn arg_values(&mut self, args: &[Ast]) -> Eval<Vec<u64>> {
        let mut values = Vec::with_capacity(args.len());
        for a in args {
            let v = self.value(a)?;
            if v.ty.float().is_some() {
                return unchecked("a call with a floating argument");
            }
            let wide = if v.ty.signed() {
                sext(v.bits, v.ty.bits(self.word()).unwrap_or(64))
            } else {
                v.bits
            };
            values.push(wide);
        }
        Ok(values)
    }

    /// Runs a callee on the machine and hands back what it left in `rax`.
    ///
    /// The callee's argument registers hold the arguments the text passes
    /// and nothing else; every other register holds what the text's
    /// variable of its name holds, as the machine's does at the call, and
    /// `rax` and `rdx` hold the last call's leftovers where the text has
    /// no variable of their name, as the machine's do: a `void` callee
    /// that leaves `rax` as it found it hands back the caller's `rax`,
    /// and the bits above the `al` a `bool` callee sets are the caller's
    /// too.
    ///
    /// # Arguments
    ///
    /// * `target` - Its address.
    /// * `args` - The argument values.
    /// * `name` - Its name, for a report.
    ///
    /// # Errors
    ///
    /// The budget, or the callee's stop when it does not return.
    fn run_callee(&mut self, target: u64, args: &[u64], name: &str) -> Eval<u64> {
        let s = self.s;
        let callee = s
            .callees
            .get(&target)
            .cloned()
            .unwrap_or_else(|| passing(s.program, s.analysis, &Overlay::default(), target));
        let sentinel = if s.word == 32 {
            SENTINEL_32
        } else {
            SENTINEL_64
        };
        let leftovers = [
            (Register::RAX, self.emu.register("rax").unwrap_or(0)),
            (Register::RDX, self.emu.register("rdx").unwrap_or(0)),
        ];
        for r in [
            "rax", "rbx", "rcx", "rdx", "rsi", "rdi", "rbp", "r8", "r9", "r10", "r11", "r12",
            "r13", "r14", "r15",
        ] {
            self.emu.set_register(r, 0);
        }
        let leaked = match s.mode {
            Mode::Machine => usize::MAX,
            Mode::Iso => 0,
        };
        for (i, reg) in s.passing.regs.iter().enumerate().take(leaked) {
            if let (Some(v), Some(name)) = (self.args.get(i), full_register_name(*reg)) {
                self.emu.set_register(name, *v);
            }
        }
        for ((_, reg, _), v) in s.cells.iter().zip(&self.vals).take(leaked) {
            if let Some(r) = reg
                && *r != Register::RSP
                && !callee.regs.iter().any(|a| a.full_register() == *r)
                && let Some(name) = full_register_name(*r)
            {
                self.emu.set_register(name, *v);
            }
        }
        for (r, left) in leftovers {
            if !self.called || s.mode == Mode::Iso {
                continue;
            }
            if !s.cells.iter().any(|(_, reg, _)| *reg == Some(r)) {
                self.emu
                    .set_register(full_register_name(r).unwrap_or("rax"), left);
            }
        }
        self.emu.set_register("rsp", s.call_sp);
        poke_word(&mut self.emu, s.call_sp, sentinel, u64::from(s.word / 8));
        callee.place(&mut self.emu, s.call_sp, args);
        self.emu.stop_at(Some(sentinel));
        self.emu.set_budget(self.fuel);
        let imports = self.emu.api_calls().len();
        self.called = true;
        let run = self.emu.run(target);
        if self.emu.api_calls().len() > imports
            && let Some(low) = args
                .iter()
                .copied()
                .filter(|v| *v > s.call_sp && *v < s.entry_sp)
                .min()
        {
            self.handed = Some(self.handed.map_or(low, |h| h.min(low)));
        }
        self.fuel = self.fuel.saturating_sub(run.steps);
        self.steps += run.steps;
        for w in &run.history {
            self.writers.insert(w.addr, self.line);
        }
        let can_return = s.analysis.function(target).is_none_or(|f| {
            f.blocks.iter().any(|b| {
                matches!(b.term, BlockTerm::Ret | BlockTerm::Indirect)
                    || (b.term == BlockTerm::Jmp
                        && b.successors
                            .iter()
                            .any(|t| f.blocks.binary_search_by_key(t, |x| x.start).is_err()))
            })
        });
        match run.stop {
            Stop::Stopped(at) if at == sentinel => {
                let rax = self.emu.register("rax").unwrap_or(0);
                let rdx = self.emu.register("rdx").unwrap_or(0);
                self.call_memo = Some((target, args.to_vec(), rax, rdx));
                Ok(if self.second_result { rdx } else { rax })
            }
            Stop::Budget => Err(End::Budget),
            stop if !can_return => Err(End::Callee(name.to_owned(), stop)),
            Stop::Fault(x) if x < s.call_sp && s.call_sp - x <= STACK_REACH => unchecked(format!(
                "the call to {name} reads its own stack where nothing was set; in the binary, earlier calls leave values there"
            )),
            Stop::Fault(_)
                if !s.analysis.function(target).is_some_and(|f| {
                    let ip = self.emu.last_ip();
                    f.blocks.iter().any(|b| b.start <= ip && ip < b.end)
                }) =>
            {
                unchecked(format!(
                    "the call to {name} jumps to {:#x}, code the text does not show, and faults there",
                    self.emu.last_ip()
                ))
            }
            Stop::Fault(x) => Err(End::Callee(name.to_owned(), Stop::Fault(x))),
            Stop::Unmodeled(what) => unchecked(format!(
                "the call to {name} stops on {what}, which the emulator does not run from a call's clean state"
            )),
            other @ (Stop::Returned
            | Stop::MemoryFull(_)
            | Stop::Stopped(_)
            | Stop::Derailed(_)
            | Stop::Exited
            | Stop::Limit(_)) => unchecked(format!("the call to {name} ends as {other}")),
        }
    }

    /// Evaluates a `strcpy` or `memcpy` from a string literal by the
    /// literal's bytes, imported or not.
    ///
    /// The text writes a string a function builds in place as such a copy
    /// ([`super::stores`]), and the literal is in no image: its bytes are
    /// what the copy writes, and C fixes what either routine does with
    /// them, so the copy needs no address for its source.
    ///
    /// # Arguments
    ///
    /// * `name` - The callee's name.
    /// * `args` - The arguments.
    ///
    /// # Returns
    ///
    /// The copy's outcome, the destination on success; `None` for any
    /// other call.
    fn literal_copy(&mut self, name: &str, args: &[Ast]) -> Option<Eval<Val>> {
        let [dst, Ast::Str(bytes), rest @ ..] = args else {
            return None;
        };
        let wanted = match (name, rest) {
            ("strcpy", []) => Ok(bytes.iter().position(|b| *b == 0).map_or(0, |k| k + 1)),
            ("memcpy", [len]) => self.value(len).and_then(|n| self.length(n)).and_then(|n| {
                usize::try_from(n)
                    .ok()
                    .filter(|n| *n <= bytes.len())
                    .ok_or_else(|| End::Unchecked("a copy past its literal".to_owned()))
            }),
            _ => return None,
        };
        Some(wanted.and_then(|n| {
            let d = self.value(dst)?;
            self.store(d.bits, bytes.iter().take(n).copied());
            Ok(d)
        }))
    }

    /// Evaluates the call of a name no variable and no function holds: the
    /// operators the lifter writes as functions, the routines it reads a
    /// string instruction or a counting loop as, and `alloca`, which hands
    /// out a fresh zeroed block of memory no other object takes. The
    /// compares answer the sign C promises, `-1`, `0` or `1`, which is all
    /// `repe cmpsb` leaves in the flags.
    ///
    /// # Arguments
    ///
    /// * `name` - The callee's name.
    /// * `args` - The arguments.
    ///
    /// # Errors
    ///
    /// Unchecked for a name this does not model; a fault for memory the
    /// routine reaches that nothing backs.
    fn builtin(&mut self, name: &str, args: &[Ast]) -> Eval<Val> {
        let mut vals = Vec::with_capacity(args.len());
        for a in args {
            vals.push(self.value(a)?);
        }
        let word = self.word();
        let arg = |k: usize| {
            vals.get(k)
                .copied()
                .ok_or_else(|| End::Unchecked(format!("{name} without its arguments")))
        };
        if let Some(h) = Helper::parse(name) {
            return self.helper(h, name, &vals);
        }
        match name {
            "NtCurrentTeb" if vals.is_empty() => Ok(self.int(self.s.teb, CTy::of(Base::Void).to())),
            "alloca" => {
                let n = self.length(arg(0)?)?;
                let at = self.alloca;
                self.alloca = at.wrapping_add(n).wrapping_add(ALLOCA_GAP + 0xf) & !0xf;
                for k in 0..n {
                    self.emu.poke(at.wrapping_add(k), 0);
                }
                Ok(self.int(at, CTy::of(Base::Void).to()))
            }
            "memset" => {
                let (d, c, n) = (arg(0)?, arg(1)?, arg(2)?);
                let n = self.length(n)?;
                self.store(d.bits, (0..n).map(|_| crate::num::lo8(c.bits)));
                Ok(d)
            }
            "memcpy" | "memmove" => {
                let (d, src, n) = (arg(0)?, arg(1)?, arg(2)?);
                let n = self.length(n)?;
                let mut bytes = Vec::with_capacity(usize::try_from(n).unwrap_or(0));
                for k in 0..n {
                    let b = self.byte(src.bits.wrapping_add(k))?;
                    if name == "memcpy" {
                        self.store(d.bits.wrapping_add(k), [b]);
                    } else {
                        bytes.push(b);
                    }
                }
                self.store(d.bits, bytes);
                Ok(d)
            }
            "memcmp" | "strcmp" | "strncmp" => {
                let (x, y) = (arg(0)?, arg(1)?);
                let n = match name {
                    "strcmp" => BUILTIN_MAX,
                    _ => self.length(arg(2)?)?,
                };
                let text = name != "memcmp";
                let mut sign = 0i64;
                for k in 0..n {
                    let a = self.byte(x.bits.wrapping_add(k))?;
                    let b = self.byte(y.bits.wrapping_add(k))?;
                    if a != b {
                        sign = if a < b { -1 } else { 1 };
                        break;
                    }
                    if text && a == 0 {
                        break;
                    }
                    if k + 1 == BUILTIN_MAX {
                        return unchecked(format!("{name} past {BUILTIN_MAX} characters"));
                    }
                }
                Ok(self.int(sign.cast_unsigned(), CTy::int(32, true)))
            }
            "strlen" | "wcslen" => {
                let n = self.string_length(name, arg(0)?.bits)?;
                Ok(self.int(n, CTy::int(word, false)))
            }
            "abs" => {
                let ty = CTy::int(word, true);
                let a = self.convert(arg(0)?, ty)?;
                let Some(bits) = abs_bits(a.bits, word) else {
                    return unchecked(format!("{name} is not a value at this width"));
                };
                Ok(self.int(bits, ty))
            }
            _ => unchecked(format!("{name} is not modeled")),
        }
    }

    /// The characters before a string's terminating zero, as `strlen`
    /// counts bytes and `wcslen` counts 16-bit units.
    ///
    /// # Arguments
    ///
    /// * `name` - `strlen` or `wcslen`.
    /// * `at` - The string's address.
    ///
    /// # Errors
    ///
    /// Unchecked past [`BUILTIN_MAX`] characters; a fault for a byte
    /// nothing backs.
    fn string_length(&self, name: &str, at: u64) -> Eval<u64> {
        let unit = if name == "strlen" { 1 } else { 2 };
        let mut n = 0u64;
        loop {
            if n >= BUILTIN_MAX {
                return unchecked(format!("{name} past {BUILTIN_MAX} characters"));
            }
            let at = at.wrapping_add(n * unit);
            let lo = self.byte(at)?;
            let hi = if unit == 2 {
                self.byte(at.wrapping_add(1))?
            } else {
                0
            };
            if lo == 0 && hi == 0 {
                return Ok(n);
            }
            n += 1;
        }
    }

    /// Evaluates a helper call with its arguments' values.
    ///
    /// The arguments convert as [`Helper::operands`] says and the result
    /// has the type [`Helper::yields`] gives it, the types the helper's C
    /// definition has.
    ///
    /// # Arguments
    ///
    /// * `h` - The helper.
    /// * `name` - Its name as the text spells it, for the reason a run
    ///   stops.
    /// * `vals` - The arguments' values.
    ///
    /// # Errors
    ///
    /// Unchecked for a helper without a value here: a bit scan of zero, a
    /// width the helper does not have, a float helper of an integer, or one
    /// that reads machine state.
    fn helper(&mut self, h: Helper, name: &str, vals: &[Val]) -> Eval<Val> {
        let word = self.word();
        let first = vals.first().copied();
        let no_value = || End::Unchecked(format!("{name} is not a value at this width"));
        if let Helper::RoundToInt(round) = h {
            let (a, fb) = (
                first.ok_or_else(no_value)?,
                vals.get(1).ok_or_else(no_value)?,
            );
            let fb = u8::try_from(fb.bits).map_err(|_| no_value())?;
            let v = round.apply(a.bits, fb).ok_or_else(no_value)?;
            return Ok(self.int(v, CTy::int(word, false)));
        }
        let (bits, args) = match h.operands() {
            Operands::Raw => (
                first.map_or(word, |a| a.ty.bits(word).unwrap_or(64)),
                vals.iter().map(|v| v.bits).collect(),
            ),
            Operands::Float => {
                let a = first.ok_or_else(no_value)?;
                let fb =
                    a.ty.float()
                        .ok_or_else(|| End::Unchecked(format!("{name} of an integer")))?;
                (fb, vec![a.bits])
            }
            Operands::Word { signed } => (
                word,
                vals.iter()
                    .map(|v| self.convert(*v, CTy::int(word, signed)).map(|v| v.bits))
                    .collect::<Eval<Vec<u64>>>()?,
            ),
            Operands::Wide => (
                word,
                vals.iter()
                    .map(|v| self.convert(*v, CTy::int(64, false)).map(|v| v.bits))
                    .collect::<Eval<Vec<u64>>>()?,
            ),
        };
        let v = h.eval(&args, bits, word).ok_or_else(no_value)?;
        Ok(match (h.yields(), first) {
            (Yields::Arg, Some(a)) if a.ty.float().is_some() => Val { bits: v, ty: a.ty },
            (Yields::Arg, Some(a)) => self.int(v, a.ty),
            (Yields::Arg, None) => return Err(no_value()),
            (Yields::Unsigned(w), _) => self.int(v, CTy::int(w, false)),
            (Yields::Word { signed }, _) => self.int(v, CTy::int(word, signed)),
        })
    }

    /// A length a builtin is handed, bounded.
    ///
    /// # Arguments
    ///
    /// * `n` - The value.
    ///
    /// # Errors
    ///
    /// Unchecked past [`BUILTIN_MAX`].
    fn length(&mut self, n: Val) -> Eval<u64> {
        let n = self.convert(n, CTy::int(64, false))?.bits;
        if n > BUILTIN_MAX || n > from_usize(self.fuel) {
            return unchecked(format!("a block of {n:#x} bytes"));
        }
        self.fuel -= usize::try_from(n).unwrap_or(0);
        Ok(n)
    }
}

#[cfg(test)]
mod tests {
    use super::{End, Script, Slot, literals};
    use crate::analysis::{Analysis, Overlay};
    use crate::program::{Arch, Program, Section};

    /// An unwritten frame byte reads as the fresh stack's zero, the value
    /// the machine reads there.
    ///
    /// A load that spans a written slot and its padding keeps each side's
    /// bytes: `*(uint64_t*)&local_30` holds the store to `local_30` in its
    /// low byte, `local_2c`'s store in its high half, and zeros between.
    ///
    /// # Panics
    ///
    /// When the load picks a written byte up one lane early, or faults.
    #[test]
    fn an_unwritten_frame_byte_reads_as_the_fresh_stack() {
        let mut code = vec![0xccu8; 0x40];
        code[..0x11].copy_from_slice(&[
            0x48, 0x83, 0xec, 0x30, // ASM: sub rsp,30h
            0x89, 0x54, 0x24, 0x04, // ASM: mov [rsp+4],edx
            0xc6, 0x04, 0x24, 0x0b, // ASM: mov byte [rsp],0Bh
            0x48, 0x8b, 0x04, 0x24, // ASM: mov rax,[rsp]
            0xc3, // ASM: ret
        ]);
        let p = Program::raw_x64(&code);
        let a = Analysis::compute(&p);
        let source = "// signature: uint64_t f(uint64_t a1, uint64_t a2)
// layout a1: 0x0 u64
uint8_t local_30;
uint32_t local_2c;

local_30 = 11;
local_2c = a2;
return *(uint64_t*)&local_30;
";
        let s = Script::read(&p, &a, &Overlay::default(), 0x1000, source).unwrap();
        let ends_with = |rhs: &str, x: &str| {
            let head = format!(
                "// signature: uint64_t f(uint64_t a1, uint64_t a2)
uint8_t local_30;
uint32_t local_2c;

local_30 = 11;
local_2c = {rhs};
return {x};
"
            );
            Script::read(&p, &a, &Overlay::default(), 0x1000, &head)
                .unwrap()
                .run(&[0x5000, 0x80], &[], 100)
                .unwrap()
                .end
        };
        assert_eq!(
            ends_with("0x80", "*(uint8_t*)((char*)&local_30 + 1)"),
            End::Returned(Some(0)),
            "a constant write stays off the padding byte"
        );
        assert_eq!(
            ends_with("a2", "*(uint8_t*)((char*)&local_30 + 1)"),
            End::Returned(Some(0)),
            "a parameter write stays off the padding byte"
        );
        assert_eq!(
            ends_with("0x80", "*(uint64_t*)&local_30"),
            End::Returned(Some(0x0000_0080_0000_000b)),
            "a constant write four bytes up reads in the high half"
        );
        let bare = "// signature: uint64_t f(uint64_t a1, uint64_t a2)
uint8_t local_30;

local_30 = 11;
return *(uint64_t*)&local_30;
";
        assert_eq!(
            Script::read(&p, &a, &Overlay::default(), 0x1000, bare)
                .unwrap()
                .run(&[0x5000, 0x80], &[], 100)
                .unwrap()
                .end,
            End::Returned(Some(11)),
            "a u64 load over one written byte reads zeros past it"
        );
        let r = s
            .run(&[0x5000, 0x80], &[(0x5000, vec![0; 8])], 100)
            .unwrap();
        assert_eq!(r.end, End::Returned(Some(0x0000_0080_0000_000b)));
    }

    /// A helper the text writes only in a condition runs.
    ///
    /// The overflow tests and the parity flag are helpers of the closed
    /// vocabulary, which the reader evaluates instead of leaving the run
    /// unchecked.
    ///
    /// # Panics
    ///
    /// When the run stops unchecked or returns another value.
    #[test]
    fn a_condition_helper_runs() {
        let p = Program::raw_x64(&[0xc3; 0x10]);
        let a = Analysis::compute(&p);
        let source = "// signature: uint64_t f(uint64_t a1, uint64_t a2)

return saddo16(a1, a2) + parity8(a1) + uaddo64(a1, a2);
";
        let s = Script::read(&p, &a, &Overlay::default(), 0x1000, source).unwrap();
        let r = s.run(&[0x7fff, 1], &[], 100).unwrap();
        assert_eq!(r.end, End::Returned(Some(2)));
        let r = s.run(&[u64::MAX, 1], &[], 100).unwrap();
        assert_eq!(r.end, End::Returned(Some(2)));
    }

    /// On a 32-bit target an address wraps at 32 bits, as the machine's do:
    /// `((uint16_t*)a2)[a1]` with `a1` all ones reads the word before `a2`.
    ///
    /// # Panics
    ///
    /// When the read faults past four gigabytes or reads elsewhere.
    #[test]
    fn a_32_bit_address_wraps_as_the_machine_wraps_it() {
        let mut bytes = vec![0xc3u8; 0x200];
        bytes[0x100] = 0x34;
        bytes[0x101] = 0x12;
        let text = Section::mapped(".text", 0x1000, 0, 0x100, false, true);
        let data = Section::mapped(".data", 0x2000, 0x100, 0x100, true, false);
        let p = Program::raw(bytes, Arch::X86, 0, Some(0x1000), vec![text, data]);
        let a = Analysis::compute(&p);
        let source = "// signature: uint32_t f(uint32_t a1, uint32_t a2)

return ((uint16_t*)a2)[a1];
";
        let s = Script::read(&p, &a, &Overlay::default(), 0x1000, source).unwrap();
        let r = s.run(&[0xffff_ffff, 0x2002], &[], 100).unwrap();
        assert_eq!(r.end, End::Returned(Some(0x1234)));
    }

    /// A name two functions share is the one the function calls: the text
    /// spells an overload by its bare name.
    ///
    /// # Panics
    ///
    /// When the run calls the other function.
    #[test]
    fn a_shared_name_is_the_function_called() {
        let mut code = vec![0xccu8; 0x50];
        code[..11].copy_from_slice(&[
            0xe8, 0x3b, 0x00, 0x00, 0x00, // ASM: call 0x1040
            0xe8, 0x16, 0x00, 0x00, 0x00, // ASM: call 0x1020
            0xc3, // ASM: ret
        ]);
        code[0x10..0x16].copy_from_slice(&[0xb8, 1, 0, 0, 0, 0xc3]);
        code[0x20..0x26].copy_from_slice(&[0xb8, 2, 0, 0, 0, 0xc3]);
        code[0x40..0x46].copy_from_slice(&[
            0xe8, 0xcb, 0xff, 0xff, 0xff, // ASM: call 0x1010
            0xc3, // ASM: ret
        ]);
        let p = Program::raw_x64(&code);
        let a = Analysis::compute(&p);
        let mut o = Overlay::default();
        o.names.insert(0x1010, "f".to_owned());
        o.names.insert(0x1020, "f".to_owned());
        let source = "// signature: uint64_t g(void)

return f();
";
        let s = Script::read(&p, &a, &o, 0x1000, source).unwrap();
        let r = s.run(&[], &[], 1000).unwrap();
        assert_eq!(r.end, End::Returned(Some(2)));
    }

    /// A callee stopping for a reason of the emulator's leaves a run
    /// unchecked.
    ///
    /// A branch on flags the clean state at a call leaves unset, or a jump
    /// into the function's own body printed as a call, is no difference of
    /// the text. A callee that cannot return (it ends in a trap or a call
    /// that never comes back, a panic) is one: the text took a path the
    /// binary, which returned, did not.
    ///
    /// # Panics
    ///
    /// When either run ends as anything but unchecked.
    #[test]
    fn a_callee_stopping_for_the_emulator_is_unchecked() {
        let mut code = vec![0xccu8; 0x20];
        code[..6].copy_from_slice(&[
            0xe8, 0x0b, 0x00, 0x00, 0x00, // ASM: call 0x1010
            0xc3, // ASM: ret
        ]);
        code[0x10..0x13].copy_from_slice(&[
            0x7e, 0x00, // ASM: jle 0x1012
            0xc3, // ASM: ret
        ]);
        let p = Program::raw_x64(&code);
        let a = Analysis::compute(&p);
        let o = Overlay::default();
        for source in [
            "// signature: uint64_t g(void)

return sub_1010();
",
            "// signature: uint64_t g(void)

return (*0x1005)();
",
        ] {
            let s = Script::read(&p, &a, &o, 0x1000, source).unwrap();
            let r = s.run(&[], &[], 1000).unwrap();
            assert!(matches!(r.end, End::Unchecked(_)), "{source}: {:?}", r.end);
        }
        let mut panics = code.clone();
        panics[0x12..0x14].copy_from_slice(&[0x0f, 0x0b]); // ASM: ud2
        let p = Program::raw_x64(&panics);
        let a = Analysis::compute(&p);
        let source = "// signature: uint64_t g(void)

return sub_1010();
";
        let s = Script::read(&p, &a, &o, 0x1000, source).unwrap();
        let r = s.run(&[], &[], 1000).unwrap();
        assert!(matches!(r.end, End::Callee(..)), "{:?}", r.end);
    }

    /// A call to code no function starts at is a jump the text prints as a
    /// call, whose code expects another frame: unchecked, not a difference.
    ///
    /// # Panics
    ///
    /// When the run ends as anything but unchecked.
    #[test]
    fn a_call_to_no_function_is_unchecked() {
        let p = Program::raw_x64(&[
            0xff, 0xe0, // ASM: jmp rax
            0x48, 0x8b, 0x44, 0x24, 0x40, // ASM: mov rax,[rsp+0x40]
            0xc3, // ASM: ret
        ]);
        let a = Analysis::compute(&p);
        assert!(a.function(0x1002).is_none());
        let source = "// signature: uint64_t g(void)

return (*0x1002)();
";
        let s = Script::read(&p, &a, &Overlay::default(), 0x1000, source).unwrap();
        let r = s.run(&[], &[], 1000).unwrap();
        assert!(matches!(r.end, End::Unchecked(_)), "{:?}", r.end);
    }

    /// A local the text hands an import and then reads is unchecked when
    /// nothing set it: the emulator answers an import without filling what
    /// it is handed, where the real one would.
    ///
    /// # Panics
    ///
    /// When the read is reported as a fault.
    #[test]
    fn a_local_an_import_was_handed_is_unchecked() {
        let mut p = Program::raw_x64(&[0xc3]);
        p.symbols.push(crate::program::Symbol {
            name: "kernel32.dll!GetSystemTimeAsFileTime".to_owned(),
            addr: 0x1800,
            kind: crate::program::SymbolKind::Import,
        });
        let a = Analysis::compute(&p);
        let source = "// signature: uint64_t g(void)
uint64_t local_10;

GetSystemTimeAsFileTime(&local_10);
return local_10;
";
        let s = Script::read(&p, &a, &Overlay::default(), 0x1000, source).unwrap();
        let r = s.run(&[], &[], 1000).unwrap();
        assert!(matches!(r.end, End::Unchecked(_)), "{:?}", r.end);
    }

    /// A return names each variable its value reads with the line that set
    /// it, and line zero for one no line set that is no parameter.
    ///
    /// # Panics
    ///
    /// When the sources differ.
    #[test]
    fn a_return_names_where_its_variables_were_set() {
        let p = Program::raw_x64(&[0xc3]);
        let a = Analysis::compute(&p);
        let source = "// signature: uint64_t g(uint64_t a1)
uint64_t rax, rcx;

rcx = a1;
return rax + rcx + a1;
";
        let s = Script::read(&p, &a, &Overlay::default(), 0x1000, source).unwrap();
        let r = s.run(&[5], &[], 100).unwrap();
        assert_eq!(r.sources, [("rax".to_owned(), 0), ("rcx".to_owned(), 4)]);
    }

    /// The image's literals are found by their bytes, narrow and wide, each
    /// at its first copy, and a run that is no literal is left out.
    ///
    /// # Panics
    ///
    /// When a literal is missed, found elsewhere, or a non-literal kept.
    #[test]
    fn literals_are_indexed_where_they_start() {
        let mut data = vec![0u8; 0x100];
        data[0x10..0x14].copy_from_slice(b"abc\0");
        data[0x20..0x24].copy_from_slice(b"abc\0");
        data[0x40..0x46].copy_from_slice(&[b'h', 0, b'i', 0, 0, 0]);
        data[0x60..0x63].copy_from_slice(&[0x01, 0x02, 0]);
        let rdata = Section::mapped(".rdata", 0x2000, 0, 0x100, false, false);
        let p = Program::raw(data, Arch::X86_64, 0, None, vec![rdata]);
        let index = literals(&p);
        assert_eq!(index.get(b"abc\0".as_slice()), Some(&0x2010));
        assert_eq!(
            index.get([b'h', 0, b'i', 0, 0, 0].as_slice()),
            Some(&0x2040)
        );
        assert_eq!(index.get([0x01, 0x02, 0].as_slice()), None);
    }

    /// Reads a text over a one-`ret` image and runs it.
    ///
    /// # Panics
    ///
    /// When the text does not read or nothing runs.
    fn run(text: &str, args: &[u64]) -> (End, usize) {
        let p = Program::raw_x64(&[0xc3]);
        let a = Analysis::compute(&p);
        let s = Script::read(&p, &a, &Overlay::default(), 0x1000, text).unwrap();
        let r = s.run(args, &[], 10_000).unwrap();
        (r.end, r.line)
    }

    /// A case named in the function's enum header is that constant, and so
    /// is the name compared against the same variable.
    ///
    /// # Panics
    ///
    /// When a path returns another value.
    #[test]
    fn an_enumerator_is_the_constant_its_header_names() {
        let cases = "// signature: uint64_t f(uint64_t a1)\n// enum values of a1: 2 values, Off = 0, On = 1\n\nswitch (a1) {\ncase Off: {\n  return 10;\n}\ncase On: {\n  return 11;\n}\ndefault: {\n  return 12;\n}\n}\n";
        assert_eq!(run(cases, &[0]).0, End::Returned(Some(10)));
        assert_eq!(run(cases, &[1]).0, End::Returned(Some(11)));
        assert_eq!(run(cases, &[2]).0, End::Returned(Some(12)));
        let compared = "// signature: uint64_t f(uint64_t a1)\n// enum values of a1: 2 values, Off = 0, On = 1\n\nif (a1 == On) {\n  return 11;\n}\nreturn 0;\n";
        assert_eq!(run(compared, &[1]).0, End::Returned(Some(11)));
        assert_eq!(run(compared, &[0]).0, End::Returned(Some(0)));
    }

    /// Loops, switches and gotos run as C runs them, and the return is cut
    /// to the declared type.
    ///
    /// # Panics
    ///
    /// When a path returns another value or ends on another line.
    #[test]
    fn control_flow_runs_as_c_runs_it() {
        let text = "// signature: uint32_t f(uint64_t a1, uint64_t a2)\nuint64_t rax, rcx;\n\nrax = 0;\nfor (rcx = 0; rcx < a1; rcx += 1) {\n  rax += rcx;\n}\nswitch (a2) {\ncase 1: case 2: {\n  rax <<= 32;\n}\ncase 3: {\n  rax += 1;\n  break;\n}\ndefault: {\n  goto L_9;\n}\n}\nreturn rax;\nL_9:\nreturn ~rax;\n";
        assert_eq!(run(text, &[4, 3]).0, End::Returned(Some(7)));
        assert_eq!(run(text, &[4, 1]).0, End::Returned(Some(1)));
        assert_eq!(run(text, &[4, 9]), (End::Returned(Some(0xffff_fff9)), 22));
    }

    /// C's conversions hold: an `int32_t` compares signed, a narrow value
    /// promotes, a `uint8_t *` steps by bytes and a `uint32_t *` by four.
    ///
    /// # Panics
    ///
    /// When a conversion differs from C's.
    #[test]
    fn conversions_follow_c() {
        let text = "// signature: uint64_t f(uint64_t a1)\nuint64_t rax;\nuint8_t rcx;\n\nrcx = 0xff;\nif ((int32_t)a1 < 0) {\n  return (uint64_t)((uint32_t*)0 + 2) + rcx + 1;\n}\nreturn (int64_t)(int8_t)rcx;\n";
        assert_eq!(run(text, &[0xffff_ffff]).0, End::Returned(Some(8 + 0x100)));
        assert_eq!(run(text, &[1]).0, End::Returned(Some(u64::MAX)));
        let bits = "// signature: int32_t f(int32_t a1)\ndouble d;\n\nd = (double)(((float)a1) & 0xffffffff);\nif (d < 1.0) {\n  return 1;\n}\nreturn 2;\n";
        assert_eq!(run(bits, &[1]).0, End::Returned(Some(1)));
        let pick = "// signature: uint64_t f(uint64_t a1)

if ((a1 == 0 ? 1 : a1) <= -32) {
  return 1;
}
return 0;
";
        assert_eq!(run(pick, &[0]).0, End::Returned(Some(1)));
    }

    /// What the reader does not model stops the run at its line, unchecked,
    /// rather than guessing.
    ///
    /// # Panics
    ///
    /// When the run ends otherwise or elsewhere.
    #[test]
    fn what_it_cannot_read_stops_at_its_line() {
        let text = "// signature: uint64_t f(uint64_t a1)\nuint64_t rax;\n\nrax = a1;\nrax = frobnicate(rax);\nreturn rax;\n";
        let (end, line) = run(text, &[1]);
        assert_eq!(end, End::Unchecked("frobnicate is not modeled".to_owned()));
        assert_eq!(line, 5);
    }

    /// A stack slot lives at its frame offset, so its address is a real
    /// one and two slots that overlap share bytes.
    ///
    /// # Panics
    ///
    /// When a slot is no memory or the overlap is lost.
    #[test]
    fn stack_slots_share_their_frame() {
        let p = Program::raw_x64(&[0xc3]);
        let a = Analysis::compute(&p);
        let text = "// signature: uint64_t f(void)\nuint64_t local_10;\nuint32_t local_c;\n\nlocal_10 = 0x1122334455667788;\nlocal_c = 0;\nreturn local_10;\n";
        let s = Script::read(&p, &a, &Overlay::default(), 0x1000, text).unwrap();
        assert!(matches!(
            s.vars.get("local_c").map(|v| v.slot),
            Some(Slot::Mem(_))
        ));
        let r = s.run(&[], &[], 100).unwrap();
        assert_eq!(r.end, End::Returned(Some(0x5566_7788)));
    }

    /// Runs a text once as ISO C on a function that only returns.
    ///
    /// # Arguments
    ///
    /// * `text` - The text, header first.
    /// * `args` - The argument values.
    ///
    /// # Panics
    ///
    /// When the text does not read.
    fn run_iso(text: &str, args: &[u64]) -> End {
        let p = Program::raw_x64(&[0xc3]);
        let a = Analysis::compute(&p);
        let s = Script::read_iso(&p, &a, &Overlay::default(), 0x1000, text).unwrap();
        s.run(args, &[], 10_000).unwrap().end
    }

    /// In ISO mode each local is an object of its own: the overlapping
    /// slots that share the frame's bytes in the machine's reading keep
    /// their own, and the control flow and conversions are C's as before.
    ///
    /// # Panics
    ///
    /// When a store to one local reaches another, or a run differs.
    #[test]
    fn iso_locals_are_objects_of_their_own() {
        let text = "// signature: uint64_t f(void)
uint64_t local_10;
uint32_t local_c;

local_10 = 0x1122334455667788;
local_c = 0;
return local_10;
";
        assert_eq!(
            run_iso(text, &[]),
            End::Returned(Some(0x1122_3344_5566_7788))
        );
        let text = "// signature: uint32_t f(uint64_t a1, uint64_t a2)
uint64_t rax, rcx;

rax = 0;
for (rcx = 0; rcx < a1; rcx += 1) {
  rax += rcx;
}
if (a2 == 3) {
  rax += 1;
}
return rax;
";
        assert_eq!(run_iso(text, &[4, 3]), End::Returned(Some(7)));
        assert_eq!(run_iso(text, &[4, 1]), End::Returned(Some(6)));
    }

    /// In ISO mode a read of what no line set is refused.
    ///
    /// That is a variable, a local's byte past the one written, a register
    /// the text never declares and a parameter the signature does not
    /// list. The machine's reading answers the first from the entry's
    /// register.
    ///
    /// # Panics
    ///
    /// When a read of poison runs on.
    #[test]
    fn iso_refuses_a_read_of_what_no_line_set() {
        let unset = "// signature: uint64_t f(uint64_t a1)
uint64_t rax;

return rax + a1;
";
        assert!(matches!(run_iso(unset, &[1]), End::Refused(why) if why.contains("`rax`")));
        assert_eq!(run(unset, &[1]).0, End::Returned(Some(1)));
        let past = "// signature: uint64_t f(void)
uint8_t local_30;

local_30 = 11;
return *(uint64_t*)&local_30;
";
        assert!(matches!(run_iso(past, &[]), End::Refused(why) if why.contains("local")));
        let register = "// signature: uint64_t f(uint64_t a1)

return rdx;
";
        assert!(matches!(run_iso(register, &[1]), End::Refused(why) if why.contains("`rdx`")));
        let unlisted = "// signature: uint64_t f(uint64_t a1)

return a2;
";
        assert!(matches!(run_iso(unlisted, &[1]), End::Refused(why) if why.contains("`a2`")));
    }

    /// A callee finds the text's register variables in the registers no
    /// argument travels in, and hands back the width it returns.
    ///
    /// As the machine's callee finds the caller's, one that leaves `rax`
    /// as it found it hands back the caller's `rax`. A callee handing back
    /// a byte hands back that byte, as C converts a `uint8_t` result, not
    /// the caller's bits above it.
    ///
    /// # Panics
    ///
    /// When a run returns otherwise.
    #[test]
    fn a_callee_finds_the_texts_registers_and_hands_back_its_width() {
        let mut code = vec![
            0xe8, 0x0b, 0x00, 0x00, 0x00, // ASM: call 0x1010
            0xe8, 0x16, 0x00, 0x00, 0x00, // ASM: call 0x1020
            0x0f, 0xb6, 0xc0, // ASM: movzx eax,al
            0xc3, // ASM: ret
        ];
        code.resize(0x10, 0xcc);
        code.push(0xc3); // ASM: ret
        code.resize(0x20, 0xcc);
        code.extend([0xb0, 0x07, 0xc3]); // ASM: mov al,7; ret
        let p = Program::raw_x64(&code);
        let a = Analysis::compute(&p);
        let o = Overlay::default();
        for (body, want) in [
            ("rax = 5;\nrax = sub_1010();\nreturn rax;\n", 5),
            ("rax = 0x100;\nrax = sub_1020();\nreturn rax;\n", 7),
        ] {
            let source = format!("// signature: uint64_t f(void)\nuint64_t rax;\n\n{body}");
            let s = Script::read(&p, &a, &o, 0x1000, &source).unwrap();
            let r = s.run(&[], &[], 1000).unwrap();
            assert_eq!(r.end, End::Returned(Some(want)), "{body}");
        }
    }
}
