//! The calls a function's text makes, read back from the effects the lifter
//! recorded beside its lines ([`Effect`](super::lift::Effect)), each argument in the
//! position its callee reads it from.
//!
//! Nothing is lifted again: the memoized decompilation already holds every
//! call as a value, so asking for a function's call sites costs what its
//! decompilation cost, once.

use std::sync::Arc;

use super::abi::{self, Conv};
use super::expr::{Expr, Key, Names, negative_magnitude};
use super::lift::{ArgAt, Call, Callee, EffectKind, Shown};
use super::{Analysis, Overlay, decompiled_cached, name_of};
use crate::program::Program;
use crate::strings::{cstr_text_at, wstr_text_at};

/// Longest string argument read whole, in characters.
const TEXT_MAX: usize = 512;

/// Most argument positions a call is laid out over; a stack word further
/// up is not an argument any callee declares.
const ARGS_MAX: usize = 32;

/// One argument a call passes, as the decompiler resolves it at the site.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct CallArg {
    /// The argument as the pseudo-C writes it, constants in hex; `?` where
    /// the lifter recorded no value for the position.
    pub(crate) text: String,
    /// Its value, when it is a constant.
    pub(crate) value: Option<u64>,
    /// The text of the string literal it points at, when it points at one.
    pub(crate) string: Option<String>,
}

impl CallArg {
    /// The argument of a position the lifter recorded no value for.
    fn unseen() -> CallArg {
        CallArg {
            text: "?".to_owned(),
            value: None,
            string: None,
        }
    }
}

/// One call a function's text makes.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct CallSite {
    /// The call (or tail jump) instruction.
    pub(crate) at: u64,
    /// What it reaches: the callee's entry when the call is direct, or the
    /// constant address it reads its target from (an import slot, a
    /// function pointer in data); `None` for a target computed at run time.
    pub(crate) target: Option<u64>,
    /// The call is a tail call, `return f(...)`.
    pub(crate) tail: bool,
    /// The text passes fewer stack words than the callee is stated to read.
    pub(crate) short: bool,
    /// The arguments by position, the first one `a1`.
    pub(crate) args: Vec<CallArg>,
}

/// Lists the calls a function's text makes, with their arguments.
///
/// The calls come from the effects the emission recorded
/// ([`EffectKind::Call`]), so they are exactly the calls the pseudo-C
/// shows, and each argument is the value the text passes. An argument
/// keeps the position its callee reads it from: a register's slot in the
/// calling convention, a stack word's distance above the return address.
/// A position the lifter recorded no value for (a register an earlier call
/// left unknown, which the text names by itself) holds `?`. Library
/// routines the text names for a
/// string instruction (`memset` for `rep stos`) are not calls to anything
/// and are left out.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Discovery results, holding the memoized decompilations.
/// * `overlay` - Names in force.
/// * `caller` - The function's entry.
///
/// # Returns
///
/// The calls in block order, or `None` when the function does not
/// decompile or the architecture has no calling convention.
pub(crate) fn call_sites(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    caller: u64,
) -> Option<Vec<CallSite>> {
    let (bitness, first_stack) = match program.arch.isa()? {
        crate::isa::Isa::X86 { bits } => {
            let conv = abi::conv(program, bits);
            (bits, conv.word + conv.shadow)
        }
        crate::isa::Isa::A64 => (64, 0),
        crate::isa::Isa::A32 => (32, 0),
    };
    let f = analysis.function(caller)?;
    let memo = decompiled_cached(program, analysis, overlay, overlay.fingerprint(), caller);
    let d = memo.as_ref().as_ref()?;
    let conv = abi::conv(program, bitness);
    let names = Names {
        program,
        analysis,
        overlay,
        this_param: false,
        result_param: None,
        own_name: Arc::from(crate::analysis::bare_name(&name_of(
            analysis, overlay, caller,
        ))),
        debug_params: Arc::from(Vec::new()),
        debug_locals: Arc::default(),
        first_stack,
        stack_params: 0,
        reg_params: u32::try_from(conv.args.len()).unwrap_or(0),
        word: conv.word,
        slot_types: Arc::default(),
        global_types: Arc::default(),
    };
    let mut out = Vec::new();
    for (i, b) in f.blocks.iter().enumerate() {
        for e in d.effects.block(i, b.start).unwrap_or_default() {
            let EffectKind::Call(c) = e.kind else {
                continue;
            };
            let target = match &c.callee {
                Callee::Direct(t) | Callee::Through(Expr::Const(t)) => Some(*t),
                Callee::Through(Expr::Var(Key::Global(slot, _))) => Some(*slot),
                Callee::Through(Expr::Deref(at, _)) => match **at {
                    Expr::Const(slot) => Some(slot),
                    _ => None,
                },
                Callee::Through(_) => None,
                Callee::Builtin(..) => continue,
            };
            out.push(CallSite {
                at: e.at,
                target,
                tail: c.shown == Shown::Tail,
                short: c.short,
                args: positioned(&c, conv, bitness, &names),
            });
        }
    }
    Some(out)
}

/// Lays a call's recorded arguments out by the position the callee reads
/// each from, `?` filling a position nothing was recorded for.
///
/// A register argument takes its slot in the convention; on a 32-bit
/// target the registers (`this`, a `__fastcall` pair) come first in the
/// order recorded. A stack word takes the position after the register
/// slots, counted from the first word above the return address (and the
/// shadow space). A floating register on a convention that numbers its
/// floats apart (System V) follows the position before it, since nothing
/// at the site says where among the integers the source placed it.
///
/// # Arguments
///
/// * `c` - The recorded call.
/// * `conv` - The caller's calling convention.
/// * `bitness` - `32` or `64`.
/// * `n` - Names for rendering the values.
fn positioned(c: &Call, conv: &Conv, bitness: u32, n: &Names<'_>) -> Vec<CallArg> {
    let word = conv.word.max(1);
    let regs32 = c
        .args
        .iter()
        .filter(|(at, _)| matches!(at, ArgAt::Reg(_)))
        .count();
    let regs_a64 = c
        .args
        .iter()
        .filter(|(at, _)| matches!(at, ArgAt::A64(_) | ArgAt::A32(_)))
        .count();
    let base = conv.shadow
        + if c.shown == Shown::Tail && regs_a64 == 0 {
            word
        } else {
            0
        };
    let mut placed: Vec<Option<CallArg>> = Vec::new();
    let mut regs_seen = 0usize;
    for (at, e) in &c.args {
        let next = placed.len();
        let pos = match *at {
            ArgAt::Reg(_) if bitness == 32 => {
                regs_seen += 1;
                regs_seen - 1
            }
            ArgAt::Reg(r) if conv.args.contains(&r) || !conv.float_seq => {
                conv.slot(r).unwrap_or(next)
            }
            ArgAt::Reg(_) | ArgAt::Operand | ArgAt::A64(_) | ArgAt::A32(_) => next,
            ArgAt::Stack(off, _) => {
                let first = if bitness == 32 {
                    regs32
                } else if regs_a64 > 0 {
                    regs_a64
                } else {
                    conv.args.len()
                };
                usize::try_from((off - base) / word)
                    .ok()
                    .filter(|_| off >= base && (off - base) % word == 0)
                    .map_or(next, |k| first + k)
            }
        };
        if pos >= ARGS_MAX {
            continue;
        }
        if placed.len() <= pos {
            placed.resize(pos + 1, None);
        }
        if let Some(slot) = placed.get_mut(pos) {
            *slot = Some(argument(e, n));
        }
    }
    placed
        .into_iter()
        .map(|a| a.unwrap_or_else(CallArg::unseen))
        .collect()
}

/// Renders one recorded argument.
///
/// A constant that names nothing reads in hex (negative when it is a small
/// negative number of the word), so a filter written `a3=0x40` reads the
/// way the row does; anything else reads as the pseudo-C writes it.
///
/// # Arguments
///
/// * `e` - The value.
/// * `n` - Names for rendering it.
fn argument(e: &Expr, n: &Names<'_>) -> CallArg {
    match e {
        Expr::Const(v) => {
            let named = n.const_name(*v, true);
            let string = named.as_deref().and_then(|shown| {
                if shown.starts_with("L\"") {
                    wstr_text_at(n.program, *v, 1, TEXT_MAX).map(|(_, t)| t)
                } else if shown.starts_with('"') {
                    cstr_text_at(n.program, *v, 1, TEXT_MAX).map(|(_, t)| t)
                } else {
                    None
                }
            });
            let text = named.unwrap_or_else(|| match negative_magnitude(*v, n.word) {
                Some(m) => format!("-{m}"),
                None if *v < 10 => v.to_string(),
                None => format!("{v:#x}"),
            });
            CallArg {
                text,
                value: Some(*v),
                string,
            }
        }
        Expr::Str(s) => CallArg {
            text: s.clone(),
            value: None,
            string: Some(
                s.trim_start_matches('L')
                    .trim_start_matches('"')
                    .trim_end_matches('"')
                    .to_owned(),
            ),
        },
        other => CallArg {
            text: other.render(n),
            value: None,
            string: None,
        },
    }
}
