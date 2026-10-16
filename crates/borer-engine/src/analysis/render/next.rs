//! The reads a function's facts point at next: at most [`NEXT_MAX`]
//! `borer://` resources with the function's address filled in, which the
//! summary and the decompile header end with.
//!
//! An agent follows a breadcrumb at the moment it is useful far more
//! reliably than it reads a catalogue: an agent rebuilt an emulator by hand
//! while `borer://emulate` was there to be read. Each rule fires on a fact
//! the analysis already has (a dispatch loop, a flattened switch, a switch
//! on an argument, a counted loop comparing a few bits of a product, a
//! compare against a telling constant, a loop that mixes and stores bytes,
//! fields read through an argument), the rules are tried
//! in a fixed order, and the first [`NEXT_MAX`] that fire are kept.

use super::*;
use crate::analysis::decompile::{EXPLODE_MAX, decompile, lift};

/// Most next steps one function is given.
pub const NEXT_MAX: usize = 2;

/// The resources a next step can name, in the order the rules are tried.
pub const NEXT_RESOURCES: [&str; 7] = [
    "vm",
    "flat",
    "scenarios",
    "partial",
    "solve",
    "emulate",
    "layout",
];

/// Fewest distinct offsets a function dereferences through one argument
/// before the argument reads as a pointer to a structure.
const LAYOUT_FIELDS_MIN: usize = 3;

/// Returns the next steps a function's facts point at, each a resource URI
/// with the function's address filled in and a few words on why.
///
/// Built once per function and overlay through [`Analysis::derived`]; the
/// decompilation the rules read is the memoized one.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `a` - The analysis.
/// * `o` - Names in force, which the decompilation reads.
/// * `entry` - The function's entry.
///
/// # Returns
///
/// At most [`NEXT_MAX`] steps, in rule order; none for an address that is
/// no function's entry, or for code that is not x86.
pub fn next_steps(p: &Program, a: &Analysis, o: &Overlay, entry: u64) -> Arc<Vec<String>> {
    a.derived.get_or_build_item(
        "next_steps",
        o.fingerprint(),
        entry,
        || steps_of(p, a, o, entry),
        |steps| steps.iter().map(String::capacity).sum(),
    )
}

/// Builds the steps [`next_steps`] memoizes.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `a` - The analysis.
/// * `o` - Names in force.
/// * `entry` - The function's entry.
///
/// # Returns
///
/// As [`next_steps`].
fn steps_of(p: &Program, a: &Analysis, o: &Overlay, entry: u64) -> Vec<String> {
    if !matches!(p.arch.isa(), Some(crate::isa::Isa::X86 { .. })) {
        return Vec::new();
    }
    let (Some(f), Some(bits)) = (a.function(entry), p.arch.bitness()) else {
        return Vec::new();
    };
    let text = decompile(p, a, o, entry).unwrap_or_default();
    let params = parameters(&text);
    let rules: [&dyn Fn() -> Option<String>; 7] = [
        &|| vm_step(p, a, f),
        &|| flat_step(a, f),
        &|| switch_step(a, f, &text),
        &|| partial_step(p, a, o, f),
        &|| check_step(p, a, f, bits, &text, params),
        &|| loop_step(p, f, bits),
        &|| layout_step(p, f, bits, &text, params),
    ];
    rules
        .iter()
        .filter_map(|rule| rule())
        .take(NEXT_MAX)
        .collect()
}

/// Points a function holding an interpreter's dispatch loop at its
/// handlers ([`vm_dispatch_tsv`]).
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `a` - The analysis.
/// * `f` - The function.
///
/// # Returns
///
/// The step, or `None` when the function holds no dispatch loop.
fn vm_step(p: &Program, a: &Analysis, f: &Function) -> Option<String> {
    let handlers = dispatch_loops_in(p, a, f)
        .iter()
        .map(|d| d.handlers.len())
        .max()?;
    Some(format!(
        "borer://vm/{:#x} (a dispatch loop of {handlers} handlers: what each does)",
        f.entry
    ))
}

/// Points a flattened function at its cases ([`flattening_tsv`]).
///
/// # Arguments
///
/// * `a` - The analysis.
/// * `f` - The function.
///
/// # Returns
///
/// The step, or `None` when no switch of the function is a flattening
/// dispatcher.
fn flat_step(a: &Analysis, f: &Function) -> Option<String> {
    let d = f
        .blocks
        .iter()
        .flat_map(|b| a.jump_tables.range(b.start..b.end))
        .find_map(|(site, cases)| flattened(a, *site, cases))?;
    Some(format!(
        "borer://flat/{:#x} (flattened: {} cases around one dispatch)",
        f.entry, d.cases
    ))
}

/// Points a function that switches on an argument at one scenario per
/// value, the default included.
///
/// # Arguments
///
/// * `a` - The analysis.
/// * `f` - The function.
/// * `text` - Its decompiled text.
///
/// # Returns
///
/// The step, or `None` when the function has no jump table or its text
/// switches on no argument.
fn switch_step(a: &Analysis, f: &Function, text: &str) -> Option<String> {
    let cases = f
        .blocks
        .iter()
        .flat_map(|b| a.jump_tables.range(b.start..b.end))
        .map(|(_, targets)| targets.len())
        .max()?;
    let slot = text.lines().find_map(|l| switched_argument(l.trim()))?;
    let to = cases.saturating_add(1).min(EXPLODE_MAX);
    Some(format!(
        "borer://scenarios/{:#x}/a{slot}=0..{to} (a switch on a{slot}: what each value runs)",
        f.entry
    ))
}

/// The argument a `switch (aN) {` line switches on.
///
/// # Arguments
///
/// * `line` - One line of pseudo-C, trimmed.
///
/// # Returns
///
/// `N`, or `None` when the line switches on anything else.
fn switched_argument(line: &str) -> Option<u32> {
    let rest = line.strip_prefix("switch (a")?;
    let digits = rest.find(|c: char| !c.is_ascii_digit())?;
    let (n, tail) = rest.split_at(digits);
    if !tail.starts_with(')') {
        return None;
    }
    n.parse().ok().filter(|n| *n > 0)
}

/// Points a counted loop that leaks a few bits of a product at the
/// hidden-number report ([`partial_tsv`]), ahead of sampling it.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `a` - The analysis.
/// * `o` - User names.
/// * `f` - The function.
///
/// # Returns
///
/// The step, or `None` when the function has no such loop, or the
/// multiplicand was not shown to be loop-invariant.
fn partial_step(p: &Program, a: &Analysis, o: &Overlay, f: &Function) -> Option<String> {
    partial::partial_hint(p, a, o, f.entry)
}

/// Points a function that takes arguments and compares against a telling
/// constant at the argument value it accepts ([`solve_tsv`]).
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `a` - The analysis.
/// * `f` - The function.
/// * `bits` - The decoder bitness.
/// * `text` - Its decompiled text.
/// * `params` - How many parameters its signature lists.
///
/// # Returns
///
/// The step, or `None` when it takes no argument or compares against no
/// telling constant.
fn check_step(
    p: &Program,
    a: &Analysis,
    f: &Function,
    bits: u32,
    text: &str,
    params: usize,
) -> Option<String> {
    if params == 0 {
        return None;
    }
    let value = check_constants(p, a, f.entry, bits)
        .first()
        .copied()
        .or_else(|| compared_constant(text))?;
    Some(format!(
        "borer://solve/{:#x} (compares against {value:#x}: the a1 it accepts)",
        f.entry
    ))
}

/// The first telling constant a decompiled text compares with `==` or
/// `!=`.
///
/// # Arguments
///
/// * `text` - The decompiled text.
///
/// # Returns
///
/// The constant ([`telling_constant`]), or `None` when no compare has one.
fn compared_constant(text: &str) -> Option<u64> {
    text.lines()
        .filter(|l| !l.trim_start().starts_with("//"))
        .filter(|l| l.contains(" == ") || l.contains(" != "))
        .flat_map(|l| l.split(|c: char| !c.is_ascii_alphanumeric()))
        .filter_map(|t| match t.strip_prefix("0x") {
            Some(hex) => u64::from_str_radix(hex, 16).ok(),
            None => t
                .starts_with(|c: char| c.is_ascii_digit())
                .then(|| t.parse::<u64>().ok())
                .flatten(),
        })
        .find(|v| telling_constant(*v))
}

/// Points a function with a loop that mixes bytes (xor, rotate) and
/// stores them at a run of it ([`emulate_tsv`]): a decoder or a checksum
/// reads plainer run than read.
///
/// Each block is decoded once; a loop is the blocks from a back edge's
/// target up to the block that takes it.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `f` - The function.
/// * `bits` - The decoder bitness.
///
/// # Returns
///
/// The step, or `None` when no loop of the function both mixes and
/// stores, or the architecture is not emulated.
fn loop_step(p: &Program, f: &Function, bits: u32) -> Option<String> {
    if p.refuses(Feature::Emulate).is_some() {
        return None;
    }
    let mut factory = InstructionInfoFactory::new();
    let blocks: Vec<(u64, bool, bool)> = f
        .blocks
        .iter()
        .map(|b| {
            let instrs = crate::analysis::functions::decode_block(p, bits, b);
            let stored = instrs.iter().any(|i| stores(i, &mut factory));
            (b.start, instrs.iter().any(mixes), stored)
        })
        .collect();
    let shaped = f.blocks.iter().any(|latch| {
        latch
            .successors
            .iter()
            .filter(|&&head| head >= f.start && head <= latch.start)
            .any(|&head| {
                let body = || {
                    blocks
                        .iter()
                        .filter(move |(start, _, _)| *start >= head && *start < latch.end)
                };
                body().any(|b| b.1) && body().any(|b| b.2)
            })
    });
    shaped.then(|| {
        format!(
            "borer://emulate/{:#x} (a loop that mixes bytes by xor or rotate and stores them: run it)",
            f.entry
        )
    })
}

/// Whether an instruction mixes bits the way a decoder or a hash does: a
/// rotate, or an xor that is not the zeroing idiom.
///
/// # Arguments
///
/// * `i` - The instruction.
fn mixes(i: &Instruction) -> bool {
    let zeroing = i.op_count() == 2
        && i.op0_kind() == OpKind::Register
        && i.op1_kind() == OpKind::Register
        && i.op0_register() == i.op1_register();
    matches!(
        i.mnemonic(),
        Mnemonic::Rol | Mnemonic::Ror | Mnemonic::Rcl | Mnemonic::Rcr
    ) || (i.mnemonic() == Mnemonic::Xor && !zeroing)
}

/// Whether an instruction writes memory as data: a call's return address
/// and a push's slot are the stack's own traffic, not a stored result.
///
/// # Arguments
///
/// * `i` - The instruction.
/// * `factory` - The decoder's access tables, reused across calls.
fn stores(i: &Instruction, factory: &mut InstructionInfoFactory) -> bool {
    i.flow_control() == FlowControl::Next
        && i.mnemonic() != Mnemonic::Push
        && factory.info(i).used_memory().iter().any(|m| {
            matches!(
                m.access(),
                OpAccess::Write
                    | OpAccess::ReadWrite
                    | OpAccess::CondWrite
                    | OpAccess::ReadCondWrite
            )
        })
}

/// Points a function that dereferences several offsets of one argument at
/// the structure those reads propose ([`layout_tsv`]).
///
/// # Arguments
///
/// * `p` - The loaded image, for its calling convention.
/// * `f` - The function.
/// * `bits` - The decoder bitness.
/// * `text` - Its decompiled text.
/// * `params` - How many parameters its signature lists.
///
/// # Returns
///
/// The step, naming the register the argument arrives in, or `None` when
/// no register argument is dereferenced at [`LAYOUT_FIELDS_MIN`] offsets.
fn layout_step(p: &Program, f: &Function, bits: u32, text: &str, params: usize) -> Option<String> {
    let registers = lift::conv(p, bits).args;
    registers
        .iter()
        .take(params)
        .enumerate()
        .find_map(|(slot, register)| {
            let n = slot + 1;
            let fields = fields_through(text, n);
            (fields >= LAYOUT_FIELDS_MIN).then(|| {
                format!(
                    "borer://layout/{:#x},{} (reads {fields} fields through a{n}: its structure)",
                    f.entry,
                    format!("{register:?}").to_lowercase()
                )
            })
        })
}

/// How many fields the decompiler laid out behind one argument: the
/// offsets its `// layout aN: 0x8 u32, 0x10 u64` header lists, wrapped
/// lines included.
///
/// # Arguments
///
/// * `text` - The decompiled text.
/// * `n` - The argument, counting from one.
///
/// # Returns
///
/// The count; zero when the text lays out no structure behind it.
fn fields_through(text: &str, n: usize) -> usize {
    let head = format!("// layout a{n}:");
    let mut lines = text.lines().skip_while(|l| !l.starts_with(&head));
    let Some(first) = lines.next() else {
        return 0;
    };
    std::iter::once(first)
        .chain(lines.take_while(|l| l.starts_with("//  ")))
        .map(|l| l.matches("0x").count())
        .sum()
}

/// How many parameters a decompiled text's `// signature:` line lists.
///
/// # Arguments
///
/// * `text` - The decompiled text.
///
/// # Returns
///
/// The count; zero for `(void)`, `()` or a text with no signature line.
fn parameters(text: &str) -> usize {
    let Some(sig) = text.lines().find_map(|l| l.strip_prefix("// signature: ")) else {
        return 0;
    };
    let (Some(open), Some(close)) = (sig.find('('), sig.rfind(')')) else {
        return 0;
    };
    let inner = sig.get(open + 1..close).unwrap_or("").trim();
    if inner.is_empty() || inner == "void" {
        return 0;
    }
    let mut depth = 0usize;
    let mut count = 1;
    for c in inner.chars() {
        match c {
            '(' => depth += 1,
            ')' => depth = depth.saturating_sub(1),
            ',' if depth == 0 => count += 1,
            _ => {}
        }
    }
    count
}
