//! String literals the direct callers of a function pass it.
//!
//! A `gettext` of a parameter does not show the format. The calls that
//! reach this function do, when every one of them passes a string or a
//! null and nothing else takes the function's address. The notes are
//! `// formats a1: "..." "..."` lines for the type pass to read and then drop.

use super::super::line::is_ident;
use crate::analysis::{Analysis, RefKind};
use crate::isa::x86::{Instruction, InstructionInfoFactory, Mnemonic, OpAccess, OpKind, Register};
use crate::program::{BinaryFormat, Program};
use crate::strings::cstr_text_at;

/// Writes the caller-format notes under the signature line.
///
/// # Arguments
///
/// * `text` - The function as the type pass is about to read it.
/// * `callers` - The image, the analysis and the function. `None` leaves
///   the text as it is.
///
/// # Returns
///
/// The text with one note per parameter whose callers pass a literal.
pub(super) fn noted(text: &str, callers: Option<(&Program, &Analysis, u64)>) -> String {
    let Some((program, analysis, entry)) = callers else {
        return text.to_owned();
    };
    let notes = format_lines(text, program, analysis, entry);
    if notes.is_empty() {
        return text.to_owned();
    }
    let mut out = String::with_capacity(text.len().saturating_add(notes.len().saturating_mul(64)));
    let mut placed = false;
    for line in text.lines() {
        out.push_str(line);
        out.push('\n');
        if !placed && line.starts_with("// signature: ") {
            for note in &notes {
                out.push_str(note);
                out.push('\n');
            }
            placed = true;
        }
    }
    if placed { out } else { text.to_owned() }
}

/// What one call passes for the argument under inspection.
enum Passed {
    /// A quoted string literal.
    Lit(String),
    /// A null, which names no format.
    Null,
}

/// What an instruction does to the register being followed.
enum Def {
    /// It does not write the register.
    Keep,
    /// It clears the register.
    Null,
    /// It loads a string literal into the register.
    Lit(String),
    /// It copies another register into it.
    Follow(Register),
    /// It writes the register in a way that is not one of those.
    Unknown,
}

/// The `// formats` notes for parameters whose callers pass string literals.
///
/// A parameter is named only when every direct call and tail jump passes
/// a string or a null for it, and no other reference of the function
/// exists. Anything else is left off, so a message whose text is not
/// visible stays untyped.
///
/// # Arguments
///
/// * `text` - The function as the type pass is about to read it.
/// * `program` - The loaded image.
/// * `analysis` - Discovery results.
/// * `entry` - The function's entry.
///
/// # Returns
///
/// One note per parameter that has at least one literal. Empty when the
/// text has no `gettext` or the callers do not agree on a visible literal.
fn format_lines(text: &str, program: &Program, analysis: &Analysis, entry: u64) -> Vec<String> {
    if !text.contains("gettext") && !text.contains("_(") {
        return Vec::new();
    }
    let mut out = Vec::new();
    for (index, name) in param_names(text).iter().enumerate() {
        let Some(lits) = argument_literals(program, analysis, entry, index) else {
            continue;
        };
        if lits.is_empty() {
            continue;
        }
        let mut line = format!("// formats {name}:");
        for lit in &lits {
            line.push(' ');
            line.push_str(lit);
        }
        out.push(line);
    }
    out
}

/// Parameter names on the `// signature:` line, in argument order.
///
/// # Arguments
///
/// * `text` - The function, header lines included.
///
/// # Returns
///
/// The names. Empty when the text has no signature.
fn param_names(text: &str) -> Vec<String> {
    let Some(sig) = text.lines().find(|l| l.starts_with("// signature: ")) else {
        return Vec::new();
    };
    let mut names = Vec::new();
    for piece in sig.split(['(', ',', ')']).skip(1) {
        let piece = piece.trim();
        if piece.is_empty() {
            continue;
        }
        let Some((_, name)) = piece.rsplit_once(' ') else {
            continue;
        };
        let name = name.strip_prefix('*').unwrap_or(name);
        if is_ident(name) {
            names.push(name.to_owned());
        }
    }
    names
}

/// The quoted literals passed as argument `index`, when every caller shows one.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Discovery results.
/// * `entry` - The callee.
/// * `index` - The argument, from zero.
///
/// # Returns
///
/// The literals, or `None` when a caller does not show a string or a null,
/// the argument is not in a register, or the function's address is taken.
fn argument_literals(
    program: &Program,
    analysis: &Analysis,
    entry: u64,
    index: usize,
) -> Option<Vec<String>> {
    let reg = arg_register(program, index)?;
    let mut lits = Vec::new();
    for site in direct_calls(analysis, entry)? {
        match passed_at(program, analysis, site, reg)? {
            Passed::Lit(text) => lits.push(text),
            Passed::Null => {}
        }
    }
    Some(lits)
}

/// Call and tail-jump sites, or `None` when any other reference exists.
///
/// # Arguments
///
/// * `analysis` - Discovery results.
/// * `entry` - The callee.
///
/// # Returns
///
/// The sites, or `None` when the address is stored, indexed or tabulated.
fn direct_calls(analysis: &Analysis, entry: u64) -> Option<Vec<u64>> {
    let mut calls = Vec::new();
    for site in analysis.xrefs_to(entry) {
        match site.kind {
            RefKind::Call | RefKind::Jmp => calls.push(site.va),
            RefKind::Data | RefKind::Index | RefKind::Table | RefKind::Ptr => return None,
        }
    }
    Some(calls)
}

/// The register a 64-bit convention uses for argument `index`.
///
/// # Arguments
///
/// * `program` - The loaded image, for its format.
/// * `index` - The argument, from zero.
///
/// # Returns
///
/// The register, or `None` on a 32-bit target or once the arguments have
/// moved to the stack.
fn arg_register(program: &Program, index: usize) -> Option<Register> {
    const SYSV: [Register; 6] = [
        Register::RDI,
        Register::RSI,
        Register::RDX,
        Register::RCX,
        Register::R8,
        Register::R9,
    ];
    const WIN: [Register; 4] = [Register::RCX, Register::RDX, Register::R8, Register::R9];
    if program.arch.bitness() != Some(64) {
        return None;
    }
    let regs: &[Register] = match program.format {
        BinaryFormat::Elf | BinaryFormat::MachO => &SYSV,
        BinaryFormat::Pe | BinaryFormat::Raw | BinaryFormat::Archive => &WIN,
    };
    regs.get(index).copied()
}

/// The literal or null in `reg` at `call`, from the straight-line block behind it.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Discovery results, for the block.
/// * `call` - The call or jump instruction.
/// * `reg` - The argument register, a full register.
///
/// # Returns
///
/// What the call passes, or `None` when the block does not show it.
fn passed_at(program: &Program, analysis: &Analysis, call: u64, reg: Register) -> Option<Passed> {
    let function = analysis.function_at(call)?;
    let block = function
        .blocks
        .iter()
        .find(|b| call >= b.start && call < b.end)?;
    let instrs = crate::analysis::functions::decode_block(program, 64, block);
    let at = instrs.iter().position(|i| i.ip() == call)?;
    let mut factory = InstructionInfoFactory::new();
    let mut reg = reg;
    for instr in instrs.get(..at)?.iter().rev() {
        match defined(program, instr, &mut factory, reg) {
            Def::Keep => {}
            Def::Null => return Some(Passed::Null),
            Def::Lit(text) => return Some(Passed::Lit(text)),
            Def::Follow(next) => reg = next,
            Def::Unknown => return None,
        }
    }
    None
}

/// How `instr` defines `reg`.
///
/// # Arguments
///
/// * `program` - The loaded image, for a literal an address names.
/// * `instr` - The instruction.
/// * `factory` - Register-access scratch.
/// * `reg` - The full register being followed.
///
/// # Returns
///
/// The definition, [`Def::Keep`] when `instr` does not write `reg`.
fn defined(
    program: &Program,
    instr: &Instruction,
    factory: &mut InstructionInfoFactory,
    reg: Register,
) -> Def {
    let writes = factory.info(instr).used_registers().iter().any(|used| {
        used.register().full_register() == reg
            && matches!(
                used.access(),
                OpAccess::Write
                    | OpAccess::ReadWrite
                    | OpAccess::CondWrite
                    | OpAccess::ReadCondWrite
            )
    });
    if !writes {
        return Def::Keep;
    }
    let dest = instr.op0_kind() == OpKind::Register && instr.op0_register().full_register() == reg;
    let wide = dest && instr.op0_register().size() >= 4;
    if !wide {
        return Def::Unknown;
    }
    match instr.mnemonic() {
        Mnemonic::Xor if same_reg(instr) => Def::Null,
        Mnemonic::Mov => mov_def(program, instr),
        Mnemonic::Lea if instr.is_ip_rel_memory_operand() => {
            literal(program, instr.memory_displacement64()).map_or(Def::Unknown, Def::Lit)
        }
        _ => Def::Unknown,
    }
}

/// Tells whether both operands of `instr` are the same full register.
///
/// # Arguments
///
/// * `instr` - The instruction.
///
/// # Returns
///
/// Whether both operands are that register.
fn same_reg(instr: &Instruction) -> bool {
    instr.op0_kind() == OpKind::Register
        && instr.op1_kind() == OpKind::Register
        && instr.op0_register().full_register() == instr.op1_register().full_register()
}

/// What a `mov` into `reg` defines.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `instr` - The move, whose destination is already the register followed.
///
/// # Returns
///
/// The definition, or [`Def::Unknown`] when the source is not a register,
/// zero, or a string address.
fn mov_def(program: &Program, instr: &Instruction) -> Def {
    match instr.op1_kind() {
        OpKind::Register => {
            let src = instr.op1_register();
            if src.size() >= 4 && src.is_gpr() {
                Def::Follow(src.full_register())
            } else {
                Def::Unknown
            }
        }
        OpKind::Immediate8
        | OpKind::Immediate16
        | OpKind::Immediate32
        | OpKind::Immediate64
        | OpKind::Immediate8to16
        | OpKind::Immediate8to32
        | OpKind::Immediate8to64
        | OpKind::Immediate32to64 => {
            let value = instr.immediate(1);
            if value == 0 {
                Def::Null
            } else {
                literal(program, value).map_or(Def::Unknown, Def::Lit)
            }
        }
        _ => Def::Unknown,
    }
}

/// The quoted C literal at `addr`, when the whole string fits on one note.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `addr` - The first byte of the string.
///
/// # Returns
///
/// `"text"` with quotes and backslashes escaped, or `None` when no short
/// string is there.
fn literal(program: &Program, addr: u64) -> Option<String> {
    const CAP: usize = 512;
    let (len, text) = cstr_text_at(program, addr, 1, CAP)?;
    if len > CAP {
        return None;
    }
    let mut out = String::from("\"");
    for c in text.chars() {
        match c {
            '\\' => out.push_str("\\\\"),
            '"' => out.push_str("\\\""),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if c.is_control() => return None,
            c => out.push(c),
        }
    }
    out.push('"');
    Some(out)
}
