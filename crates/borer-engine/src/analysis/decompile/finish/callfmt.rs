//! String literals the direct callers of a function pass it.
//!
//! A `gettext` of a parameter does not show the format. The calls that
//! reach this function do, when every one of them passes a string or a
//! null, nothing else takes the function's address, and the function is
//! not exported. The notes are
//! `// formats a1: "..." "..."` lines for the type pass to read and then drop.

use super::super::line::is_ident;
use crate::analysis::{Analysis, RefKind};
use crate::isa::x86::{Instruction, InstructionInfoFactory, Mnemonic, OpAccess, OpKind, Register};
use crate::program::{BinaryFormat, Program, SymbolKind};
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
/// a string or a null for it, no other reference of the function exists,
/// and the function is not exported. Anything else is left off, so a
/// message whose text is not visible stays untyped.
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
    if exported(program, entry) {
        return Vec::new();
    }
    let Some(params) = parameters(text) else {
        return Vec::new();
    };
    let classes: Vec<Option<Class>> = params.iter().map(|p| p.class).collect();
    let mut out = Vec::new();
    for (index, param) in params.iter().enumerate() {
        if param.class != Some(Class::Int) {
            continue;
        }
        let Some(lits) = argument_literals(program, analysis, entry, &classes, index) else {
            continue;
        };
        if lits.is_empty() {
            continue;
        }
        let mut line = format!("// formats {}:", param.name);
        for lit in &lits {
            line.push(' ');
            line.push_str(lit);
        }
        out.push(line);
    }
    out
}

/// How a parameter is passed on a 64-bit machine.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Class {
    /// An integer or a pointer, in an integer argument register.
    Int,
    /// A float, in an xmm register.
    Float,
}

/// One parameter of the signature under inspection.
struct Param {
    /// The parameter's name.
    name: String,
    /// How it is passed. `None` is a type this does not place in a register.
    class: Option<Class>,
}

/// One piece of a signature parameter list.
enum Parsed {
    /// `void`, `...`, or an empty piece: not a parameter.
    Skip,
    /// A parameter this can name.
    One(Param),
    /// A piece whose type or name this cannot place.
    Bad,
}

/// Parameters of the `// signature:` line, when the return needs no hidden pointer.
///
/// An aggregate return, or a parameter that is not an integer, a pointer
/// or a float, has no register this can name. The scan then writes no
/// notes, rather than reading the wrong argument.
///
/// # Arguments
///
/// * `text` - The function, header lines included.
///
/// # Returns
///
/// The parameters in argument order, or `None` when the signature is
/// missing or its layout is not one this can count.
fn parameters(text: &str) -> Option<Vec<Param>> {
    let sig = text
        .lines()
        .find_map(|l| l.strip_prefix("// signature: "))?;
    if !return_supported(sig) {
        return None;
    }
    let mut out = Vec::new();
    for piece in sig.split(['(', ',', ')']).skip(1) {
        match parse_param(piece) {
            Parsed::Skip => {}
            Parsed::One(param) => out.push(param),
            Parsed::Bad => return None,
        }
    }
    Some(out)
}

/// Tells whether `sig`'s return value leaves the integer argument registers alone.
///
/// # Arguments
///
/// * `sig` - The text after `// signature: `.
///
/// # Returns
///
/// Whether the return is void, an integer, a pointer or a float. An
/// aggregate would take a hidden pointer in the first integer register.
fn return_supported(sig: &str) -> bool {
    let head = sig.split('(').next().unwrap_or("").trim();
    let mut words: Vec<&str> = head.split_whitespace().collect();
    let Some(name) = words.pop() else {
        return false;
    };
    let stars = name.chars().take_while(|&c| c == '*' || c == '&').count();
    if !is_ident(&name[stars..]) {
        return false;
    }
    if stars > 0 {
        return true;
    }
    let ty = words.join(" ");
    ty == "void" || scalar_class(&ty).is_some()
}

/// The parameter `piece` declares.
///
/// # Arguments
///
/// * `piece` - One parameter from the signature, commas already split.
///
/// # Returns
///
/// [`Parsed::Skip`] for `void` and `...`, [`Parsed::Bad`] when the piece
/// is not a plain name, and the parameter otherwise.
fn parse_param(piece: &str) -> Parsed {
    let piece = piece.trim();
    if piece.is_empty() || piece == "void" || piece == "..." {
        return Parsed::Skip;
    }
    let Some((ty, name)) = piece.rsplit_once(' ') else {
        return Parsed::Bad;
    };
    let stars = name.chars().take_while(|&c| c == '*' || c == '&').count();
    if !is_ident(&name[stars..]) {
        return Parsed::Bad;
    }
    let class = if stars > 0 {
        Some(Class::Int)
    } else {
        scalar_class(ty)
    };
    Parsed::One(Param {
        name: name[stars..].to_owned(),
        class,
    })
}

/// The register class of a scalar `ty`, ignoring a pointer star.
///
/// # Arguments
///
/// * `ty` - The type, as the signature spells it.
///
/// # Returns
///
/// The class, or `None` for a struct, a union, or a type this does not know.
fn scalar_class(ty: &str) -> Option<Class> {
    let mut bare = ty.trim();
    while let Some(rest) = bare
        .strip_prefix("const ")
        .or_else(|| bare.strip_prefix("volatile "))
    {
        bare = rest.trim();
    }
    if matches!(bare, "float" | "double" | "long double") {
        return Some(Class::Float);
    }
    if bare.starts_with("struct ") || bare.starts_with("union ") || bare.contains('[') {
        return None;
    }
    if bare.starts_with("enum ") {
        return Some(Class::Int);
    }
    if matches!(
        bare,
        "size_t"
            | "ssize_t"
            | "ptrdiff_t"
            | "intptr_t"
            | "uintptr_t"
            | "wchar_t"
            | "char8_t"
            | "char16_t"
            | "char32_t"
            | "bool"
            | "_Bool"
    ) {
        return Some(Class::Int);
    }
    let words: Vec<&str> = bare.split_whitespace().collect();
    if !words.is_empty()
        && words.iter().all(|w| {
            matches!(
                *w,
                "signed" | "unsigned" | "short" | "long" | "int" | "char" | "bool" | "_Bool"
            )
        })
    {
        return Some(Class::Int);
    }
    let digits = bare
        .strip_prefix("uint")
        .or_else(|| bare.strip_prefix("int"))
        .and_then(|rest| rest.strip_suffix("_t"))?;
    (!digits.is_empty() && digits.chars().all(|c| c.is_ascii_digit())).then_some(Class::Int)
}

/// The quoted literals passed as argument `index`, when every caller shows one.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Discovery results.
/// * `entry` - The callee.
/// * `classes` - The parameter classes, in argument order.
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
    classes: &[Option<Class>],
    index: usize,
) -> Option<Vec<String>> {
    let reg = register_at(
        program.format,
        program.arch.bitness().unwrap_or(0),
        classes,
        index,
    )?;
    let mut lits = Vec::new();
    for site in direct_calls(analysis, entry)? {
        match passed_at(program, analysis, site, reg)? {
            Passed::Lit(text) => lits.push(text),
            Passed::Null => {}
        }
    }
    Some(lits)
}

/// Tells whether `entry` is a symbol another module can call.
///
/// A caller outside this image does not appear in the references, so the
/// literals found here are not every value the parameter can hold.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `entry` - The function's entry.
///
/// # Returns
///
/// Whether an exported symbol is at `entry`.
fn exported(program: &Program, entry: u64) -> bool {
    program
        .symbols
        .iter()
        .any(|s| s.kind == SymbolKind::Export && s.addr == entry)
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

/// The integer register argument `index` is passed in.
///
/// System V counts only integer and pointer parameters: a float before
/// the argument does not move it to the next integer register. Windows
/// counts every parameter, and a float still occupies its slot. A type
/// this cannot place, at or before `index`, has no answer.
///
/// # Arguments
///
/// * `format` - The image's binary format, which picks the convention.
/// * `bitness` - Decoder bitness. Only 64 is counted.
/// * `classes` - The parameter classes, in argument order.
/// * `index` - The argument, from zero.
///
/// # Returns
///
/// The register, or `None` when the argument is a float, is past the
/// integer registers, or the layout is not one this can count.
fn register_at(
    format: BinaryFormat,
    bitness: u32,
    classes: &[Option<Class>],
    index: usize,
) -> Option<Register> {
    const SYSV: [Register; 6] = [
        Register::RDI,
        Register::RSI,
        Register::RDX,
        Register::RCX,
        Register::R8,
        Register::R9,
    ];
    const WIN: [Register; 4] = [Register::RCX, Register::RDX, Register::R8, Register::R9];
    if bitness != 64 || classes.get(index).copied() != Some(Some(Class::Int)) {
        return None;
    }
    match format {
        BinaryFormat::Elf | BinaryFormat::MachO => {
            let mut slot = 0usize;
            for (i, class) in classes.iter().enumerate() {
                match class {
                    Some(Class::Float) => {}
                    Some(Class::Int) if i == index => return SYSV.get(slot).copied(),
                    Some(Class::Int) => slot += 1,
                    None => return None,
                }
            }
            None
        }
        BinaryFormat::Pe | BinaryFormat::Raw | BinaryFormat::Archive => {
            if classes.iter().take(index).any(Option::is_none) {
                return None;
            }
            WIN.get(index).copied()
        }
    }
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

#[cfg(test)]
#[expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]
mod tests {
    use super::*;

    /// A float uses an xmm register. On System V the next integer stays in
    /// `rdi`; on Windows it takes the next slot. An unknown type is not counted.
    #[test]
    fn a_float_does_not_shift_past_its_convention() {
        let both = [Some(Class::Int), Some(Class::Int)];
        assert_eq!(
            register_at(BinaryFormat::Elf, 64, &both, 1),
            Some(Register::RSI)
        );
        let shifted = [Some(Class::Float), Some(Class::Int), Some(Class::Int)];
        assert_eq!(
            register_at(BinaryFormat::Elf, 64, &shifted, 1),
            Some(Register::RDI)
        );
        assert_eq!(
            register_at(BinaryFormat::Elf, 64, &shifted, 2),
            Some(Register::RSI)
        );
        assert_eq!(register_at(BinaryFormat::Elf, 64, &shifted, 0), None);
        assert_eq!(
            register_at(BinaryFormat::Pe, 64, &shifted, 1),
            Some(Register::RDX)
        );
        let unknown = [None, Some(Class::Int)];
        assert_eq!(register_at(BinaryFormat::Elf, 64, &unknown, 1), None);
        assert_eq!(register_at(BinaryFormat::Elf, 32, &both, 0), None);
        let text = "// signature: void f(float a1, char *a2, uint64_t a3)\n";
        let params = parameters(text).unwrap_or_default();
        let classes: Vec<Option<Class>> = params.iter().map(|p| p.class).collect();
        assert_eq!(
            register_at(BinaryFormat::Elf, 64, &classes, 1),
            Some(Register::RDI)
        );
        assert!(parameters("// signature: struct stat f(char *a1)\n").is_none());
    }
}
