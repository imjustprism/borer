//! How a decompiled function is called: the convention its code shows and
//! the signature its text prints.
//!
//! A run passes its arguments where the decompiler reads them (the
//! registers of the function's convention, then the stack past the return
//! address and any shadow space), and types each one by the signature the
//! reader sees, so a run and the text agree on what `a2` is.

use crate::isa::x86::Register;

use super::abi;
use super::ctext::{Base, CTy, Tok, closing, leading_type, split_top, tokens};
use crate::analysis::{Analysis, Overlay};
use crate::emulate::Emulator;
use crate::num::from_usize;
use crate::program::Program;

/// How a function takes its arguments: the registers in order, then the
/// stack from a frame offset.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Passing {
    /// The argument registers, in convention order.
    pub(crate) regs: Vec<Register>,
    /// Frame offset of the first stack-passed argument, past the return
    /// address and any shadow space.
    pub(crate) first_stack: u64,
    /// The stack word in bytes.
    pub(crate) word: u64,
}

impl Passing {
    /// Puts arguments where a callee entered with the stack pointer at
    /// `sp` reads them.
    ///
    /// # Arguments
    ///
    /// * `emu` - The machine.
    /// * `sp` - The stack pointer the callee is entered with.
    /// * `args` - The argument values, in order.
    pub(crate) fn place(&self, emu: &mut Emulator<'_>, sp: u64, args: &[u64]) {
        for (i, v) in args.iter().enumerate() {
            self.place_arg(emu, sp, i, *v);
        }
    }

    /// Puts one argument where a callee entered with the stack pointer at
    /// `sp` reads it, leaving the others as they are.
    ///
    /// # Arguments
    ///
    /// * `emu` - The machine.
    /// * `sp` - The stack pointer the callee is entered with.
    /// * `i` - The argument's position from zero: `a1` is 0.
    /// * `v` - The value.
    pub(crate) fn place_arg(&self, emu: &mut Emulator<'_>, sp: u64, i: usize, v: u64) {
        match self.regs.get(i) {
            Some(r) => {
                emu.set_register(register_name(*r), v);
            }
            None => {
                let at = sp.wrapping_add(self.stack_offset(i));
                poke_word(emu, at, v, self.word);
            }
        }
    }

    /// The frame offset of a stack-passed argument.
    ///
    /// # Arguments
    ///
    /// * `i` - The argument's position from zero, past the registers.
    pub(super) fn stack_offset(&self, i: usize) -> u64 {
        let past = from_usize(i.saturating_sub(self.regs.len()));
        self.first_stack.wrapping_add(past.wrapping_mul(self.word))
    }
}

/// How a function takes its arguments, as its decompilation reads them.
///
/// The convention is the function's own [`super::Shape`], read through the
/// memo its callers' decompilations read it from.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Its functions.
/// * `overlay` - User names.
/// * `entry` - The function's entry; an address no function starts at
///   (an import's stub) takes the target's default convention.
///
/// # Returns
///
/// The registers and the stack layout its arguments use.
pub(crate) fn passing(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    entry: u64,
) -> Passing {
    let bitness = program.arch.bitness().unwrap_or(64);
    let conv = match analysis.function(entry).filter(|f| f.entry == entry) {
        Some(f) => {
            abi::shape(
                program,
                analysis,
                overlay,
                overlay.fingerprint(),
                f,
                bitness,
            )
            .conv
        }
        None => abi::conv(program, bitness),
    };
    let word = conv.word.unsigned_abs();
    Passing {
        regs: conv.args.to_vec(),
        first_stack: word.wrapping_add(conv.shadow.unsigned_abs()),
        word,
    }
}

/// The emulator's name of a general register.
///
/// # Arguments
///
/// * `r` - The register, any width.
fn register_name(r: Register) -> &'static str {
    match r.full_register() {
        Register::RAX => "rax",
        Register::RBX => "rbx",
        Register::RCX => "rcx",
        Register::RDX => "rdx",
        Register::RSI => "rsi",
        Register::RDI => "rdi",
        Register::RBP => "rbp",
        Register::RSP => "rsp",
        Register::R8 => "r8",
        Register::R9 => "r9",
        Register::R10 => "r10",
        Register::R11 => "r11",
        Register::R12 => "r12",
        Register::R13 => "r13",
        Register::R14 => "r14",
        _ => "r15",
    }
}

/// Writes the low `n` bytes of a value, little-endian.
///
/// # Arguments
///
/// * `emu` - The machine.
/// * `at` - The first address.
/// * `v` - The value.
/// * `n` - How many bytes, at most 8.
pub(super) fn poke_word(emu: &mut Emulator<'_>, at: u64, v: u64, n: u64) {
    for k in 0..n.min(8) {
        emu.poke(at.wrapping_add(k), crate::num::lo8(v >> (k * 8)));
    }
}

/// How a parameter's declared type reads, for typing an input.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Kind {
    /// An integer of this many bits, and whether it is signed.
    Int(u8, bool),
    /// A pointer.
    Pointer,
    /// A floating value.
    Float,
    /// A type this does not compute with.
    Other,
}

impl Kind {
    /// How a type reads.
    ///
    /// # Arguments
    ///
    /// * `ty` - The type.
    pub(super) fn of(ty: CTy) -> Self {
        if ty.is_ptr() {
            return Self::Pointer;
        }
        match ty.base {
            Base::Int(bits, signed) => Self::Int(bits, signed),
            Base::Float(_) => Self::Float,
            Base::Void | Base::Opaque | Base::Wide => Self::Other,
        }
    }
}

/// Reads one parameter of a signature: its type and its name.
///
/// # Arguments
///
/// * `toks` - The parameter's tokens.
/// * `word` - The machine word in bits.
fn parameter(toks: &[Tok], word: u8) -> Option<(String, CTy)> {
    let (name_at, name) = toks.iter().enumerate().rev().find_map(|(k, t)| match t {
        Tok::Name(n) => Some((k, n.clone())),
        _ => None,
    })?;
    let ty_toks = toks.get(..name_at)?;
    let ty = leading_type(ty_toks, word).map_or(CTy::int(word, false), |(t, used)| {
        let stars = ty_toks
            .get(used..)
            .unwrap_or(&[])
            .iter()
            .filter(|t| matches!(t, Tok::Punct("*" | "&")))
            .count();
        (0..stars).fold(t, |t, _| t.to())
    });
    Some((name, ty))
}

/// The signature a decompiled function's text prints.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Signature {
    /// The line as printed, after `// signature: `.
    pub(crate) text: String,
    /// The parameters in order, with their types.
    pub(super) params: Vec<(String, CTy)>,
    /// The return type, `None` for `void`.
    pub(super) ret: Option<CTy>,
    /// The machine word in bits.
    word: u8,
}

impl Signature {
    /// How the parameters read, in order.
    pub(crate) fn parameter_kinds(&self) -> Vec<Kind> {
        self.params.iter().map(|(_, ty)| Kind::of(*ty)).collect()
    }

    /// How the return type reads and its width, `None` for `void`.
    pub(crate) fn return_kind(&self) -> Option<(Kind, u8)> {
        let ty = self.ret?;
        Some((Kind::of(ty), ty.bits(self.word).unwrap_or(self.word)))
    }
}

/// The prototype the type library states for a function the binary itself
/// defines under a library name (a statically linked `strtok`, a DLL's own
/// export), when the code agrees with it.
///
/// The code agrees when it takes as many parameters as the declaration
/// lists, reads a variable list exactly when the declaration has one, and
/// returns a value exactly when the declaration does; the types then say
/// what the parameters and the result are where the code shows only their
/// widths.
///
/// # Arguments
///
/// * `name` - The function's name.
/// * `format` - The binary's format, which picks the platform's rows.
/// * `count` - How many parameters the code shows.
/// * `variadic` - Whether the code reads a variable list.
/// * `returns` - Whether the code returns a value.
///
/// # Returns
///
/// The return type and the parameter types, or `None` when the library
/// has no row for the name or the code disagrees with it.
pub(super) fn library_prototype(
    name: &str,
    format: crate::program::BinaryFormat,
    count: usize,
    variadic: bool,
    returns: bool,
) -> Option<(&'static str, Vec<&'static str>)> {
    let d = crate::analysis::typelib::declared(name, format)?;
    (d.params.len() == count && d.variadic == variadic && (d.ret != "void") == returns)
        .then(|| (d.ret, d.params.iter().map(|p| p.ty).collect()))
}

/// Reads the signature a decompiled function's text prints on its
/// `// signature:` line.
///
/// # Arguments
///
/// * `text` - The function's text, header first.
/// * `word` - The machine word in bits.
///
/// # Errors
///
/// When the text has no signature line, or it does not read.
pub(crate) fn printed(text: &str, word: u8) -> Result<Signature, String> {
    let line = text
        .lines()
        .take_while(|l| !l.trim().is_empty())
        .find_map(|l| l.trim().strip_prefix("// signature: "))
        .ok_or("the text has no signature line")?;
    let toks = tokens(line)?;
    let close = toks
        .iter()
        .rposition(|t| *t == Tok::Punct(")"))
        .ok_or("a signature without parameters")?;
    let open = (0..close)
        .rev()
        .find(|&k| closing(&toks, k) == Some(close))
        .ok_or("a signature without parameters")?;
    let lead = toks.get(..open).unwrap_or(&[]);
    let ret_toks = lead.get(..lead.len().saturating_sub(1)).unwrap_or(&[]);
    let ret = parameter(&[ret_toks, &[Tok::Name("r".to_owned())]].concat(), word)
        .map(|(_, ty)| ty)
        .filter(|ty| *ty != CTy::of(Base::Void));
    let mut params = Vec::new();
    for p in split_top(toks.get(open + 1..close).unwrap_or(&[]), ",") {
        if p.is_empty() || p == [Tok::Punct("...")] || p == [Tok::Name("void".to_owned())] {
            continue;
        }
        params.push(parameter(p, word).ok_or("a parameter that does not read")?);
    }
    Ok(Signature {
        text: line.to_owned(),
        params,
        ret,
        word,
    })
}
