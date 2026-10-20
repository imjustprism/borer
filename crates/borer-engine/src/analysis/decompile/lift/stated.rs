//! What a declaration states of a callee.
//!
//! The prototype an agent stated for a function of the program
//! ([`Overlay::prototypes`](crate::analysis::Overlay::prototypes)), else
//! the type library's declaration of an import
//! ([`crate::analysis::typelib`]), say what the call hands back and, for
//! an import, what its constant arguments name.
//!
//! A call's shape is otherwise read from the code: the registers set before
//! it, the registers read after it. A declaration is a claim about the
//! callee instead, so where it rules out a result the code goes on to read,
//! the call says so ([`Call::contradicted`]) and the block it sits in makes
//! no claim of agreement with the binary.

use super::*;
use crate::analysis::typelib::{self, Decl, Pass};

/// What a declaration states a callee hands back.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(in crate::analysis::decompile) enum Returns {
    /// Nothing: a `void` function.
    Nothing,
    /// An integer or a pointer in the return register, of this many bits.
    Int(u8),
    /// A float in the float return register (`xmm0`, or `st0` on a 32-bit
    /// target), of this many bits.
    Float(u8),
}

impl Returns {
    /// Reads what a return type passes as.
    ///
    /// # Arguments
    ///
    /// * `pass` - The type's pass; `None` (a name the library does not
    ///   know) is a word in the return register.
    /// * `word` - The machine word in bits.
    pub(in crate::analysis::decompile) fn of(pass: Option<Pass>, word: u8) -> Self {
        match pass {
            Some(Pass::Void) => Self::Nothing,
            Some(Pass::Float(bits)) => Self::Float(bits),
            Some(p @ (Pass::Int { .. } | Pass::Pointer)) => Self::Int(p.bits(word)),
            None => Self::Int(word),
        }
    }

    /// Narrows what the code after a call reads to what the declaration
    /// lets it read.
    ///
    /// # Arguments
    ///
    /// * `rax` - The code reads the integer return register.
    /// * `float` - The code reads the float return register (and not the
    ///   integer one).
    ///
    /// # Returns
    ///
    /// `(rax is a result, the float register is a result, the code reads a
    /// register the declaration says holds no result)`.
    pub(in crate::analysis::decompile) fn filter(
        self,
        rax: bool,
        float: bool,
    ) -> (bool, bool, bool) {
        match self {
            Self::Nothing => (false, false, rax || float),
            Self::Int(_) => (rax, false, float),
            Self::Float(_) => (false, float, rax),
        }
    }
}

/// Returns the type library's declaration of the import a call reaches.
///
/// # Arguments
///
/// * `ctx` - The program and its analysis.
/// * `reached` - The callee's entry or the import slot the call goes
///   through.
///
/// # Returns
///
/// The declaration, or `None` when the call reaches no import the library
/// declares for the binary's platform.
pub(in crate::analysis::decompile) fn library_decl(
    ctx: &Ctx<'_>,
    reached: Option<u64>,
) -> Option<&'static Decl> {
    let names = import_names(ctx);
    let name = crate::analysis::bare_name(import_raw(ctx, &names, reached?)?);
    typelib::declared(name, ctx.program.format)
}

/// Reads a library declaration as the arity a call passes.
///
/// On a 64-bit target a parameter is one position, a float one in a vector
/// register; on a 32-bit target it is the stack words it takes (two for a
/// 64-bit integer or a `double`), popped by the callee when the
/// declaration's convention says so (`WINAPI` is `__stdcall`) and by the
/// caller for a `__cdecl` one: the C library, POSIX and every variadic
/// function.
///
/// # Arguments
///
/// * `decl` - The declaration.
/// * `bitness` - 32 or 64.
/// * `format` - The calling binary's format.
pub(in crate::analysis::decompile) fn library_prototype(
    decl: &Decl,
    bitness: u32,
    format: BinaryFormat,
) -> crate::analysis::prototypes::Prototype {
    let word = u8::try_from(bitness).unwrap_or(64);
    let passes: Vec<Option<Pass>> = decl
        .params
        .iter()
        .map(|p| typelib::pass_of(p.ty, word, format))
        .collect();
    let params = if bitness == 32 {
        passes.iter().map(|p| typelib::words32(*p)).sum()
    } else {
        passes.len()
    };
    let floats = passes
        .iter()
        .take(8)
        .enumerate()
        .filter(|(_, p)| matches!(p, Some(Pass::Float(_))))
        .fold(0u8, |m, (i, _)| m | (1 << i));
    crate::analysis::prototypes::Prototype {
        params: u8::try_from(params).unwrap_or(u8::MAX),
        this: false,
        callee_pops: decl.conv != typelib::Conv::Cdecl && !decl.variadic,
        hidden_return: false,
        variadic: decl.variadic,
        floats,
    }
}

/// Returns what a declaration states a callee hands back: the prototype
/// stated for the function the call enters, else the library's
/// declaration of the import it reaches.
///
/// # Arguments
///
/// * `ctx` - The program, its analysis and the overlay.
/// * `target` - The callee's entry when the call names a function.
/// * `reached` - The callee's entry or the import slot the call goes
///   through.
///
/// # Returns
///
/// What it hands back, or `None` when nothing declares the callee; a
/// compiler runtime helper ([`runtime_helper`]) is declared by its
/// prototype.
pub(in crate::analysis::decompile) fn stated_returns(
    ctx: &Ctx<'_>,
    target: Option<u64>,
    reached: Option<u64>,
) -> Option<Returns> {
    let word = u8::try_from(ctx.bitness).unwrap_or(64);
    if let Some(p) = target.and_then(|t| ctx.overlay.prototypes.get(&t)) {
        return Some(p.ret.as_ref().map_or(Returns::Nothing, |ty| {
            Returns::of(ty.pass(&ctx.overlay.types, word, ctx.program.format), word)
        }));
    }
    library_decl(ctx, reached)
        .map(|d| Returns::of(typelib::pass_of(d.ret, word, ctx.program.format), word))
        .or_else(|| {
            let h = runtime_helper(ctx, reached?)?;
            let (bits, float) = crate::analysis::runtime::returns(
                h,
                ctx.bitness,
                crate::analysis::runtime::microsoft(ctx.program.arch, ctx.program.format),
            )?;
            Some(if float {
                Returns::Float(bits)
            } else {
                Returns::Int(bits)
            })
        })
}

/// Reads a constant argument as the text renders it: decimal, `0x` hex, or
/// either negated (the two's complement of the magnitude).
///
/// # Arguments
///
/// * `text` - One rendered argument.
///
/// # Returns
///
/// The value, or `None` when the argument is not a bare number.
fn arg_value(text: &str) -> Option<u64> {
    let (negative, digits) = match text.strip_prefix('-') {
        Some(rest) => (true, rest),
        None => (false, text),
    };
    let v = match digits.strip_prefix("0x") {
        Some(hex) => u64::from_str_radix(hex, 16).ok()?,
        None if digits.bytes().all(|b| b.is_ascii_digit()) => digits.parse::<u64>().ok()?,
        None => return None,
    };
    Some(if negative { v.wrapping_neg() } else { v })
}

/// Spells a value read as a signed integer of `bits` as a negative number,
/// when it is one of small magnitude.
///
/// # Arguments
///
/// * `v` - The value.
/// * `bits` - The integer's width (8 to 64).
///
/// # Returns
///
/// `-N`, or `None` when the value is not negative at that width or its
/// magnitude passes `0xffff`, which reads better as hex.
fn negative(v: u64, bits: u8) -> Option<String> {
    /// The largest magnitude written as a negative number.
    const NEGATIVE_MAX: u64 = 0xffff;
    let mask = if bits >= 64 {
        u64::MAX
    } else {
        (1u64 << bits) - 1
    };
    let top = 1u64 << (bits.clamp(1, 64) - 1);
    let magnitude = v.wrapping_neg() & mask;
    (v & top != 0 && magnitude <= NEGATIVE_MAX).then(|| format!("-{magnitude}"))
}

impl Exec<'_, '_> {
    /// Notes the type a declared callee whose result the text binds
    /// returns (its stated prototype's, else the library's), when the type
    /// is as wide as the word and no float: the variable holding only such
    /// results is declared of it ([`Ctx::result_types`]).
    ///
    /// # Arguments
    ///
    /// * `target` - The callee's entry when the call names a function.
    /// * `reached` - The callee's entry or the import slot the call goes
    ///   through.
    /// * `callee` - The callee as the call renders it.
    pub(in crate::analysis::decompile) fn note_result_type(
        &mut self,
        target: Option<u64>,
        reached: Option<u64>,
        callee: &str,
    ) {
        let word = u8::try_from(self.ctx.bitness).unwrap_or(64);
        let format = self.ctx.program.format;
        let stated = target
            .and_then(|t| self.ctx.overlay.prototypes.get(&t))
            .map(|p| {
                p.ret
                    .as_ref()
                    .map(|ty| (ty.spell(), ty.pass(&self.ctx.overlay.types, word, format)))
            });
        if let Some((group, ret)) = library_decl(self.ctx, reached)
            .filter(|_| stated.is_none())
            .and_then(|d| Some((d.ret_group?, d.ret)))
        {
            let bits = typelib::pass_of(ret, word, format).map_or(word, |p| p.bits(word));
            self.ctx
                .result_groups
                .insert(callee.to_owned(), (group, bits.max(8)));
        }
        let declared = match stated {
            Some(ret) => ret,
            None => library_decl(self.ctx, reached)
                .map(|d| (d.ret.to_owned(), typelib::pass_of(d.ret, word, format))),
        };
        let Some((spelled, pass)) = declared else {
            return;
        };
        if pass.is_some_and(|p| p.bits(word) == word && !matches!(p, Pass::Float(_))) {
            self.ctx.result_types.insert(callee.to_owned(), spelled);
        }
    }

    /// Renders a call's constant arguments by what the callee's declaration
    /// says they are.
    ///
    /// A parameter that takes a constant group names its value by the group
    /// ([`typelib::render`]), at the width the parameter's type passes; a
    /// pointer parameter passed zero is `NULL`, and a signed one passed a
    /// small negative value at its width is that negative number (`-1` for
    /// an `int` set as `0xffffffff`). Only bare numbers change:
    /// an expression, a string or a named global stays as it was. The value
    /// the call is recorded with is the number, which is what the check
    /// against the binary compares; the name is its spelling.
    ///
    /// # Arguments
    ///
    /// * `reached` - The callee's entry or the import slot the call goes
    ///   through.
    /// * `args` - The rendered arguments, in order.
    pub(in crate::analysis::decompile) fn name_arguments(
        &self,
        reached: Option<u64>,
        args: &mut [String],
    ) {
        let Some(decl) = library_decl(self.ctx, reached) else {
            return;
        };
        let word = u8::try_from(self.ctx.bitness).unwrap_or(64);
        for (arg, param) in args.iter_mut().zip(&decl.params) {
            let Some(v) = arg_value(arg) else {
                continue;
            };
            let pass = typelib::pass_of(param.ty, word, self.ctx.program.format);
            let named = match (param.group.and_then(typelib::group), pass) {
                (Some(g), _) => typelib::render(g, v, pass.map_or(word, |p| p.bits(word)).max(8)),
                (None, Some(Pass::Pointer)) if v == 0 => Some("NULL".to_owned()),
                (None, Some(Pass::Int { bits, signed: true })) => negative(v, bits),
                (None, _) => None,
            };
            if let Some(text) = named {
                *arg = text;
            }
        }
    }
}

#[cfg(test)]
#[expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]
mod tests {
    use super::{Returns, arg_value, negative};
    use crate::analysis::typelib::Pass;

    /// Arguments read back as the renderer writes numbers; anything else
    /// is no constant.
    #[test]
    fn arguments_read_back_as_numbers() {
        assert_eq!(arg_value("3"), Some(3));
        assert_eq!(arg_value("0x80000000"), Some(0x8000_0000));
        assert_eq!(arg_value("-1"), Some(u64::MAX));
        assert_eq!(arg_value("-0x10"), Some(0u64.wrapping_sub(0x10)));
        assert_eq!(arg_value("rax"), None);
        assert_eq!(arg_value("L\"x\""), None);
        assert_eq!(arg_value("0x"), None);
    }

    /// A signed parameter's small negative value reads as negative at its
    /// width; a positive one, or a large magnitude, does not.
    #[test]
    fn signed_values_read_as_negative_at_their_width() {
        assert_eq!(negative(0xffff_ffff, 32).as_deref(), Some("-1"));
        assert_eq!(negative(u64::MAX, 32).as_deref(), Some("-1"));
        assert_eq!(negative(0xffff_fff6, 32).as_deref(), Some("-10"));
        assert_eq!(negative(0x7fff_ffff, 32), None);
        assert_eq!(negative(0x8000_0000, 32), None);
        assert_eq!(negative(u64::MAX, 64).as_deref(), Some("-1"));
        assert_eq!(negative(0xff, 8).as_deref(), Some("-1"));
    }

    /// A declared result narrows what the code reads, and says when the
    /// code reads a register the declaration rules out.
    #[test]
    fn a_declared_result_narrows_the_reads() {
        assert_eq!(Returns::of(Some(Pass::Void), 64), Returns::Nothing);
        assert_eq!(Returns::of(Some(Pass::Pointer), 32), Returns::Int(32));
        assert_eq!(Returns::of(None, 64), Returns::Int(64));
        assert_eq!(Returns::Nothing.filter(false, true), (false, false, true));
        assert_eq!(Returns::Nothing.filter(false, false), (false, false, false));
        assert_eq!(Returns::Int(32).filter(true, false), (true, false, false));
        assert_eq!(Returns::Int(32).filter(false, true), (false, false, true));
        assert_eq!(Returns::Float(64).filter(false, true), (false, true, false));
        assert_eq!(Returns::Float(64).filter(true, false), (false, false, true));
    }
}
