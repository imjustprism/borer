//! What a call the text makes hands back, read off the machine after the
//! callee ran.

use super::*;
use crate::analysis::decompile::abi::function::prototype;

/// Most argument positions a call passing a float is checked with: the
/// positions a float mask holds ([`float_mask`]).
const FLOAT_POSITIONS: usize = 8;

impl Running<'_, '_> {
    /// Returns a call's argument values as the words its callee takes, a
    /// floating one as its bits.
    ///
    /// A float is converted to the parameter type the callee's prototype
    /// states, as C converts an argument to a declared parameter
    /// (`INFINITY` handed to a `float` parameter is the single's bits). An
    /// integer is sign-extended from its own width when signed.
    ///
    /// # Arguments
    ///
    /// * `target` - The callee's entry.
    /// * `vals` - The evaluated arguments.
    ///
    /// # Returns
    ///
    /// The words, and a bit per position that is floating ([`float_mask`]).
    ///
    /// # Errors
    ///
    /// Unchecked for a float among more than [`FLOAT_POSITIONS`]
    /// arguments, or one handed to a parameter the prototype does not
    /// declare floating.
    pub(super) fn passed(&self, target: u64, vals: Vec<Val>) -> Eval<(Vec<u64>, u8)> {
        let floating = vals.iter().any(|v| v.ty.float().is_some());
        if floating && vals.len() > FLOAT_POSITIONS {
            return unchecked("a call passing a float among more than eight arguments");
        }
        let proto = floating
            .then(|| prototype(self.s.program, self.s.analysis, &Overlay::default(), target))
            .flatten();
        let mut out = Vec::with_capacity(vals.len());
        for (i, v) in vals.into_iter().enumerate() {
            let declared = proto.as_ref().and_then(|p| p.params.get(i)).copied();
            out.push(match (v.ty.float(), declared) {
                (None, _) => v,
                (Some(_), Some("float")) => self.convert(v, CTy::of(Base::Float(32)))?,
                (Some(_), Some("double")) => self.convert(v, CTy::of(Base::Float(64)))?,
                (Some(_), _) => {
                    return unchecked(
                        "a call passing a float to a parameter not declared floating",
                    );
                }
            });
        }
        let word = self.word();
        let floats = float_mask(out.iter().map(|v| v.ty.float().is_some()));
        let wide = |v: &Val| {
            if v.ty.signed() {
                sext(v.bits, v.ty.bits(word).unwrap_or(64))
            } else {
                v.bits
            }
        };
        Ok((out.iter().map(wide).collect(), floats))
    }
}

/// Returns what a call to a function hands back.
///
/// A callee whose result is floating ([`Function::ret_float`]) hands it
/// back in `xmm0` on a 64-bit target and in `st0` on a 32-bit one, which a
/// call from the text does not read; any other in `rax`, at the width
/// [`returned_bits`] reads.
///
/// # Arguments
///
/// * `analysis` - The functions.
/// * `target` - The callee's entry.
/// * `word` - The machine word in bits.
/// * `rax` - `rax` after the callee returned.
/// * `xmm0` - `xmm0` after the callee returned.
///
/// # Errors
///
/// Unchecked for a floating result on a 32-bit target.
///
/// [`Function::ret_float`]: crate::analysis::Function::ret_float
pub(super) fn returned(
    analysis: &Analysis,
    target: u64,
    word: u8,
    rax: u64,
    xmm0: u128,
) -> Eval<Val> {
    let float = analysis
        .function(target)
        .filter(|f| f.entry == target)
        .and_then(|f| f.ret_float);
    let (bits, ty) = match float {
        Some(_) if word != 64 => {
            return unchecked("a call whose floating result comes back in st0");
        }
        Some(fb) => (
            u64::try_from(xmm0 & u128::from(mask(fb))).unwrap_or(0),
            CTy::of(Base::Float(fb)),
        ),
        None => (
            rax,
            CTy::int(returned_bits(analysis, target).unwrap_or(word), false),
        ),
    };
    Ok(Val {
        bits: bits & mask(ty.bits(word).unwrap_or(64)),
        ty,
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
        Some(sig) => crate::analysis::decompile::lift::declared_bits(&sig.ret),
        None => f.ret_width?,
    };
    (bits <= 16).then_some(bits)
}
