//! Runtime helpers: the functions a compiler calls for an operation the
//! machine has no instruction for, and the C operator each one is.
//!
//! Their prototypes, and those of every other helper, are in
//! [`crate::analysis::runtime`].
//!
//! A 128-bit division on x86-64 or arm64 is a call to `__umodti3` and its
//! kin in libgcc or compiler-rt. Each 128-bit operand travels as two
//! registers, low half first, and the result comes back in the result
//! register pair. Printed as a call, the helper is a name a reader's
//! compiler does not declare, and its four 64-bit arguments are not the
//! two 128-bit ones it takes; printed as its operator on
//! `unsigned __int128`, it is the source the compiler lowered.

/// A runtime helper the catalog knows.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum Runtime {
    /// `__udivti3`: unsigned 128-bit division.
    Udivti3,
    /// `__umodti3`: unsigned 128-bit remainder.
    Umodti3,
    /// `__divti3`: signed 128-bit division.
    Divti3,
    /// `__modti3`: signed 128-bit remainder.
    Modti3,
    /// `__multi3`: 128-bit multiplication, the low 128 bits.
    Multi3,
}

impl Runtime {
    /// Returns the helper a callee name names.
    ///
    /// # Arguments
    ///
    /// * `name` - The callee's name as a call prints it.
    ///
    /// # Returns
    ///
    /// The helper, or `None` for any other name.
    pub(crate) fn named(name: &str) -> Option<Self> {
        match name {
            "__udivti3" => Some(Self::Udivti3),
            "__umodti3" => Some(Self::Umodti3),
            "__divti3" => Some(Self::Divti3),
            "__modti3" => Some(Self::Modti3),
            "__multi3" => Some(Self::Multi3),
            _ => None,
        }
    }

    /// Returns the C operator the helper computes and the 128-bit type it
    /// computes it in.
    fn operator(self) -> (&'static str, &'static str) {
        match self {
            Self::Udivti3 => ("/", "uint128_t"),
            Self::Umodti3 => ("%", "uint128_t"),
            Self::Divti3 => ("/", "int128_t"),
            Self::Modti3 => ("%", "int128_t"),
            Self::Multi3 => ("*", "uint128_t"),
        }
    }

    /// Returns the helper's call as its C operator over the 128-bit
    /// operands its argument registers carry.
    ///
    /// # Arguments
    ///
    /// * `args` - The arguments as the call passes them: each operand's
    ///   low half, then its high half.
    ///
    /// # Returns
    ///
    /// The expression, or `None` when the call does not pass two operands
    /// in four halves.
    pub(crate) fn lowered(self, args: &[String]) -> Option<String> {
        let [a_lo, a_hi, b_lo, b_hi] = args else {
            return None;
        };
        let (op, ty) = self.operator();
        let wide = |lo: &str, hi: &str| format!("((uint128_t)({hi}) << 64 | (uint64_t)({lo}))");
        Some(format!(
            "(({ty}){} {op} ({ty}){})",
            wide(a_lo, a_hi),
            wide(b_lo, b_hi)
        ))
    }
}

/// Returns the text of a call: the C operator of a runtime helper the
/// catalog knows ([`Runtime::lowered`]), else `callee(args)`.
///
/// # Arguments
///
/// * `callee` - The callee as the call prints it.
/// * `args` - The rendered arguments, in order.
pub(crate) fn call_text(callee: &str, args: &[String]) -> String {
    Runtime::named(callee)
        .and_then(|r| r.lowered(args))
        .unwrap_or_else(|| format!("{callee}({})", args.join(", ")))
}

#[cfg(test)]
mod tests {
    use super::{Runtime, call_text};

    /// `__umodti3` over the halves of two 128-bit operands prints as `%`
    /// on `unsigned __int128`, not as a call no compiler declares.
    ///
    /// # Panics
    ///
    /// When the call stays a call.
    #[test]
    fn a_128_bit_remainder_prints_as_its_operator() {
        let args = [
            "a".to_owned(),
            "b".to_owned(),
            "m".to_owned(),
            "0".to_owned(),
        ];
        assert_eq!(
            call_text("__umodti3", &args),
            "((uint128_t)((uint128_t)(b) << 64 | (uint64_t)(a)) % (uint128_t)((uint128_t)(0) << 64 | (uint64_t)(m)))"
        );
        assert_eq!(call_text("strlen", &args[..1]), "strlen(a)");
        assert_eq!(Runtime::Umodti3.lowered(&args[..2]), None);
        assert_eq!(
            crate::analysis::runtime::helper("__umodti3").map(|h| h.proto),
            Some("uint128_t __umodti3(uint128_t a, uint128_t b)"),
            "the prototype comes from the one runtime table"
        );
    }
}
