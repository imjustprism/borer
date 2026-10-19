//! Floating-point compare predicates: the sixteen answers an IEEE-754
//! compare of two values can be asked, NaN order included.
//!
//! A float compare is ordered (false when either value is NaN) or unordered
//! (true then), crossed with the relation it asks. Negating a predicate gives
//! another predicate of the set, never a different relation on the same
//! order: `!(a < b)` is "unordered or greater or equal", which C's `a >= b`
//! is not.

use crate::isa::x86::ConditionCode;

/// One of the sixteen float compare predicates of LLVM's `fcmp`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(super) enum FPred {
    /// Never holds.
    False,
    /// Ordered and equal.
    Oeq,
    /// Ordered and greater.
    Ogt,
    /// Ordered and greater or equal.
    Oge,
    /// Ordered and less.
    Olt,
    /// Ordered and less or equal.
    Ole,
    /// Ordered and not equal.
    One,
    /// Neither value is NaN.
    Ord,
    /// Unordered or equal.
    Ueq,
    /// Unordered or greater.
    Ugt,
    /// Unordered or greater or equal.
    Uge,
    /// Unordered or less.
    Ult,
    /// Unordered or less or equal.
    Ule,
    /// Unordered or not equal.
    Une,
    /// Either value is NaN.
    Uno,
    /// Always holds.
    True,
}

impl FPred {
    /// Every predicate, in declaration order: a predicate's position here is
    /// its code in a packed lift.
    pub(super) const ALL: [FPred; 16] = [
        FPred::False,
        FPred::Oeq,
        FPred::Ogt,
        FPred::Oge,
        FPred::Olt,
        FPred::Ole,
        FPred::One,
        FPred::Ord,
        FPred::Ueq,
        FPred::Ugt,
        FPred::Uge,
        FPred::Ult,
        FPred::Ule,
        FPred::Une,
        FPred::Uno,
        FPred::True,
    ];

    /// Returns the predicate that holds exactly where this one does not.
    pub(super) fn negate(self) -> FPred {
        match self {
            FPred::False => FPred::True,
            FPred::Oeq => FPred::Une,
            FPred::Ogt => FPred::Ule,
            FPred::Oge => FPred::Ult,
            FPred::Olt => FPred::Uge,
            FPred::Ole => FPred::Ugt,
            FPred::One => FPred::Ueq,
            FPred::Ord => FPred::Uno,
            FPred::Ueq => FPred::One,
            FPred::Ugt => FPred::Ole,
            FPred::Uge => FPred::Olt,
            FPred::Ult => FPred::Oge,
            FPred::Ule => FPred::Ogt,
            FPred::Une => FPred::Oeq,
            FPred::Uno => FPred::Ord,
            FPred::True => FPred::False,
        }
    }

    /// Tells whether the predicate holds for two values.
    ///
    /// # Arguments
    ///
    /// * `a` - The left value.
    /// * `b` - The right value.
    pub(super) fn holds(self, a: f64, b: f64) -> bool {
        let unordered = a.is_nan() || b.is_nan();
        let ordered = |rel: bool| !unordered && rel;
        let either = |rel: bool| unordered || rel;
        match self {
            FPred::False => false,
            FPred::Oeq => ordered(a == b),
            FPred::Ogt => ordered(a > b),
            FPred::Oge => ordered(a >= b),
            FPred::Olt => ordered(a < b),
            FPred::Ole => ordered(a <= b),
            FPred::One => ordered(a != b),
            FPred::Ord => !unordered,
            FPred::Ueq => either(a == b),
            FPred::Ugt => either(a > b),
            FPred::Uge => either(a >= b),
            FPred::Ult => either(a < b),
            FPred::Ule => either(a <= b),
            FPred::Une => either(a != b),
            FPred::Uno => unordered,
            FPred::True => true,
        }
    }

    /// Returns the predicate that holds on a set of compare outcomes.
    ///
    /// # Arguments
    ///
    /// * `set` - The outcomes, one bit each: greater 1, less 2, equal 4,
    ///   unordered 8; higher bits are ignored.
    pub(super) fn of_outcomes(set: u8) -> FPred {
        match set & 0xf {
            0 => FPred::False,
            1 => FPred::Ogt,
            2 => FPred::Olt,
            3 => FPred::One,
            4 => FPred::Oeq,
            5 => FPred::Oge,
            6 => FPred::Ole,
            7 => FPred::Ord,
            8 => FPred::Uno,
            9 => FPred::Ugt,
            10 => FPred::Ult,
            11 => FPred::Une,
            12 => FPred::Ueq,
            13 => FPred::Uge,
            14 => FPred::Ule,
            15.. => FPred::True,
        }
    }

    /// Returns the predicate an x86 condition code asks after `comiss`,
    /// `ucomisd` or `fcomi`.
    ///
    /// Those set ZF, PF and CF all three on an unordered pair, so `a` and
    /// `ae` are ordered, `b` and `be` unordered, `e` holds on a NaN and `ne`
    /// does not.
    ///
    /// # Arguments
    ///
    /// * `cc` - The condition code.
    ///
    /// # Returns
    ///
    /// The predicate, or `None` for a code a float compare does not decide.
    pub(super) fn of_flags(cc: ConditionCode) -> Option<FPred> {
        use ConditionCode as C;
        Some(match cc {
            C::a => FPred::Ogt,
            C::ae => FPred::Oge,
            C::b => FPred::Ult,
            C::be => FPred::Ule,
            C::e => FPred::Ueq,
            C::ne => FPred::One,
            C::p => FPred::Uno,
            C::np => FPred::Ord,
            C::None | C::s | C::ns | C::o | C::no | C::l | C::ge | C::le | C::g => return None,
        })
    }

    /// Returns the C operator that asks this predicate, when one does.
    ///
    /// C's relational operators are ordered and its `!=` unordered, so the
    /// four ordered relations, `oeq` and `une` have one, and the predicates
    /// they negate are spelled as that negation.
    ///
    /// # Returns
    ///
    /// The operator and whether it stands negated, or `None` for `one`,
    /// `ueq`, `ord`, `uno`, `true` and `false`.
    pub(super) fn operator(self) -> Option<(&'static str, bool)> {
        Some(match self {
            FPred::Oeq => ("==", false),
            FPred::Une => ("!=", false),
            FPred::Ogt => (">", false),
            FPred::Oge => (">=", false),
            FPred::Olt => ("<", false),
            FPred::Ole => ("<=", false),
            FPred::Ule => (">", true),
            FPred::Ult => (">=", true),
            FPred::Uge => ("<", true),
            FPred::Ugt => ("<=", true),
            FPred::False | FPred::One | FPred::Ord | FPred::Ueq | FPred::Uno | FPred::True => {
                return None;
            }
        })
    }
}

#[cfg(test)]
mod tests {
    use super::FPred;
    use crate::isa::x86::ConditionCode;

    /// Pairs that cover less, equal, greater and unordered.
    const PAIRS: [(f64, f64); 5] = [
        (1.0, 2.0),
        (2.0, 2.0),
        (3.0, 2.0),
        (f64::NAN, 2.0),
        (1.0, f64::NAN),
    ];

    /// A negated predicate holds exactly where the predicate does not.
    #[test]
    #[expect(
        clippy::missing_panics_doc,
        reason = "assertions are the point of a test"
    )]
    fn negation_is_closed_and_exact() {
        for p in FPred::ALL {
            assert_eq!(p.negate().negate(), p);
            for (a, b) in PAIRS {
                assert_eq!(p.negate().holds(a, b), !p.holds(a, b), "{p:?} {a} {b}");
            }
        }
    }

    /// The predicate of an outcome set holds on exactly those outcomes.
    #[test]
    #[expect(
        clippy::missing_panics_doc,
        reason = "assertions are the point of a test"
    )]
    fn outcome_sets_name_the_predicate_holding_on_them() {
        let outcomes = [(3.0, 2.0), (1.0, 2.0), (2.0, 2.0), (f64::NAN, 2.0)];
        for set in 0..16u8 {
            let p = FPred::of_outcomes(set);
            for (bit, (a, b)) in outcomes.iter().enumerate() {
                assert_eq!(p.holds(*a, *b), set >> bit & 1 == 1, "{set} {p:?}");
            }
        }
    }

    /// The inverse of a flag code asks the negated predicate.
    #[test]
    #[expect(
        clippy::missing_panics_doc,
        reason = "assertions are the point of a test"
    )]
    fn flag_codes_agree_with_their_inverse() {
        use ConditionCode as C;
        let pairs = [(C::a, C::be), (C::ae, C::b), (C::e, C::ne), (C::p, C::np)];
        for (c, inv) in pairs {
            let p = FPred::of_flags(c).unwrap();
            assert_eq!(FPred::of_flags(inv), Some(p.negate()));
        }
    }

    /// The C operator of a predicate evaluates as the predicate.
    #[test]
    #[expect(
        clippy::missing_panics_doc,
        reason = "assertions are the point of a test"
    )]
    fn operators_spell_the_predicate_c_evaluates() {
        for p in FPred::ALL {
            let Some((op, negated)) = p.operator() else {
                continue;
            };
            for (a, b) in PAIRS {
                let c = match op {
                    "==" => a == b,
                    "!=" => a != b,
                    ">" => a > b,
                    ">=" => a >= b,
                    "<" => a < b,
                    _ => a <= b,
                };
                assert_eq!(c != negated, p.holds(a, b), "{p:?} {a} {b}");
            }
        }
    }
}
