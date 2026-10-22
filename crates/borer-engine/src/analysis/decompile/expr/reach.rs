//! What a computed frame address may reach: the slots a read through it
//! may read, and whether it may land below its base.

use super::{Expr, Key, Op, known_bits, min_opt};

impl Expr {
    /// Tells whether the expression may read text variable `k`: it reads
    /// it, or, for a stack slot, reads through a computed frame address at
    /// or below the slot (`*(&local_14 + ebx * 4)` may read any slot from
    /// `local_14` up), which a write of the slot changes as well.
    ///
    /// # Arguments
    ///
    /// * `k` - The variable.
    pub(in crate::analysis::decompile) fn may_read(&self, k: Key) -> bool {
        self.mentions(k)
            || matches!(k, Key::Slot(o) if self.frame_read_base().is_some_and(|b| b <= o))
    }

    /// The lowest frame offset the expression reads through a computed
    /// address from: `k` for `*(&local + x)`, any offset when `x` may
    /// reach below it ([`Expr::reaches_below`]), never for a slot read
    /// whole.
    pub(super) fn frame_read_base(&self) -> Option<i64> {
        match self {
            Expr::Deref(a, _) => match **a {
                Expr::Sp(_) => None,
                _ => min_opt(
                    a.frame_address()
                        .map(|b| if a.reaches_below() { i64::MIN } else { b }),
                    a.frame_read_base(),
                ),
            },
            Expr::Const(_) | Expr::Str(_) | Expr::Sp(_) | Expr::Var(_) | Expr::FConst(..) => None,
            Expr::Bin(_, l, r) => min_opt(l.frame_read_base(), r.frame_read_base()),
            Expr::Un(_, e) | Expr::Sext(e, _) | Expr::Cast(e, _) | Expr::Bitcast(e, _) => {
                e.frame_read_base()
            }
            Expr::Call(_, args) | Expr::Helper(_, args) => {
                args.iter().filter_map(Expr::frame_read_base).min()
            }
            Expr::Cond(c) => c.frame_read_base(),
            Expr::Ternary(c, a, b) => min_opt(
                c.frame_read_base(),
                min_opt(a.frame_read_base(), b.frame_read_base()),
            ),
        }
    }

    /// The lowest frame offset the expression's value can point at, as an
    /// address: `k` for `&local_k + x`, never through a value loaded from
    /// memory.
    pub(super) fn frame_address(&self) -> Option<i64> {
        match self {
            Expr::Sp(k) => Some(*k),
            Expr::Bin(_, l, r) => min_opt(l.frame_address(), r.frame_address()),
            Expr::Un(_, e) | Expr::Sext(e, _) | Expr::Cast(e, _) | Expr::Bitcast(e, _) => {
                e.frame_address()
            }
            Expr::Ternary(_, a, b) => min_opt(a.frame_address(), b.frame_address()),
            Expr::Const(_)
            | Expr::Str(_)
            | Expr::Var(_)
            | Expr::FConst(..)
            | Expr::Deref(..)
            | Expr::Call(..)
            | Expr::Helper(..)
            | Expr::Cond(_) => None,
        }
    }

    /// Tells whether a frame address may land below its base: an index
    /// added to it is not provably small, so it may be negative
    /// (`&local_88 + (int64_t)a4 * 16`) or wrap the address space
    /// (`&local_418 + rcx * 8` for an `rcx` near `2^61`).
    ///
    /// An index whose bits are bounded below `2^31` (a byte loaded,
    /// masked, scaled by a constant) only reaches up from the base.
    pub(in crate::analysis::decompile) fn reaches_below(&self) -> bool {
        /// Largest index that cannot reach below a frame base.
        const SMALL: u64 = 1 << 31;
        /// An upper bound of `e`'s unsigned value, when one is known.
        fn bound(e: &Expr) -> u64 {
            match e {
                Expr::Bin(Op::Mul, l, r) => match (&**l, &**r) {
                    (x, Expr::Const(c)) | (Expr::Const(c), x) => bound(x).saturating_mul(*c),
                    _ => u64::MAX,
                },
                Expr::Bin(Op::Shl, x, s) => match **s {
                    Expr::Const(s) if s < 64 => bound(x).saturating_mul(1 << s),
                    _ => u64::MAX,
                },
                Expr::Bin(Op::Add, l, r) => bound(l).saturating_add(bound(r)),
                _ => known_bits(e),
            }
        }
        match self {
            Expr::Sp(_) => false,
            Expr::Bin(Op::Add, l, r) => match (l.frame_address(), r.frame_address()) {
                (Some(_), None) => l.reaches_below() || bound(r) > SMALL,
                (None, Some(_)) => r.reaches_below() || bound(l) > SMALL,
                _ => true,
            },
            _ => true,
        }
    }
}
