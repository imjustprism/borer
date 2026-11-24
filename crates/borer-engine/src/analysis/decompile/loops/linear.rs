//! Values of the finished text as linear forms over unknown atoms, the one
//! evaluator the loop proofs share ([`Eval`]).

use super::super::ctext::{Ast, Base, Bin, CTy, Tok, Un, expression, leading_type, named_type};
use super::super::expr::{mask_bits, sext};
use super::super::finish::{decl_type, declares};
use super::super::interp::{names_in, pure};
use super::*;
use crate::analysis::protos::local_depth;

/// Reads one C expression of the text.
///
/// # Arguments
///
/// * `text` - The expression.
/// * `word` - The image's word in bits, the width of `size_t` in a cast.
///
/// # Returns
///
/// The expression, `None` when the text does not read as one.
pub(super) fn read(text: &str, word: u8) -> Option<Ast> {
    let toks = c_tokens(text).ok()?;
    expression(&toks, &|n| named_type(n, word).is_none(), word).ok()
}

/// How an atom's bits fill the width of the form it stands in.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum Fill {
    /// The atom is as wide as the form, or only its low bits count.
    Whole,
    /// Its bits are widened with zeros.
    Zero,
    /// Its bits are widened with copies of its top bit.
    Sign,
}

/// An unknown part of a value.
#[derive(Debug, Clone, PartialEq)]
pub(super) enum Atom {
    /// What an expression of the state before the assignments computes:
    /// it names no variable an assignment changed.
    Expr(Ast),
    /// The frame base, which `&local_N` is `N` below.
    Frame,
    /// A value the decision cannot name, equal only to itself.
    Fresh(usize),
}

/// One atom of a form, the bits of it that count and its coefficient.
#[derive(Debug, Clone, PartialEq)]
pub(super) struct Term {
    /// The atom.
    pub(super) atom: Atom,
    /// The low bits of the atom that count.
    pub(super) bits: u8,
    /// How those bits fill the form's width.
    pub(super) fill: Fill,
    /// The coefficient, modulo the form's width.
    pub(super) coef: u64,
}

/// A value modulo `2^w` as a sum of atoms with constant coefficients.
#[derive(Debug, Clone, PartialEq)]
pub(super) struct Lin {
    /// The atoms with their coefficients, none zero.
    pub(super) terms: Vec<Term>,
    /// The constant.
    pub(super) k: u64,
    /// The width in bits.
    pub(super) w: u8,
}

impl Lin {
    /// Returns a constant at width `w`.
    ///
    /// # Arguments
    ///
    /// * `k` - The constant.
    /// * `w` - The width.
    fn konst(k: u64, w: u8) -> Self {
        Self {
            terms: Vec::new(),
            k: k & mask_bits(w),
            w,
        }
    }

    /// Returns one atom at width `w`, whole.
    ///
    /// # Arguments
    ///
    /// * `atom` - The atom.
    /// * `w` - The width.
    fn one(atom: Atom, w: u8) -> Self {
        Self {
            terms: vec![Term {
                atom,
                bits: w,
                fill: Fill::Whole,
                coef: 1,
            }],
            k: 0,
            w,
        }
    }

    /// Returns the sum of two forms of one width.
    ///
    /// # Arguments
    ///
    /// * `o` - The other form.
    fn add(mut self, o: Self) -> Self {
        let m = mask_bits(self.w);
        self.k = self.k.wrapping_add(o.k) & m;
        for t in o.terms {
            match self
                .terms
                .iter_mut()
                .find(|u| u.atom == t.atom && u.bits == t.bits && u.fill == t.fill)
            {
                Some(u) => u.coef = u.coef.wrapping_add(t.coef) & m,
                None => self.terms.push(Term {
                    coef: t.coef & m,
                    ..t
                }),
            }
        }
        self.terms.retain(|t| t.coef != 0);
        self
    }

    /// Returns the form times a constant.
    ///
    /// # Arguments
    ///
    /// * `c` - The constant.
    fn scale(mut self, c: u64) -> Self {
        let m = mask_bits(self.w);
        self.k = self.k.wrapping_mul(c) & m;
        for t in &mut self.terms {
            t.coef = t.coef.wrapping_mul(c) & m;
        }
        self.terms.retain(|t| t.coef != 0);
        self
    }

    /// Returns the form's low `w` bits, a form of width `w`.
    ///
    /// # Arguments
    ///
    /// * `w` - The narrower width.
    fn truncate(mut self, w: u8) -> Self {
        let m = mask_bits(w);
        self.k &= m;
        for t in &mut self.terms {
            t.coef &= m;
            if t.bits >= w {
                t.bits = w;
                t.fill = Fill::Whole;
            }
        }
        self.terms.retain(|t| t.coef != 0);
        self.w = w;
        self
    }

    /// Tells whether two forms are the same sum, in any order of terms.
    ///
    /// # Arguments
    ///
    /// * `o` - The other form.
    pub(super) fn same(&self, o: &Self) -> bool {
        self.w == o.w
            && self.k == o.k
            && self.terms.len() == o.terms.len()
            && self.terms.iter().all(|t| o.terms.contains(t))
    }

    /// Returns the constant when the form has no atom.
    fn constant(&self) -> Option<u64> {
        self.terms.is_empty().then_some(self.k)
    }

    /// Returns the one atom whose being zero this form's being zero is.
    ///
    /// `c * X` is zero exactly when `X` is when `c`'s factor of two cannot
    /// carry a non-zero `X`, of the bits that count, past the width.
    ///
    /// # Returns
    ///
    /// The atom and the bits of it that count, `None` for any other form.
    fn zero_atom(&self) -> Option<(&Atom, u8)> {
        let [t] = self.terms.as_slice() else {
            return None;
        };
        let shift = u8::try_from(t.coef.trailing_zeros()).ok()?;
        (self.k == 0 && t.bits.checked_add(shift)? <= self.w).then_some((&t.atom, t.bits))
    }
}

/// A value as the decision knows it: a form and its C type.
#[derive(Debug, Clone)]
pub(super) struct Num {
    /// The form, at the type's width.
    pub(super) lin: Lin,
    /// The C type.
    pub(super) ty: CTy,
}

/// Which order a comparison reads its sides in.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum Order {
    /// As signed integers.
    Signed,
    /// As unsigned integers.
    Unsigned,
}

/// A test brought to a form two spellings of it share.
#[derive(Debug)]
pub(super) enum Pred {
    /// The form is not zero.
    NonZero(Lin),
    /// The form is zero.
    Zero(Lin),
    /// `<` or `<=` between two forms.
    Ordered(Bin, Order, Lin, Lin),
}

impl Pred {
    /// Tells whether two tests are proved to hold for exactly the same
    /// values; false means not proved.
    ///
    /// # Arguments
    ///
    /// * `o` - The other test.
    pub(super) fn same(&self, o: &Self) -> bool {
        match (self, o) {
            (Self::NonZero(x), Self::NonZero(y)) | (Self::Zero(x), Self::Zero(y)) => {
                match (x.zero_atom(), y.zero_atom()) {
                    (Some(s), Some(t)) => s == t,
                    _ => x.same(y) || x.same(&y.clone().scale(u64::MAX)),
                }
            }
            (Self::Ordered(p, s, x1, y1), Self::Ordered(q, t, x2, y2)) => {
                p == q && s == t && x1.same(x2) && y1.same(y2)
            }
            _ => false,
        }
    }

    /// Returns the test's truth when its forms are constants.
    fn truth(&self) -> Option<bool> {
        match self {
            Self::NonZero(d) => d.constant().map(|k| k != 0),
            Self::Zero(d) => d.constant().map(|k| k == 0),
            Self::Ordered(op, order, x, y) => {
                let key = |v: u64| match order {
                    Order::Signed => i128::from(sext(v, x.w).cast_signed()),
                    Order::Unsigned => i128::from(v),
                };
                let (p, q) = (key(x.constant()?), key(y.constant()?));
                Some(if *op == Bin::Lt { p < q } else { p <= q })
            }
        }
    }
}

/// What a function's declarations say, each read once.
#[derive(Debug, Default)]
pub(super) struct Declared {
    /// Each name looked up and the type its one declaration gives.
    types: Vec<(String, Option<CTy>)>,
    /// Each frame slot the text names and the bytes below the frame base
    /// it starts at, gathered at the first slot looked up.
    slots: Option<Vec<(String, i64)>>,
    /// The lines that declare: the function's own header or signature
    /// line and its local declarations, gathered at the first name looked
    /// up. A call, a test or a prototype names other things in
    /// parentheses.
    decls: Option<Vec<String>>,
}

/// The values a run of assignments leaves, as C computes them at the
/// widths the text states.
pub(super) struct Eval<'l> {
    /// The function's lines, for the declarations.
    lines: &'l [String],
    /// The machine word in bits.
    word: u8,
    /// The declarations looked up so far.
    declared: &'l mut Declared,
    /// Whether a read of memory is an atom, the same at every read: a
    /// guard and the test it guards read the same memory, while a value
    /// the entry rule decides on reads none.
    memory: bool,
    /// Each name assigned and its value, latest last; `None` is unknown.
    set: Vec<(String, Option<Num>)>,
    /// The fresh atoms made so far.
    fresh: usize,
}

impl<'l> Eval<'l> {
    /// Returns an evaluator with nothing assigned.
    ///
    /// # Arguments
    ///
    /// * `lines` - The function's lines, for the declarations.
    /// * `word` - The image's word in bits.
    /// * `declared` - The declarations looked up so far.
    /// * `memory` - Whether a read of memory is an atom.
    pub(super) fn new(
        lines: &'l [String],
        word: u8,
        declared: &'l mut Declared,
        memory: bool,
    ) -> Self {
        Self {
            lines,
            word,
            declared,
            memory,
            set: Vec::new(),
            fresh: 0,
        }
    }

    /// Runs one assignment chain, right to left as C does.
    ///
    /// # Arguments
    ///
    /// * `e` - The chain, `a = b = e`.
    ///
    /// # Returns
    ///
    /// The value the chain yields, `None` when unknown.
    pub(super) fn assign(&mut self, e: &Ast) -> Option<Num> {
        let Ast::Assign(None, target, value) = e else {
            return None;
        };
        let Ast::Name(name) = &**target else {
            return None;
        };
        let got = match &**value {
            Ast::Assign(..) => self.assign(value),
            v => self.value(v),
        };
        let stored = got
            .zip(self.type_of(name))
            .and_then(|(v, ty)| self.convert(v, ty));
        self.set.push((name.clone(), stored.clone()));
        stored
    }

    /// Returns the type a name holds: its declaration's, else a machine
    /// word for a register or a numbered variable.
    ///
    /// A frame slot is followed only when it is declared and no other slot
    /// the text names may share its bytes: a write to one would change the
    /// other.
    ///
    /// A register or numbered variable no line declares is an unsigned
    /// word because that is what the text means by it: the text's own
    /// interpreter reads such a name so, and every read of a narrower part
    /// is written as a cast. The exit form's widths and signedness are
    /// checked against that type, so the rewrite says nothing the text
    /// did not.
    ///
    /// # Arguments
    ///
    /// * `name` - The name.
    ///
    /// # Returns
    ///
    /// The type, or `None` for a name the decision does not follow: a
    /// global (memory another reader may change), a parameter or slot no
    /// line declares, a slot another overlaps, a type with no integer
    /// value.
    pub(super) fn type_of(&mut self, name: &str) -> Option<CTy> {
        let gpr = is_gpr(name);
        let var = vars::is_var_name(name);
        let slot = local_depth(name);
        if !gpr && !var && slot.is_none() && !is_param_name(name) {
            return None;
        }
        let ty = self.declared_type(name);
        if let Some(depth) = slot {
            let size = ty?.size(self.word)?;
            return self.alone(name, depth, size).then_some(ty).flatten();
        }
        ty.or_else(|| (gpr || var).then_some(CTy::int(self.word, false)))
    }

    /// Returns the integer or pointer type one declaration of a name gives
    /// ([`decl_type`] over the lines that declare).
    ///
    /// # Arguments
    ///
    /// * `name` - The name.
    ///
    /// # Returns
    ///
    /// The type, `None` when no single declaration gives one this reads.
    fn declared_type(&mut self, name: &str) -> Option<CTy> {
        if let Some((_, ty)) = self.declared.types.iter().find(|(n, _)| n == name) {
            return *ty;
        }
        let lines = self.lines;
        let decls = self.declared.decls.get_or_insert_with(|| {
            lines
                .iter()
                .enumerate()
                .filter(|(i, l)| {
                    let t = l.trim();
                    let header = indent_of(l) == 0
                        && !t.ends_with(';')
                        && lines.get(i + 1).is_some_and(|n| n.trim() == "{");
                    header
                        || t.starts_with("// signature:")
                        || declares(t) && !t.starts_with("extern ")
                })
                .map(|(_, l)| l.clone())
                .collect()
        });
        let ty = decl_type(decls, name).and_then(|text| {
            let toks = c_tokens(&text).ok()?;
            let (base, at) = leading_type(&toks, self.word)?;
            let ty = toks
                .get(at..)?
                .iter()
                .try_fold(base, |t, s| matches!(s, Tok::Punct("*")).then(|| t.to()))?;
            let known = matches!(ty.base, Base::Int(..) | Base::Void);
            known.then_some(ty).filter(|ty| self.bits(*ty).is_some())
        });
        self.declared.types.push((name.to_owned(), ty));
        ty
    }

    /// Tells whether no other frame slot the text names may share a
    /// slot's bytes.
    ///
    /// # Arguments
    ///
    /// * `name` - The slot's name.
    /// * `depth` - Bytes below the frame base it starts at.
    /// * `size` - Its size in bytes.
    fn alone(&mut self, name: &str, depth: i64, size: u64) -> bool {
        let lines = self.lines;
        let slots = self.declared.slots.get_or_insert_with(|| {
            let mut seen: Vec<(String, i64)> = lines
                .iter()
                .flat_map(|l| tokens(l))
                .filter_map(|w| Some((w.to_owned(), local_depth(w)?)))
                .collect();
            seen.sort_unstable();
            seen.dedup();
            seen
        });
        let others: Vec<(String, i64)> = slots.iter().filter(|(n, _)| n != name).cloned().collect();
        let end = depth.saturating_sub(i64::try_from(size).unwrap_or(i64::MAX));
        others.into_iter().all(|(other, d)| {
            let reach = self
                .declared_type(&other)
                .and_then(|ty| ty.size(self.word))
                .and_then(|s| i64::try_from(s).ok());
            d <= end || reach.is_some_and(|r| d.saturating_sub(r) >= depth)
        })
    }

    /// Returns the bits a value of an integer or pointer type holds.
    ///
    /// # Arguments
    ///
    /// * `ty` - The type.
    ///
    /// # Returns
    ///
    /// The width, `None` for a floating, vector, `void` or opaque value.
    pub(super) fn bits(&self, ty: CTy) -> Option<u8> {
        let scalar = matches!(ty.base, Base::Int(..)) || ty.is_ptr();
        scalar.then(|| ty.bits(self.word)).flatten()
    }

    /// Converts a value to a type, as an assignment or a cast does: a
    /// narrowing keeps the low bits, a widening fills a constant or a
    /// single atom by its sign and makes anything else a fresh atom, which
    /// keeps every form as small as the expression it came from.
    ///
    /// # Arguments
    ///
    /// * `n` - The value.
    /// * `to` - The type.
    ///
    /// # Returns
    ///
    /// The value at `to`, `None` when either type holds no integer.
    pub(super) fn convert(&mut self, n: Num, to: CTy) -> Option<Num> {
        let (from, w) = (self.bits(n.ty)?, self.bits(to)?);
        let fill = if n.ty.signed() {
            Fill::Sign
        } else {
            Fill::Zero
        };
        let lin = if w <= from {
            n.lin.truncate(w)
        } else if let Some(k) = n.lin.constant() {
            Lin::konst(if n.ty.signed() { sext(k, from) } else { k }, w)
        } else {
            let term = match n.lin.terms.as_slice() {
                [t] if t.coef == 1 && n.lin.k == 0 && t.fill == Fill::Whole => {
                    Term { fill, ..t.clone() }
                }
                _ => {
                    self.fresh += 1;
                    Term {
                        atom: Atom::Fresh(self.fresh),
                        bits: from,
                        fill,
                        coef: 1,
                    }
                }
            };
            Lin {
                terms: vec![term],
                k: 0,
                w,
            }
        };
        Some(Num { lin, ty: to })
    }

    /// Returns the type two integer operands meet at, as C's usual
    /// conversions say; a pointer meets as an unsigned word.
    ///
    /// # Arguments
    ///
    /// * `a` - One operand's type.
    /// * `b` - The other's.
    pub(super) fn common(&self, a: CTy, b: CTy) -> CTy {
        let int = |t: CTy| match (t.is_ptr(), t.base) {
            (false, Base::Int(bits, _)) if bits < 32 => (32, true),
            (false, Base::Int(bits, signed)) => (bits, signed),
            _ => (self.word, false),
        };
        let ((wa, sa), (wb, sb)) = (int(a), int(b));
        let (w, s) = match (sa, sb) {
            _ if sa == sb => (wa.max(wb), sa),
            (true, _) if wa > wb => (wa, true),
            (false, _) if wb > wa => (wb, true),
            _ => (wa.max(wb), false),
        };
        CTy::int(w, s)
    }

    /// Returns the value of an expression.
    ///
    /// A part the form cannot open, a product, a mask or (when
    /// [`Eval::memory`] holds) a read of memory, is an atom: the
    /// expression itself when it names no variable an assignment changed,
    /// else a fresh one.
    ///
    /// # Arguments
    ///
    /// * `e` - The expression.
    ///
    /// # Returns
    ///
    /// The value, `None` when the decision cannot follow it.
    pub(super) fn value(&mut self, e: &Ast) -> Option<Num> {
        match e {
            Ast::Int(v, ty) => Some(Num {
                lin: Lin::konst(*v, self.bits(*ty)?),
                ty: *ty,
            }),
            Ast::Name(n) => match self.set.iter().rev().find(|(m, _)| m == n) {
                Some((_, v)) => {
                    let v = v.clone();
                    v.filter(|_| self.type_of(n).is_some())
                }
                None => {
                    let ty = self.type_of(n)?;
                    Some(Num {
                        lin: Lin::one(Atom::Expr(e.clone()), self.bits(ty)?),
                        ty,
                    })
                }
            },
            Ast::Cast(ty, x) => {
                let n = self.value(x)?;
                self.convert(n, *ty)
            }
            Ast::Un(Un::Addr, x) => {
                let Ast::Name(n) = &**x else { return None };
                let depth = local_depth(n)?;
                let w = self.word;
                Some(Num {
                    lin: Lin::one(Atom::Frame, w)
                        .add(Lin::konst(depth.cast_unsigned().wrapping_neg(), w)),
                    ty: self.declared_type(n).unwrap_or(CTy::of(Base::Opaque)).to(),
                })
            }
            Ast::Un(op @ (Un::Neg | Un::Not), x) => {
                let n = self.value(x)?;
                let ty = (!n.ty.is_ptr()).then(|| self.common(n.ty, n.ty))?;
                let n = self.convert(n, ty)?;
                match (op, n.lin.constant()) {
                    (Un::Neg, _) => Some(Num {
                        lin: n.lin.scale(u64::MAX),
                        ty,
                    }),
                    (_, Some(k)) => Some(Num {
                        lin: Lin::konst(!k, n.lin.w),
                        ty,
                    }),
                    _ => self.atom(e, ty),
                }
            }
            Ast::Bin(op @ (Bin::Add | Bin::Sub), l, r) => self.sum(*op, l, r),
            Ast::Bin(op, l, r) if !op.compares() => self.product(*op, e, l, r),
            Ast::Un(Un::Deref, x) | Ast::Index(x, _) if self.memory && pure(e) => {
                let ty = self.value(x)?.ty.pointee()?;
                self.atom(e, ty)
            }
            Ast::Float(..)
            | Ast::Str(_)
            | Ast::Un(..)
            | Ast::Bin(..)
            | Ast::Logic(..)
            | Ast::Pick(..)
            | Ast::Call(..)
            | Ast::Index(..)
            | Ast::Arrow(..)
            | Ast::Assign(..)
            | Ast::Step(..) => None,
        }
    }

    /// Returns the value of an integer operator other than a sum: a
    /// multiple or a shift by a constant opens up, anything else is an atom.
    ///
    /// # Arguments
    ///
    /// * `op` - The operator.
    /// * `e` - The whole expression.
    /// * `l` - The left operand.
    /// * `r` - The right operand.
    ///
    /// # Returns
    ///
    /// The value, `None` when an operand is a pointer or unknown.
    fn product(&mut self, op: Bin, e: &Ast, l: &Ast, r: &Ast) -> Option<Num> {
        let (a, b) = (self.value(l)?, self.value(r)?);
        if a.ty.is_ptr() || b.ty.is_ptr() {
            return None;
        }
        let ty = match op {
            Bin::Shl | Bin::Shr => self.common(a.ty, a.ty),
            _ => self.common(a.ty, b.ty),
        };
        let w = self.bits(ty)?;
        let shift = b.lin.constant().filter(|n| *n < u64::from(w));
        let (a, b) = (self.convert(a, ty)?, self.convert(b, ty)?);
        let scaled = match (op, a.lin.constant(), b.lin.constant()) {
            (Bin::Mul, _, Some(c)) => Some(a.lin.scale(c)),
            (Bin::Mul, Some(c), _) => Some(b.lin.scale(c)),
            (Bin::Shl, _, _) => shift
                .and_then(|n| u32::try_from(n).ok())
                .and_then(|n| 1u64.checked_shl(n))
                .map(|c| a.lin.scale(c)),
            _ => None,
        };
        match scaled {
            Some(lin) => Some(Num { lin, ty }),
            None => self.atom(e, ty),
        }
    }

    /// Returns an atom of an expression's value at a type: the expression
    /// itself when it names no variable an assignment changed, else a
    /// fresh atom.
    ///
    /// # Arguments
    ///
    /// * `e` - The expression.
    /// * `ty` - Its type.
    ///
    /// # Returns
    ///
    /// The value, `None` when the type holds no integer.
    fn atom(&mut self, e: &Ast, ty: CTy) -> Option<Num> {
        let w = self.bits(ty)?;
        let mut names = Vec::new();
        names_in(e, &mut names);
        let changed = names.iter().any(|n| self.set.iter().any(|(m, _)| m == n));
        let atom = if changed {
            self.fresh += 1;
            Atom::Fresh(self.fresh)
        } else {
            Atom::Expr(e.clone())
        };
        Some(Num {
            lin: Lin::one(atom, w),
            ty,
        })
    }

    /// Returns the value of `l + r` or `l - r`.
    ///
    /// A pointer steps by its pointee, and a pointer with an unknown part
    /// (a name, the frame) only when that is one byte: before the parameter
    /// types settle the text may still count such a sum in bytes.
    ///
    /// # Arguments
    ///
    /// * `op` - [`Bin::Add`] or [`Bin::Sub`].
    /// * `l` - The left operand.
    /// * `r` - The right operand.
    ///
    /// # Returns
    ///
    /// The value, `None` when the decision cannot follow it.
    fn sum(&mut self, op: Bin, l: &Ast, r: &Ast) -> Option<Num> {
        let sub = op == Bin::Sub;
        let (a, b) = (self.value(l)?, self.value(r)?);
        let (a, b) = if b.ty.is_ptr() && !sub {
            (b, a)
        } else {
            (a, b)
        };
        if b.ty.is_ptr() {
            return None;
        }
        let (a, step, ty) = if a.ty.is_ptr() {
            let size = a.ty.pointee()?.size(self.word)?;
            if size != 1 && !a.lin.terms.is_empty() {
                return None;
            }
            let b = self.convert(b, CTy::int(self.word, true))?;
            (a.lin, b.lin.scale(size), a.ty)
        } else {
            let ty = self.common(a.ty, b.ty);
            (self.convert(a, ty)?.lin, self.convert(b, ty)?.lin, ty)
        };
        let step = if sub { step.scale(u64::MAX) } else { step };
        Some(Num {
            lin: a.add(step),
            ty,
        })
    }

    /// Returns a test's form ([`Pred`]): `a != b` as `a - b` not zero, `a >
    /// b` as `b < a`, an unsigned `0 < x` or `1 <= x` as `x` not zero, and
    /// a bare value as not zero.
    ///
    /// # Arguments
    ///
    /// * `e` - The test.
    ///
    /// # Returns
    ///
    /// The form, `None` when the test is not one this reads.
    pub(super) fn pred(&mut self, e: &Ast) -> Option<Pred> {
        match e {
            Ast::Bin(op, l, r) if op.compares() => {
                let (a, b) = (self.value(l)?, self.value(r)?);
                let ty = self.common(a.ty, b.ty);
                let (a, b) = (self.convert(a, ty)?.lin, self.convert(b, ty)?.lin);
                let (op, a, b) = match op {
                    Bin::Gt => (Bin::Lt, b, a),
                    Bin::Ge => (Bin::Le, b, a),
                    o => (*o, a, b),
                };
                let order = if ty.signed() {
                    Order::Signed
                } else {
                    Order::Unsigned
                };
                let low = |k: u64| order == Order::Unsigned && a.constant() == Some(k);
                Some(match op {
                    Bin::Ne => Pred::NonZero(a.add(b.scale(u64::MAX))),
                    Bin::Eq => Pred::Zero(a.add(b.scale(u64::MAX))),
                    Bin::Lt if low(0) => Pred::NonZero(b),
                    Bin::Le if low(1) => Pred::NonZero(b),
                    o => Pred::Ordered(o, order, a, b),
                })
            }
            Ast::Un(Un::LogNot, x) => match self.pred(x)? {
                Pred::NonZero(d) => Some(Pred::Zero(d)),
                Pred::Zero(d) => Some(Pred::NonZero(d)),
                Pred::Ordered(..) => None,
            },
            _ => {
                let n = self.value(e)?;
                let ty = self.common(n.ty, n.ty);
                Some(Pred::NonZero(self.convert(n, ty)?.lin))
            }
        }
    }

    /// Tells whether a condition is true.
    ///
    /// # Arguments
    ///
    /// * `e` - The condition.
    ///
    /// # Returns
    ///
    /// The truth, `None` when undecided.
    pub(super) fn truth(&mut self, e: &Ast) -> Option<bool> {
        match e {
            Ast::Logic(and, a, b) => match self.truth(a)? {
                t if t != *and => Some(t),
                _ => self.truth(b),
            },
            _ => self.pred(e)?.truth(),
        }
    }
}

/// Returns the subexpressions an expression is built of, in order.
///
/// # Arguments
///
/// * `e` - The expression.
pub(super) fn children(e: &Ast) -> Vec<&Ast> {
    match e {
        Ast::Int(..) | Ast::Float(..) | Ast::Str(_) | Ast::Name(_) => Vec::new(),
        Ast::Un(_, a) | Ast::Cast(_, a) | Ast::Arrow(a, _) | Ast::Step(_, _, a) => vec![a],
        Ast::Bin(_, a, b) | Ast::Logic(_, a, b) | Ast::Index(a, b) | Ast::Assign(_, a, b) => {
            vec![a, b]
        }
        Ast::Pick(c, m, o) => std::iter::once(&**c)
            .chain(m.as_deref())
            .chain(std::iter::once(&**o))
            .collect(),
        Ast::Call(f, args) => std::iter::once(&**f).chain(args).collect(),
    }
}

/// Collects the outermost reads of memory in an expression: each
/// dereference, index and field.
///
/// # Arguments
///
/// * `e` - The expression.
/// * `out` - The reads, in order.
pub(super) fn memory_reads<'e>(e: &'e Ast, out: &mut Vec<&'e Ast>) {
    if matches!(e, Ast::Un(Un::Deref, _) | Ast::Index(..) | Ast::Arrow(..)) {
        out.push(e);
        return;
    }
    for c in children(e) {
        memory_reads(c, out);
    }
}

/// Collects the reads of memory an expression makes on every path: not in
/// the right side of `&&` or `||`, nor in an arm of `?:`.
///
/// # Arguments
///
/// * `e` - The expression.
/// * `out` - The reads, outer before inner.
pub(super) fn always_reads<'e>(e: &'e Ast, out: &mut Vec<&'e Ast>) {
    if matches!(e, Ast::Un(Un::Deref, _) | Ast::Index(..) | Ast::Arrow(..)) {
        out.push(e);
    }
    match e {
        Ast::Logic(_, a, _) | Ast::Pick(a, ..) => always_reads(a, out),
        _ => {
            for c in children(e) {
                always_reads(c, out);
            }
        }
    }
}

/// Tells whether an expression divides anywhere, which traps on a zero
/// divisor.
///
/// # Arguments
///
/// * `e` - The expression.
pub(super) fn divides(e: &Ast) -> bool {
    matches!(e, Ast::Bin(Bin::Div | Bin::Rem, ..)) || children(e).into_iter().any(divides)
}

/// Tells whether a name is a general register of any target the lifters
/// read: x64's and x86's, arm32's `r0` to `r15`, arm64's `x0` to `x30`;
/// not a float, vector or temporary.
///
/// # Arguments
///
/// * `name` - The name.
pub(super) fn is_gpr(name: &str) -> bool {
    is_register_name(name) && !name.starts_with(['s', 'v', 't', 'x'])
        || numbered_register(name, 'r', 15)
        || numbered_register(name, 'x', 30)
}

/// Tells whether a name is the register `<letter><n>` for `n` up to `max`.
///
/// # Arguments
///
/// * `name` - The name.
/// * `letter` - The bank's letter.
/// * `max` - The highest number.
fn numbered_register(name: &str, letter: char, max: u8) -> bool {
    name.strip_prefix(letter)
        .filter(|d| !d.starts_with('0') || d.len() == 1)
        .and_then(|d| d.parse::<u8>().ok())
        .is_some_and(|n| n <= max)
}
