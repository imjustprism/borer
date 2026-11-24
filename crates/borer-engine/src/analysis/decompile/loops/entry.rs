//! A rotated loop whose first test the values set right before it decide
//! ([`decided_do`]).

use super::super::ctext::{Ast, Base, Bin, CTy, Tok, Un, expression, leading_type, named_type};
use super::super::expr::{mask_bits, sext};
use super::super::finish::{decl_type, declares};
use super::super::interp::pure;
use super::*;
use crate::analysis::protos::local_depth;

/// Most plain assignments in front of a `do` the decision reads.
const RUN_MAX: usize = 16;

/// Writes each `do` of a function whose first test is true on entry as a
/// `while` or a `for` ([`decided_do`]).
///
/// It runs right after the registers are split into variables
/// ([`super::super::vars::split_webs`]), which reads a `do` as a loop that
/// runs at least once: a `while` before the split would leave it a path
/// past the loop that the entry values rule out, and a copy to carry a
/// value along it. The declarations it adds give the decision its widths.
///
/// # Arguments
///
/// * `text` - A decompiled function, header lines first.
/// * `word` - The image's word in bits (32 or 64): the width of a pointer
///   and of a register no line declares.
///
/// # Returns
///
/// The text with those loops rewritten.
pub(in crate::analysis::decompile) fn decided_loops(text: String, word: u8) -> String {
    if !text.contains("do {") {
        return text;
    }
    let mut lines: Vec<String> = text.lines().map(str::to_owned).collect();
    let mut declared = Declared::default();
    let mut changed = false;
    let mut k = 0;
    while k < lines.len() {
        changed |= decided_do(&mut lines, k, word, &mut declared);
        k += 1;
    }
    if !changed {
        return text;
    }
    let mut out = lines.join("\n");
    out.push('\n');
    out
}

/// Rewrites the `do` that opens on line `k + 1` as a `while` or a `for`
/// when its first test is true on entry.
///
/// `do { B } while (C);` is `while (C) { B }` when the values the lines in
/// front of it set make `C` true, and `for (v = e; C; step) { B' }` when
/// line `k` is that `v = e;` and `B` ends with `v`'s step ([`step`]).
///
/// `do { B } while (C);` and `while (C) { B }` run the same statements
/// exactly when `C` holds the first time: the guard the compiler left out
/// because it knew. The lines in front are the plain assignments to names
/// directly above the `do` at its level, up to a call, a store, a label or
/// a block; [`decided`] puts their values into `C` and keeps the loop when
/// the result is not proven true. No rewrite takes a loop that holds a
/// label or an empty one, which [`spin`] reads.
///
/// # Arguments
///
/// * `lines` - The body lines.
/// * `k` - The line before the `do {`.
/// * `word` - The image's word in bits.
/// * `declared` - The declarations looked up so far, which no rewrite
///   here changes.
///
/// # Returns
///
/// Whether the `do` became a `while` or a `for`.
fn decided_do(lines: &mut Vec<String>, k: usize, word: u8, declared: &mut Declared) -> bool {
    let Some(open) = lines.get(k + 1).filter(|l| l.trim() == "do {") else {
        return false;
    };
    let pad = indent_of(open);
    let Some(latch) = closing(lines, k + 1, pad) else {
        return false;
    };
    let Some(cond) = lines
        .get(latch)
        .and_then(|l| l.trim().strip_prefix("} while (")?.strip_suffix(");"))
        .map(str::to_owned)
    else {
        return false;
    };
    let body = lines.get(k + 2..latch).unwrap_or(&[]);
    if body.is_empty() || body.iter().any(|l| is_label(l)) {
        return false;
    }
    let mut steps: Vec<Ast> = (0..=k)
        .rev()
        .take(RUN_MAX)
        .map_while(|j| {
            lines
                .get(j)
                .filter(|l| indent_of(l) == pad && !impure(l))
                .and_then(|l| assignment(l, word))
        })
        .collect();
    steps.reverse();
    let run = lines.get(k + 1 - steps.len()..=k).unwrap_or(&[]);
    if !decided(lines, &steps, &cond, word, declared) {
        return false;
    }
    let pad_s = " ".repeat(pad);
    let close = format!("{pad_s}}}");
    let counted = run
        .last()
        .and_then(|l| plain_assignment(l))
        .filter(|(v, _)| mentions_ident(&cond, v))
        .and_then(|(v, value)| Some((v, value, step(body, pad, v)?)));
    let (at, rewritten): (usize, Vec<String>) = match counted {
        Some((v, value, (idx, step))) => {
            let step = step
                .strip_prefix(&format!("{v} = {v} + "))
                .filter(|inc| parse_const(inc).is_some())
                .map_or(step.clone(), |inc| format!("{v} += {inc}"));
            let head = format!("{pad_s}for ({v} = {value}; {cond}; {step}) {{");
            let kept = body
                .iter()
                .enumerate()
                .filter(|&(i, _)| i != idx)
                .map(|(_, l)| l.clone());
            let out = std::iter::once(head)
                .chain(kept)
                .chain(std::iter::once(close))
                .collect();
            (k, out)
        }
        None => {
            let out = std::iter::once(format!("{pad_s}while ({cond}) {{"))
                .chain(body.iter().cloned())
                .chain(std::iter::once(close))
                .collect();
            (k + 1, out)
        }
    };
    lines.splice(at..=latch, rewritten);
    true
}

/// Returns the step a `for` header takes from a loop body.
///
/// That is its last line ([`step_of`]), or a constant step of `v` just
/// before a last plain assignment that does not read `v`, which may run
/// after it: `v` is then a register or a numbered variable, which no
/// address reaches, so the last line cannot read it through memory either.
///
/// # Arguments
///
/// * `body` - The loop body's lines.
/// * `pad` - The indentation of the loop's opener.
/// * `v` - The loop variable.
///
/// # Returns
///
/// The step's line in `body` and its text; `None` when the body ends with
/// no such step or continues at its own level.
pub(super) fn step(body: &[String], pad: usize, v: &str) -> Option<(usize, String)> {
    if let Some(step) = step_of(body, pad + 2, v) {
        return Some((body.len() - 1, step.to_owned()));
    }
    let at = body.len().checked_sub(2)?;
    let (line, tail) = (body.get(at)?, body.last()?);
    let tail_lhs = plain_assignment(tail)
        .or_else(|| tail.trim().strip_suffix(';')?.split_once(" += "))
        .map(|(lhs, _)| lhs);
    let apart = indent_of(line) == pad + 2
        && indent_of(tail) == pad + 2
        && !mentions_ident(tail, v)
        && !impure(tail)
        && tail_lhs.is_some_and(|lhs| is_register_name(lhs) || vars::is_var_name(lhs))
        && (is_register_name(v) || vars::is_var_name(v))
        && !continues_at_top(body);
    let s = line.trim().strip_suffix(';').filter(|_| apart)?;
    let inc = s
        .strip_prefix(&format!("{v} += "))
        .or_else(|| s.strip_prefix(&format!("{v} = {v} + ")))
        .filter(|inc| parse_const(inc).is_some_and(|c| c > 0))?;
    Some((at, format!("{v} += {inc}")))
}

/// Reads a line as a chain of plain assignments to names of one pure
/// value, `a = b = e;`.
///
/// # Arguments
///
/// * `line` - The line.
/// * `word` - The machine word in bits, the width of `size_t` in a cast.
///
/// # Returns
///
/// The assignment, or `None` for any other line.
fn assignment(line: &str, word: u8) -> Option<Ast> {
    /// Tells whether `e` is a chain of `=` to names ending in a pure value.
    fn chain(e: &Ast) -> bool {
        match e {
            Ast::Assign(None, t, v) => matches!(**t, Ast::Name(_)) && (chain(v) || pure(v)),
            _ => false,
        }
    }
    let toks = c_tokens(line.trim().strip_suffix(';')?).ok()?;
    let e = expression(&toks, &|n| named_type(n, word).is_none(), word).ok()?;
    chain(&e).then_some(e)
}

/// Tells whether a loop's test is true on entry, after the assignments in
/// front of it ran.
///
/// Each value is followed as C computes it at the widths the text states
/// ([`Entry`]); a name nothing in front sets stands for what it held, the
/// same at every read. The test is decided when it compares two integer
/// constants, or one such name or the frame base plus two offsets that
/// differ (or agree) at the compared width, and nothing narrowed either
/// side below it. Anything else is undecided: nothing is sampled.
///
/// # Arguments
///
/// * `lines` - The function's lines, for the declarations.
/// * `steps` - The assignments in front of the loop, in order
///   ([`assignment`]).
/// * `cond` - The loop's test.
/// * `word` - The image's word in bits.
/// * `declared` - The declarations looked up so far ([`decided_do`]).
fn decided(lines: &[String], steps: &[Ast], cond: &str, word: u8, declared: &mut Declared) -> bool {
    let Some(test) = c_tokens(cond)
        .ok()
        .and_then(|t| expression(&t, &|n| named_type(n, word).is_none(), word).ok())
    else {
        return false;
    };
    let mut entry = Entry {
        lines,
        word,
        declared,
        set: Vec::new(),
    };
    for step in steps {
        entry.assign(step);
    }
    entry.truth(&test) == Some(true)
}

/// The unknown part of a value.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Root<'a> {
    /// None: the value is its offset.
    Lit,
    /// What a name held before the assignments ran.
    Name(&'a str),
    /// The frame base, which `&local_N` is `N` below.
    Frame,
}

/// A value as the decision knows it: a root plus a constant.
#[derive(Debug, Clone, Copy)]
struct Num<'a> {
    /// The unknown part.
    root: Root<'a>,
    /// The constant, within the type's width.
    off: u64,
    /// The C type.
    ty: CTy,
    /// The low bits in which the value is the root plus the offset; a
    /// narrowing on the way drops the rest.
    exact: u8,
}

/// What a function's declarations say, each read once.
#[derive(Debug, Default)]
struct Declared {
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

/// The values the assignments in front of a loop leave.
struct Entry<'a, 'l> {
    /// The function's lines, for the declarations.
    lines: &'l [String],
    /// The machine word in bits.
    word: u8,
    /// The declarations looked up so far.
    declared: &'l mut Declared,
    /// Each name assigned and its value, latest last; `None` is unknown.
    set: Vec<(&'a str, Option<Num<'a>>)>,
}

impl<'a> Entry<'a, '_> {
    /// Runs one assignment chain, right to left as C does.
    ///
    /// # Arguments
    ///
    /// * `e` - The chain ([`assignment`]).
    ///
    /// # Returns
    ///
    /// The value the chain yields, `None` when unknown.
    fn assign(&mut self, e: &'a Ast) -> Option<Num<'a>> {
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
        self.set.push((name.as_str(), stored));
        stored
    }

    /// Returns the type a name holds: its declaration's, else a machine
    /// word for a register or a numbered variable.
    ///
    /// A frame slot is followed only when it is declared and no other slot
    /// the text names may share its bytes: a write to one would change the
    /// other.
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
    fn type_of(&mut self, name: &str) -> Option<CTy> {
        let gpr = is_register_name(name) && !name.starts_with(['s', 'v', 't', 'x'])
            || numbered_register(name, 'r', 15)
            || numbered_register(name, 'x', 30);
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
    fn bits(&self, ty: CTy) -> Option<u8> {
        let scalar = matches!(ty.base, Base::Int(..)) || ty.is_ptr();
        scalar.then(|| ty.bits(self.word)).flatten()
    }

    /// Converts a value to a type, as an assignment or a cast does.
    ///
    /// # Arguments
    ///
    /// * `n` - The value.
    /// * `to` - The type.
    ///
    /// # Returns
    ///
    /// The value at `to`, `None` when either type holds no integer.
    fn convert(&self, n: Num<'a>, to: CTy) -> Option<Num<'a>> {
        let (from, w) = (self.bits(n.ty)?, self.bits(to)?);
        let off = if n.root == Root::Lit && w > from && n.ty.signed() {
            sext(n.off, from)
        } else {
            n.off
        };
        Some(Num {
            off: off & mask_bits(w),
            ty: to,
            exact: n.exact.min(w),
            ..n
        })
    }

    /// Returns the type two integer operands meet at, as C's usual
    /// conversions say; a pointer meets as an unsigned word.
    ///
    /// # Arguments
    ///
    /// * `a` - One operand's type.
    /// * `b` - The other's.
    fn common(&self, a: CTy, b: CTy) -> CTy {
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
    /// # Arguments
    ///
    /// * `e` - The expression.
    ///
    /// # Returns
    ///
    /// The value, `None` when the decision cannot follow it.
    fn value(&mut self, e: &'a Ast) -> Option<Num<'a>> {
        match e {
            Ast::Int(v, ty) => {
                let w = self.bits(*ty)?;
                Some(Num {
                    root: Root::Lit,
                    off: v & mask_bits(w),
                    ty: *ty,
                    exact: w,
                })
            }
            Ast::Name(n) => match self.set.iter().rev().find(|(m, _)| m == n).map(|&(_, v)| v) {
                Some(v) => v.filter(|_| self.type_of(n).is_some()),
                None => {
                    let ty = self.type_of(n)?;
                    Some(Num {
                        root: Root::Name(n.as_str()),
                        off: 0,
                        ty,
                        exact: self.bits(ty)?,
                    })
                }
            },
            Ast::Cast(ty, x) => {
                let n = self.value(x)?;
                self.convert(n, *ty)
            }
            Ast::Un(Un::Addr, x) => {
                let Ast::Name(n) = &**x else { return None };
                Some(Num {
                    root: Root::Frame,
                    off: local_depth(n)?.cast_unsigned().wrapping_neg() & mask_bits(self.word),
                    ty: self.declared_type(n).unwrap_or(CTy::of(Base::Opaque)).to(),
                    exact: self.word,
                })
            }
            Ast::Un(Un::Neg, x) => {
                let n = self.value(x)?;
                let ty = self.common(n.ty, n.ty);
                let n = self.convert(n, ty).filter(|n| n.root == Root::Lit)?;
                let w = self.bits(ty)?;
                Some(Num {
                    off: n.off.wrapping_neg() & mask_bits(w),
                    ..n
                })
            }
            Ast::Bin(op @ (Bin::Add | Bin::Sub), l, r) => self.sum(*op, l, r),
            _ => None,
        }
    }

    /// Returns the value of `l + r` or `l - r`, of which at most the left
    /// side, or either side of a sum, has a root.
    ///
    /// A pointer a name holds, or a frame slot's address, steps by its
    /// pointee only when that is one byte: before the parameter types
    /// settle the text may still count such a sum in bytes.
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
    fn sum(&mut self, op: Bin, l: &'a Ast, r: &'a Ast) -> Option<Num<'a>> {
        let sub = op == Bin::Sub;
        let (a, b) = (self.value(l)?, self.value(r)?);
        let (a, b) = if b.root != Root::Lit && !sub {
            (b, a)
        } else {
            (a, b)
        };
        if b.root != Root::Lit || b.ty.is_ptr() {
            return None;
        }
        let (a, step, ty) = if a.ty.is_ptr() {
            let size = a.ty.pointee()?.size(self.word)?;
            if size != 1 && matches!(a.root, Root::Name(_) | Root::Frame) {
                return None;
            }
            let b = self.convert(b, CTy::int(self.word, true))?;
            (a, b.off.wrapping_mul(size), a.ty)
        } else {
            let ty = self.common(a.ty, b.ty);
            (self.convert(a, ty)?, self.convert(b, ty)?.off, ty)
        };
        let step = if sub { step.wrapping_neg() } else { step };
        let w = self.bits(ty)?;
        Some(Num {
            off: a.off.wrapping_add(step) & mask_bits(w),
            ty,
            exact: a.exact.min(w),
            ..a
        })
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
    fn truth(&mut self, e: &'a Ast) -> Option<bool> {
        match e {
            Ast::Logic(and, a, b) => match self.truth(a)? {
                t if t != *and => Some(t),
                _ => self.truth(b),
            },
            Ast::Un(Un::LogNot, a) => self.truth(a).map(|t| !t),
            Ast::Bin(op, a, b) if op.compares() => self.compare(*op, a, b),
            _ => self
                .value(e)
                .filter(|n| n.root == Root::Lit)
                .map(|n| n.off != 0),
        }
    }

    /// Decides a comparison.
    ///
    /// Two constants compare at the type they meet at. Two values on one
    /// root are equal exactly when their offsets agree at that width, if
    /// neither was narrowed below it; their order is undecided.
    ///
    /// # Arguments
    ///
    /// * `op` - The comparison.
    /// * `a` - The left side.
    /// * `b` - The right side.
    ///
    /// # Returns
    ///
    /// The truth, `None` when undecided.
    fn compare(&mut self, op: Bin, a: &'a Ast, b: &'a Ast) -> Option<bool> {
        let (x, y) = (self.value(a)?, self.value(b)?);
        let ty = self.common(x.ty, y.ty);
        let w = self.bits(ty)?;
        let (x, y) = (self.convert(x, ty)?, self.convert(y, ty)?);
        let same = (x.off ^ y.off) & mask_bits(w) == 0;
        if x.root != Root::Lit || y.root != Root::Lit {
            let one = x.root == y.root && x.exact >= w && y.exact >= w;
            return match op {
                Bin::Eq if one => Some(same),
                Bin::Ne if one => Some(!same),
                _ => None,
            };
        }
        let key = |v: u64| {
            if ty.signed() {
                i128::from(sext(v, w).cast_signed())
            } else {
                i128::from(v)
            }
        };
        let (p, q) = (key(x.off), key(y.off));
        Some(match op {
            Bin::Lt => p < q,
            Bin::Le => p <= q,
            Bin::Gt => p > q,
            Bin::Ge => p >= q,
            Bin::Eq => same,
            Bin::Ne => !same,
            _ => return None,
        })
    }
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
