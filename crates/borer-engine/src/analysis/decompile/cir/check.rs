//! The invariants of a printable tree, checked: what [`check`] finds is
//! what keeps the text from being C.

use super::print::bin_op;
use super::{
    Arm, ArmBody, BinOp, Body, CTy, CaseLabel, Else, Expr, ExprKind, Label, LitKind, Name, Stmt,
    StmtKind, UnOp,
};
use std::collections::{BTreeMap, BTreeSet};

/// What a value holds, as far as C's operators care: a float or a pointer
/// takes fewer of them than an integer.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(in crate::analysis::decompile) enum Holds {
    /// A `float` or a `double`.
    Float,
    /// A pointer, to data or to a function.
    Pointer,
    /// A fixed-width integer.
    Integer,
    /// A value of a type the check does not know.
    Other,
}

impl Holds {
    /// Classifies a type.
    ///
    /// # Arguments
    ///
    /// * `ty` - The type.
    ///
    /// # Returns
    ///
    /// What a value of that type holds.
    pub(in crate::analysis::decompile) const fn of(ty: &CTy) -> Self {
        match ty {
            CTy::Float(_) => Self::Float,
            CTy::Ptr(_) | CTy::FnPtr { .. } => Self::Pointer,
            CTy::Int { .. } => Self::Integer,
            CTy::Void | CTy::Named(_) => Self::Other,
        }
    }
}

/// A way a tree breaks an invariant.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(in crate::analysis::decompile) enum Violation {
    /// An identifier read that nothing declares.
    Undeclared(String),
    /// A name that is not a C identifier.
    NotIdent(String),
    /// A `goto` whose label the body does not hold.
    DanglingGoto(Label),
    /// A computed `goto`, which C does not have.
    ComputedGoto(String),
    /// Text the builder could not read as C.
    Raw(String),
    /// A call to an identifier nothing declares.
    UndeclaredCall(String),
    /// An operator C does not apply to what its operand holds: `&` on a
    /// float, `*` on a pointer.
    BadOperand(&'static str, Holds),
}

/// Lists the violations of a body, each once, in the order the body meets
/// them.
///
/// A called identifier `declared` does not hold is
/// [`Violation::UndeclaredCall`], not [`Violation::Undeclared`]: the
/// translation unit may declare it. An operand's [`Holds`] is read from the
/// declared names, casts and literals only, so an operator is reported
/// only on a value C's rules type for certain.
///
/// # Arguments
///
/// * `body` - The tree.
/// * `declared` - The names the function declares (its parameters, locals,
///   globals and the helpers it defines), each with what it holds.
///
/// # Returns
///
/// The violations, empty for a body that is C.
pub(in crate::analysis::decompile) fn check(
    body: &Body,
    declared: &BTreeMap<&str, Holds>,
) -> Vec<Violation> {
    let mut walk = Walk {
        declared,
        labels: BTreeSet::new(),
        gotos: Vec::new(),
        found: Vec::new(),
    };
    walk.stmts(&body.stmts);
    let Walk {
        labels,
        gotos,
        mut found,
        ..
    } = walk;
    found.extend(
        gotos
            .into_iter()
            .filter(|l| !labels.contains(l))
            .map(Violation::DanglingGoto),
    );
    let mut seen = BTreeSet::new();
    found.retain(|v| seen.insert(v.clone()));
    found
}

/// The state of a walk over a body.
struct Walk<'d> {
    /// The names declared, with what each holds.
    declared: &'d BTreeMap<&'d str, Holds>,
    /// The labels the body holds.
    labels: BTreeSet<Label>,
    /// The labels its `goto`s name, in order.
    gotos: Vec<Label>,
    /// The violations found so far.
    found: Vec<Violation>,
}

impl Walk<'_> {
    /// Walks statements.
    ///
    /// # Arguments
    ///
    /// * `list` - The statements.
    fn stmts(&mut self, list: &[Stmt]) {
        for s in list {
            self.stmt(s);
        }
    }

    /// Walks one statement and what it holds.
    ///
    /// # Arguments
    ///
    /// * `s` - The statement.
    fn stmt(&mut self, s: &Stmt) {
        match &s.kind {
            StmtKind::Expr(e) | StmtKind::Return(Some(e)) => self.expr(e),
            StmtKind::Return(None)
            | StmtKind::Break
            | StmtKind::Continue
            | StmtKind::Comment(_)
            | StmtKind::Asm(_)
            | StmtKind::Blank => {}
            StmtKind::Goto(l) => self.gotos.push(*l),
            StmtKind::Label(l) => {
                self.labels.insert(*l);
            }
            StmtKind::If { cond, then, other } => {
                self.expr(cond);
                self.stmts(then);
                match other {
                    None => {}
                    Some(Else::Block(body)) => self.stmts(body),
                    Some(Else::If(next)) => self.stmt(next),
                }
            }
            StmtKind::Guard { cond, then } => {
                self.expr(cond);
                self.stmt(then);
            }
            StmtKind::While { cond, body } | StmtKind::DoWhile { body, cond } => {
                self.expr(cond);
                self.stmts(body);
            }
            StmtKind::For {
                init,
                cond,
                step,
                body,
            } => {
                self.expr(init);
                self.expr(cond);
                self.expr(step);
                self.stmts(body);
            }
            StmtKind::Switch { value, arms } => {
                self.expr(value);
                for Arm { labels, body, .. } in arms {
                    for l in labels {
                        match l {
                            CaseLabel::Value(v) => self.expr(v),
                            CaseLabel::Default => {}
                        }
                    }
                    match body {
                        ArmBody::Inline(s) => self.stmt(s),
                        ArmBody::Block(list) => self.stmts(list),
                    }
                }
            }
            StmtKind::Block(body) => self.stmts(body),
            StmtKind::Raw(text) if text.contains("goto *") => {
                self.found.push(Violation::ComputedGoto(text.clone()));
            }
            StmtKind::Raw(text) => self.found.push(Violation::Raw(text.clone())),
        }
    }

    /// Checks a name read as a value.
    ///
    /// # Arguments
    ///
    /// * `n` - The name.
    fn name(&mut self, n: &Name) {
        match n {
            Name::Ident(i) if !self.declared.contains_key(i.as_str()) => {
                self.found
                    .push(Violation::Undeclared(i.as_str().to_owned()));
            }
            Name::Ident(_) => {}
            Name::Sym(s) => self.found.push(Violation::NotIdent(s.clone())),
        }
    }

    /// Walks an expression.
    ///
    /// # Arguments
    ///
    /// * `e` - The expression.
    fn expr(&mut self, e: &Expr) {
        self.operands(e);
        match &e.kind {
            ExprKind::Lit(_) => {}
            ExprKind::Name(n) => self.name(n),
            ExprKind::Unary(_, a)
            | ExprKind::Postfix(_, a)
            | ExprKind::Cast(_, a)
            | ExprKind::Paren(a) => self.expr(a),
            ExprKind::Binary(_, l, r) | ExprKind::Assign(_, l, r) | ExprKind::Index(l, r) => {
                self.expr(l);
                self.expr(r);
            }
            ExprKind::Cond(c, a, b) => {
                self.expr(c);
                self.expr(a);
                self.expr(b);
            }
            ExprKind::Call(f, args) => {
                match &f.kind {
                    ExprKind::Name(Name::Ident(i)) if !self.declared.contains_key(i.as_str()) => {
                        self.found
                            .push(Violation::UndeclaredCall(i.as_str().to_owned()));
                    }
                    ExprKind::Name(Name::Ident(_)) => {}
                    ExprKind::Name(Name::Sym(s)) => {
                        self.found.push(Violation::NotIdent(s.clone()));
                    }
                    ExprKind::Lit(_)
                    | ExprKind::Unary(..)
                    | ExprKind::Postfix(..)
                    | ExprKind::Binary(..)
                    | ExprKind::Assign(..)
                    | ExprKind::Cond(..)
                    | ExprKind::Cast(..)
                    | ExprKind::Call(..)
                    | ExprKind::Index(..)
                    | ExprKind::Member { .. }
                    | ExprKind::Paren(_)
                    | ExprKind::Raw(_) => self.expr(f),
                }
                for a in args {
                    self.expr(a);
                }
            }
            ExprKind::Member { base, field, .. } => {
                self.expr(base);
                if let Name::Sym(s) = field {
                    self.found.push(Violation::NotIdent(s.clone()));
                }
            }
            ExprKind::Raw(text) => self.found.push(Violation::Raw(text.clone())),
        }
    }

    /// Reports an operator C does not apply to what its operand holds.
    ///
    /// # Arguments
    ///
    /// * `e` - The expression, whose own operator is checked.
    fn operands(&mut self, e: &Expr) {
        let (op, sides): (&'static str, [Option<&Expr>; 2]) = match &e.kind {
            ExprKind::Unary(UnOp::BitNot, a) => ("~", [Some(a), None]),
            ExprKind::Unary(UnOp::Deref, a) => ("unary *", [Some(a), None]),
            ExprKind::Index(base, at) if self.holds(at) == Holds::Integer => {
                ("[]", [Some(base), None])
            }
            ExprKind::Binary(op, l, r) | ExprKind::Assign(Some(op), l, r) => {
                (bin_op(*op), [Some(l), Some(r)])
            }
            ExprKind::Lit(_)
            | ExprKind::Name(_)
            | ExprKind::Unary(..)
            | ExprKind::Postfix(..)
            | ExprKind::Assign(None, ..)
            | ExprKind::Cond(..)
            | ExprKind::Cast(..)
            | ExprKind::Call(..)
            | ExprKind::Index(..)
            | ExprKind::Member { .. }
            | ExprKind::Paren(_)
            | ExprKind::Raw(_) => return,
        };
        for side in sides.into_iter().flatten() {
            let holds = self.holds(side);
            if refuses(op, holds) {
                self.found.push(Violation::BadOperand(op, holds));
            }
        }
    }

    /// What an expression holds when C's rules say so for certain,
    /// [`Holds::Other`] whenever the check cannot tell.
    ///
    /// # Arguments
    ///
    /// * `e` - The expression.
    ///
    /// # Returns
    ///
    /// What the value holds.
    fn holds(&self, e: &Expr) -> Holds {
        match &e.kind {
            ExprKind::Lit(l) => match l.kind {
                LitKind::Float => Holds::Float,
                LitKind::Str => Holds::Pointer,
                LitKind::Int | LitKind::Char => Holds::Integer,
            },
            ExprKind::Name(Name::Ident(i)) => self
                .declared
                .get(i.as_str())
                .copied()
                .unwrap_or(Holds::Other),
            ExprKind::Unary(UnOp::AddrOf, _) => Holds::Pointer,
            ExprKind::Unary(UnOp::Not, _) => Holds::Integer,
            ExprKind::Unary(UnOp::Deref, p) => pointee(p),
            ExprKind::Index(base, _) => pointee(base),
            ExprKind::Unary(
                UnOp::Neg | UnOp::Plus | UnOp::BitNot | UnOp::PreInc | UnOp::PreDec,
                a,
            )
            | ExprKind::Postfix(_, a)
            | ExprKind::Paren(a)
            | ExprKind::Assign(_, a, _) => self.holds(a),
            ExprKind::Cast(ty, _) => Holds::of(ty),
            ExprKind::Binary(op, l, r) => {
                let (l, r) = (self.holds(l), self.holds(r));
                match op {
                    BinOp::Add | BinOp::Sub => match (l, r) {
                        (Holds::Pointer, Holds::Pointer) => Holds::Other,
                        (Holds::Float, _) | (_, Holds::Float) => Holds::Float,
                        (Holds::Other, _) | (_, Holds::Other) => Holds::Other,
                        (Holds::Pointer, Holds::Integer) | (Holds::Integer, Holds::Pointer) => {
                            Holds::Pointer
                        }
                        (Holds::Integer, Holds::Integer) => Holds::Integer,
                    },
                    BinOp::Mul | BinOp::Div if l == Holds::Float || r == Holds::Float => {
                        Holds::Float
                    }
                    BinOp::Mul
                    | BinOp::Div
                    | BinOp::Rem
                    | BinOp::Shl
                    | BinOp::Shr
                    | BinOp::BitAnd
                    | BinOp::BitXor
                    | BinOp::BitOr
                        if l == Holds::Integer && r == Holds::Integer =>
                    {
                        Holds::Integer
                    }
                    BinOp::Mul
                    | BinOp::Div
                    | BinOp::Rem
                    | BinOp::Shl
                    | BinOp::Shr
                    | BinOp::BitAnd
                    | BinOp::BitXor
                    | BinOp::BitOr => Holds::Other,
                    BinOp::Lt
                    | BinOp::Le
                    | BinOp::Gt
                    | BinOp::Ge
                    | BinOp::Eq
                    | BinOp::Ne
                    | BinOp::And
                    | BinOp::Or => Holds::Integer,
                }
            }
            ExprKind::Cond(_, a, b) => match (self.holds(a), self.holds(b)) {
                (a, b) if a == b => a,
                _ => Holds::Other,
            },
            ExprKind::Name(Name::Sym(_))
            | ExprKind::Call(..)
            | ExprKind::Member { .. }
            | ExprKind::Raw(_) => Holds::Other,
        }
    }
}

/// What the place a pointer expression points at holds, read from a cast
/// to a pointer type only.
///
/// # Arguments
///
/// * `p` - The pointer expression.
///
/// # Returns
///
/// What the place holds, [`Holds::Other`] when no cast says.
fn pointee(p: &Expr) -> Holds {
    match &p.kind {
        ExprKind::Cast(CTy::Ptr(inner), _) => Holds::of(inner),
        ExprKind::Paren(a) => pointee(a),
        ExprKind::Lit(_)
        | ExprKind::Name(_)
        | ExprKind::Unary(..)
        | ExprKind::Postfix(..)
        | ExprKind::Binary(..)
        | ExprKind::Assign(..)
        | ExprKind::Cond(..)
        | ExprKind::Cast(..)
        | ExprKind::Call(..)
        | ExprKind::Index(..)
        | ExprKind::Member { .. }
        | ExprKind::Raw(_) => Holds::Other,
    }
}

/// Tells whether C refuses an operator on an operand that holds this.
///
/// A float takes no `%`, shift or bitwise operator and is not read
/// through, a pointer takes none of those nor `*` or `/`, an integer is
/// not read through (`unary *`, `[]`).
///
/// # Arguments
///
/// * `op` - The operator as spelled, a load `unary *` or `[]`.
/// * `holds` - What the operand holds.
///
/// # Returns
///
/// Whether the operator does not apply.
fn refuses(op: &str, holds: Holds) -> bool {
    let bits = matches!(op, "%" | "<<" | ">>" | "&" | "|" | "^" | "~");
    let load = matches!(op, "unary *" | "[]");
    match holds {
        Holds::Float => bits || load,
        Holds::Pointer => bits || matches!(op, "*" | "/"),
        Holds::Integer => load,
        Holds::Other => false,
    }
}
