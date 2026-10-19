//! The invariants of a printable tree, checked: what [`check`] finds is
//! what keeps the text from being C.

use super::{Arm, ArmBody, Body, CaseLabel, Else, Expr, ExprKind, Label, Name, Stmt, StmtKind};
use std::collections::BTreeSet;

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
}

/// Lists the violations of a body, each once, in the order the body meets
/// them.
///
/// A called name is a function, which the translation unit declares, so
/// only names read as values must be in `declared`.
///
/// # Arguments
///
/// * `body` - The tree.
/// * `declared` - The names the function declares: its parameters, locals
///   and globals.
///
/// # Returns
///
/// The violations, empty for a body that is C.
pub(in crate::analysis::decompile) fn check(
    body: &Body,
    declared: &BTreeSet<&str>,
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
    /// The names declared.
    declared: &'d BTreeSet<&'d str>,
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
            Name::Ident(i) if !self.declared.contains(i.as_str()) => {
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
}
