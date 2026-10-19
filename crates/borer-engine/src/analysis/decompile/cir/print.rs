//! The printer: the one walk that turns a tree into text.
//!
//! The layout is the structurer's: two spaces per nesting level, one
//! statement per line, an opening brace at the end of its line and the
//! closing one on a line of its own, `switch` arms at the depth of their
//! `switch`, and an empty line left empty.

use super::{
    Arm, ArmBody, BinOp, Body, CTy, CaseLabel, Decl, Else, Expr, ExprKind, Head, Item, PostOp,
    Proto, Stmt, StmtKind, UnOp,
};
use std::fmt::Write as _;

/// Prints a body, one line per statement line, each ending in a newline.
///
/// # Arguments
///
/// * `body` - The tree.
///
/// # Returns
///
/// The text.
pub(in crate::analysis::decompile) fn print(body: &Body) -> String {
    let mut out = String::new();
    stmts(&body.stmts, 0, &mut out);
    out
}

/// Prints declarations, one per line: `uint64_t a, b;`, a pointer type as
/// `T *a, *b;`, a note after the semicolon.
///
/// # Arguments
///
/// * `decls` - The declarations, in order.
/// * `out` - Receives the text.
pub(in crate::analysis::decompile) fn print_decls(decls: &[Decl], out: &mut String) {
    for d in decls {
        let names: Vec<&str> = d.names.iter().map(super::Name::as_str).collect();
        match &d.ty {
            CTy::Ptr(inner) => {
                let mut base = String::new();
                ty(inner, &mut base);
                let _ = write!(out, "{} *{};", base.trim_end(), names.join(", *"));
            }
            CTy::Void | CTy::Int { .. } | CTy::Float(_) | CTy::FnPtr { .. } | CTy::Named(_) => {
                ty(&d.ty, out);
                let _ = write!(out, " {};", names.join(", "));
            }
        }
        if let Some(note) = &d.note {
            let _ = write!(out, " // {note}");
        }
        out.push('\n');
    }
}

/// Prints the file-scope items of a translation unit, one per line: a
/// defined function's body on its prototype's line.
///
/// # Arguments
///
/// * `items` - The items, in order.
/// * `out` - Receives the text.
pub(in crate::analysis::decompile) fn print_items(items: &[Item], out: &mut String) {
    for item in items {
        match item {
            Item::Extern(p) => {
                out.push_str("extern ");
                proto(p, out);
                out.push(';');
            }
            Item::Inline(p, body) => {
                out.push_str("static inline ");
                proto(p, out);
                out.push_str(" {");
                for line in print(body).lines().map(str::trim).filter(|l| !l.is_empty()) {
                    out.push(' ');
                    out.push_str(line);
                }
                out.push_str(" }");
            }
            Item::Table {
                name,
                ty: Some(CTy::FnPtr { ret, params }),
                entries,
            } => {
                out.push_str("static ");
                ty(ret, out);
                let _ = write!(out, " (*const {}[{}])(", name.as_str(), entries.len());
                if params.is_empty() {
                    out.push_str("void");
                }
                for (k, p) in params.iter().enumerate() {
                    if k > 0 {
                        out.push_str(", ");
                    }
                    ty(p, out);
                }
                let names: Vec<&str> = entries.iter().map(super::Name::as_str).collect();
                let _ = write!(out, ") = {{{}}};", names.join(", "));
            }
            Item::Table { name, entries, .. } => {
                let names: Vec<String> = entries
                    .iter()
                    .map(|e| format!("(void *){}", e.as_str()))
                    .collect();
                let _ = write!(
                    out,
                    "static void *const {}[{}] = {{{}}};",
                    name.as_str(),
                    entries.len(),
                    names.join(", ")
                );
            }
        }
        out.push('\n');
    }
}

/// Prints a prototype without its semicolon: `uint64_t f(uint64_t a1)`, a
/// pointer result or parameter written against its name.
///
/// # Arguments
///
/// * `p` - The prototype.
/// * `out` - Receives the text.
fn proto(p: &Proto, out: &mut String) {
    let named = |t: &CTy, name: &str, out: &mut String| {
        let at = out.len();
        ty(t, out);
        if !name.is_empty() && !out[at..].ends_with('*') {
            out.push(' ');
        }
        out.push_str(name);
    };
    named(&p.ret, p.name.as_str(), out);
    out.push('(');
    for (k, (t, name)) in p.params.iter().enumerate() {
        if k > 0 {
            out.push_str(", ");
        }
        named(t, name.as_ref().map_or("", super::Name::as_str), out);
    }
    if p.variadic {
        out.push_str(if p.params.is_empty() { "..." } else { ", ..." });
    }
    if p.params.is_empty() && !p.variadic {
        out.push_str("void");
    }
    out.push(')');
}

/// Prints statements at a nesting depth.
///
/// # Arguments
///
/// * `list` - The statements.
/// * `depth` - The nesting depth, two spaces each.
/// * `out` - Receives the text.
fn stmts(list: &[Stmt], depth: usize, out: &mut String) {
    for s in list {
        stmt(s, depth, out);
    }
}

/// Writes the indentation of a depth.
///
/// # Arguments
///
/// * `depth` - The nesting depth.
/// * `out` - Receives the text.
fn pad(depth: usize, out: &mut String) {
    for _ in 0..depth {
        out.push_str("  ");
    }
}

/// Prints one statement and the lines it holds.
///
/// # Arguments
///
/// * `s` - The statement.
/// * `depth` - Its nesting depth.
/// * `out` - Receives the text.
fn stmt(s: &Stmt, depth: usize, out: &mut String) {
    if matches!(s.kind, StmtKind::Blank) {
        out.push('\n');
        return;
    }
    pad(depth, out);
    line(s, depth, out);
}

/// Prints a statement from where its line's indentation ends, its last
/// line's newline included.
///
/// # Arguments
///
/// * `s` - The statement.
/// * `depth` - Its nesting depth, for the lines inside it.
/// * `out` - Receives the text.
fn line(s: &Stmt, depth: usize, out: &mut String) {
    match &s.kind {
        StmtKind::Expr(e) => {
            expr(e, out);
            out.push_str(";\n");
        }
        StmtKind::Return(None) => out.push_str("return;\n"),
        StmtKind::Return(Some(e)) => {
            out.push_str("return ");
            expr(e, out);
            out.push_str(";\n");
        }
        StmtKind::Goto(l) => {
            let _ = writeln!(out, "goto L_{:x};", l.0);
        }
        StmtKind::Label(l) => {
            let _ = writeln!(out, "L_{:x}:", l.0);
        }
        StmtKind::Break => out.push_str("break;\n"),
        StmtKind::Continue => out.push_str("continue;\n"),
        StmtKind::If { cond, then, other } => if_chain(cond, then, other.as_ref(), depth, out),
        StmtKind::Guard { cond, then } => {
            out.push_str("if (");
            expr(cond, out);
            out.push_str(") ");
            line(then, depth, out);
        }
        StmtKind::While { cond, body } => {
            out.push_str("while (");
            expr(cond, out);
            out.push_str(") {\n");
            close(body, depth, out);
        }
        StmtKind::DoWhile { body, cond } => {
            out.push_str("do {\n");
            stmts(body, depth + 1, out);
            pad(depth, out);
            out.push_str("} while (");
            expr(cond, out);
            out.push_str(");\n");
        }
        StmtKind::For {
            init,
            cond,
            step,
            body,
        } => {
            out.push_str("for (");
            expr(init, out);
            out.push_str("; ");
            expr(cond, out);
            out.push_str("; ");
            expr(step, out);
            out.push_str(") {\n");
            close(body, depth, out);
        }
        StmtKind::Switch { value, arms } => {
            out.push_str("switch (");
            expr(value, out);
            out.push_str(") {\n");
            for a in arms {
                pad(depth, out);
                arm(a, depth, out);
            }
            pad(depth, out);
            out.push_str("}\n");
        }
        StmtKind::Block(body) => {
            out.push_str("{\n");
            close(body, depth, out);
        }
        StmtKind::Try {
            seh,
            body,
            handlers,
        } => {
            out.push_str(if *seh { "__try {\n" } else { "try {\n" });
            stmts(body, depth + 1, out);
            for h in handlers {
                pad(depth, out);
                match &h.head {
                    Head::Catch(decl) => {
                        let _ = writeln!(out, "}} catch ({decl}) {{");
                    }
                    Head::Except(filter) => {
                        out.push_str("} __except (");
                        expr(filter, out);
                        out.push_str(") {\n");
                    }
                    Head::Finally => out.push_str("} __finally {\n"),
                }
                stmts(&h.body, depth + 1, out);
            }
            pad(depth, out);
            out.push_str("}\n");
        }
        StmtKind::Comment(text) => {
            let _ = writeln!(out, "//{text}");
        }
        StmtKind::Asm(text) => {
            let _ = writeln!(out, "/* asm: {text} */");
        }
        StmtKind::Blank => out.push('\n'),
        StmtKind::Raw(text) => {
            out.push_str(text);
            out.push('\n');
        }
    }
}

/// Prints a block's statements one level deeper and its closing brace.
///
/// # Arguments
///
/// * `body` - The statements inside the braces.
/// * `depth` - The depth of the line that opened the block.
/// * `out` - Receives the text.
fn close(body: &[Stmt], depth: usize, out: &mut String) {
    stmts(body, depth + 1, out);
    pad(depth, out);
    out.push_str("}\n");
}

/// Prints an `if` from its condition on, with its `else if` and `else`
/// arms joined to the closing braces (`} else {`).
///
/// # Arguments
///
/// * `cond` - The condition.
/// * `then` - The statements run when it holds.
/// * `other` - The `else` arm.
/// * `depth` - The depth of the `if`.
/// * `out` - Receives the text, after the indentation.
fn if_chain(cond: &Expr, then: &[Stmt], other: Option<&Else>, depth: usize, out: &mut String) {
    out.push_str("if (");
    expr(cond, out);
    out.push_str(") {\n");
    stmts(then, depth + 1, out);
    pad(depth, out);
    match other {
        None => out.push_str("}\n"),
        Some(Else::Block(body)) => {
            out.push_str("} else {\n");
            close(body, depth, out);
        }
        Some(Else::If(next)) => {
            out.push_str("} else ");
            line(next, depth, out);
        }
    }
}

/// Prints a `switch` arm from its labels on.
///
/// # Arguments
///
/// * `a` - The arm.
/// * `depth` - The depth of the `switch`.
/// * `out` - Receives the text, after the indentation.
fn arm(a: &Arm, depth: usize, out: &mut String) {
    for l in &a.labels {
        match l {
            CaseLabel::Value(v) => {
                out.push_str("case ");
                expr(v, out);
                out.push_str(": ");
            }
            CaseLabel::Default => out.push_str("default: "),
        }
    }
    match &a.body {
        ArmBody::Inline(s) => line(s, depth, out),
        ArmBody::Block(body) => {
            out.push_str("{\n");
            close(body, depth, out);
        }
    }
}

/// Spells a type: `uint8_t*` for a pointer.
///
/// # Arguments
///
/// * `t` - The type.
/// * `out` - Receives the text.
pub(super) fn ty(t: &CTy, out: &mut String) {
    match t {
        CTy::Void => out.push_str("void"),
        CTy::Int { bits, signed } => {
            let _ = write!(out, "{}int{bits}_t", if *signed { "" } else { "u" });
        }
        CTy::Float(32) => out.push_str("float"),
        CTy::Float(_) => out.push_str("double"),
        CTy::Ptr(inner) => {
            ty(inner, out);
            out.push('*');
        }
        CTy::FnPtr { ret, params } => {
            ty(ret, out);
            out.push_str(" (*)(");
            for (k, p) in params.iter().enumerate() {
                if k > 0 {
                    out.push_str(", ");
                }
                ty(p, out);
            }
            out.push(')');
        }
        CTy::Named(name) => out.push_str(name),
    }
}

/// Spells a binary operator.
///
/// # Arguments
///
/// * `op` - The operator.
pub(super) const fn bin_op(op: BinOp) -> &'static str {
    match op {
        BinOp::Mul => "*",
        BinOp::Div => "/",
        BinOp::Rem => "%",
        BinOp::Add => "+",
        BinOp::Sub => "-",
        BinOp::Shl => "<<",
        BinOp::Shr => ">>",
        BinOp::Lt => "<",
        BinOp::Le => "<=",
        BinOp::Gt => ">",
        BinOp::Ge => ">=",
        BinOp::Eq => "==",
        BinOp::Ne => "!=",
        BinOp::BitAnd => "&",
        BinOp::BitXor => "^",
        BinOp::BitOr => "|",
        BinOp::And => "&&",
        BinOp::Or => "||",
    }
}

/// Prints an expression: binary operators spaced, unary ones and casts
/// joined to their operand, arguments separated by `, `.
///
/// # Arguments
///
/// * `e` - The expression.
/// * `out` - Receives the text.
fn expr(e: &Expr, out: &mut String) {
    match &e.kind {
        ExprKind::Lit(l) => out.push_str(&l.text),
        ExprKind::Name(n) => out.push_str(n.as_str()),
        ExprKind::Unary(op, a) => {
            out.push_str(match op {
                UnOp::Neg => "-",
                UnOp::Plus => "+",
                UnOp::BitNot => "~",
                UnOp::Not => "!",
                UnOp::Deref => "*",
                UnOp::AddrOf => "&",
                UnOp::PreInc => "++",
                UnOp::PreDec => "--",
            });
            expr(a, out);
        }
        ExprKind::Postfix(op, a) => {
            expr(a, out);
            out.push_str(match op {
                PostOp::Inc => "++",
                PostOp::Dec => "--",
            });
        }
        ExprKind::Binary(op, l, r) => {
            expr(l, out);
            out.push(' ');
            out.push_str(bin_op(*op));
            out.push(' ');
            expr(r, out);
        }
        ExprKind::Assign(op, place, value) => {
            expr(place, out);
            out.push(' ');
            if let Some(op) = op {
                out.push_str(bin_op(*op));
            }
            out.push_str("= ");
            expr(value, out);
        }
        ExprKind::Cond(c, a, b) => {
            expr(c, out);
            out.push_str(" ? ");
            expr(a, out);
            out.push_str(" : ");
            expr(b, out);
        }
        ExprKind::Cast(t, a) => {
            out.push('(');
            ty(t, out);
            out.push(')');
            expr(a, out);
        }
        ExprKind::Call(f, args) => {
            expr(f, out);
            out.push('(');
            for (k, a) in args.iter().enumerate() {
                if k > 0 {
                    out.push_str(", ");
                }
                expr(a, out);
            }
            out.push(')');
        }
        ExprKind::Index(b, i) => {
            expr(b, out);
            out.push('[');
            expr(i, out);
            out.push(']');
        }
        ExprKind::Member { base, field, arrow } => {
            expr(base, out);
            out.push_str(if *arrow { "->" } else { "." });
            out.push_str(field.as_str());
        }
        ExprKind::Paren(a) => {
            out.push('(');
            expr(a, out);
            out.push(')');
        }
        ExprKind::Raw(text) => out.push_str(text),
    }
}
