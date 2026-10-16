//! Variables: one per def-use web of a register, and the definitions no
//! use reads dropped.
//!
//! The lifter names a value by the register that holds it, so one `rax`
//! stands for every value a function ever leaves in `rax`: a length, then
//! a pointer, then a status. This pass reads the finished text as the C it
//! is, joins the definitions that reach a common use into webs (a web is
//! one value as far as any reader can tell), gives every web a variable of
//! its own, `var1` to `varN` in the order they appear, drops the
//! definitions nothing reads, and declares the new names at the register's
//! type. Then a temporary read once folds into its read, a constant into
//! the reads that convert it whole, and a copy into its source, where
//! nothing can run out of order. It changes spelling only: every use still
//! reads exactly the definitions it read, at the type it read them.
//!
//! A web the function's entry reaches keeps the register's name, since it
//! holds what the register held when the function was called; so does a
//! web an unmodelled instruction (`/* asm */`), a call to a thunk that
//! jumps through the register, or the caller (a handed-back second result)
//! reads, since those read the machine register, not a C variable. A jump
//! out of the text (`goto *x;`) keeps every value alive. A register whose
//! address the text takes or that an expression assigns inside itself is
//! left alone, and a text this cannot read is returned unchanged.

use super::traces::{Stmt, blank, statements};
use super::*;

/// Most nodes times tracked variables one text is analysed for: the
/// liveness and web walks are linear in each, and a text past this keeps
/// its register names rather than costing a long walk.
const WORK_MAX: usize = 4_000_000;

/// Most rounds of dropping dead definitions: a dropped line can leave the
/// definitions it read dead in turn.
const ROUNDS: usize = 8;

/// The name every new variable is numbered under: `var1`, `var2`, ...
///
/// Not `v1`: `v0` to `v31` are arm64's vector registers.
const PREFIX: &str = "var";

/// The operators and punctuation of more than one character, longest first.
const PUNCTS: [&str; 22] = [
    "<<=", ">>=", "->", "++", "--", "<<", ">>", "<=", ">=", "==", "!=", "&&", "||", "+=", "-=",
    "*=", "/=", "%=", "&=", "|=", "^=", "::",
];

/// The operators that write the variable before them.
const COMPOUND: [&str; 10] = ["+=", "-=", "*=", "/=", "%=", "&=", "|=", "^=", "<<=", ">>="];


/// What a token is.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum Lex {
    /// An identifier.
    Name,
    /// A numeric literal.
    Number,
    /// A string or character literal.
    Literal,
    /// An operator or punctuation.
    Punct,
}

/// One token of a line and the bytes it spans.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) struct Tok {
    /// What it is.
    pub(super) lex: Lex,
    /// Its first byte in the line.
    pub(super) at: usize,
    /// One past its last byte.
    pub(super) end: usize,
}

/// Splits a line into tokens, leaving out whitespace and comments.
///
/// # Arguments
///
/// * `line` - One line of the text.
///
/// # Returns
///
/// The tokens in order; a comment that does not end ends the line.
pub(super) fn lex(line: &str) -> Vec<Tok> {
    let b = line.as_bytes();
    let mut out = Vec::new();
    let mut i = 0;
    while let Some(&c) = b.get(i) {
        let rest = line.get(i..).unwrap_or("");
        if c.is_ascii_whitespace() {
            i += 1;
            continue;
        }
        if rest.starts_with("//") {
            break;
        }
        if rest.starts_with("/*") {
            match rest.get(2..).and_then(|r| r.find("*/")) {
                Some(k) => {
                    i += k + 4;
                    continue;
                }
                None => break,
            }
        }
        let quote = match c {
            b'"' | b'\'' => Some(0),
            b'L' | b'u' | b'U' if matches!(b.get(i + 1), Some(b'"' | b'\'')) => Some(1),
            b'u' if b.get(i + 1) == Some(&b'8') && b.get(i + 2) == Some(&b'"') => Some(2),
            _ => None,
        };
        if let Some(skip) = quote {
            let close = b.get(i + skip).copied().unwrap_or(b'"');
            let mut j = i + skip + 1;
            while let Some(&d) = b.get(j) {
                if d == b'\\' {
                    j += 2;
                    continue;
                }
                j += 1;
                if d == close {
                    break;
                }
            }
            let end = j.min(b.len());
            out.push(Tok {
                lex: Lex::Literal,
                at: i,
                end,
            });
            i = end;
            continue;
        }
        if c.is_ascii_digit() {
            let hex = rest.starts_with("0x") || rest.starts_with("0X");
            let mut j = i + 1;
            while let Some(&d) = b.get(j) {
                let sign =
                    matches!(d, b'+' | b'-') && !hex && matches!(b.get(j - 1), Some(b'e' | b'E'));
                if d.is_ascii_alphanumeric() || d == b'_' || d == b'.' || sign {
                    j += 1;
                } else {
                    break;
                }
            }
            out.push(Tok {
                lex: Lex::Number,
                at: i,
                end: j,
            });
            i = j;
            continue;
        }
        if c.is_ascii_alphabetic() || c == b'_' {
            let mut j = i + 1;
            while b
                .get(j)
                .is_some_and(|d| d.is_ascii_alphanumeric() || *d == b'_')
            {
                j += 1;
            }
            out.push(Tok {
                lex: Lex::Name,
                at: i,
                end: j,
            });
            i = j;
            continue;
        }
        let len = PUNCTS.iter().find(|p| rest.starts_with(**p)).map_or_else(
            || rest.chars().next().map_or(1, char::len_utf8),
            |p| p.len(),
        );
        out.push(Tok {
            lex: Lex::Punct,
            at: i,
            end: i + len,
        });
        i += len;
    }
    out
}

/// One line and its tokens.
#[derive(Debug)]
pub(super) struct Line<'t> {
    /// The line as written.
    pub(super) text: &'t str,
    /// Its tokens.
    pub(super) toks: Vec<Tok>,
}

impl Line<'_> {
    /// The text of token `k`, empty past the end.
    ///
    /// # Arguments
    ///
    /// * `k` - The token's index.
    pub(super) fn word(&self, k: usize) -> &str {
        self.toks
            .get(k)
            .and_then(|t| self.text.get(t.at..t.end))
            .unwrap_or("")
    }

    /// Tells whether token `k` is the punctuation `p`.
    ///
    /// # Arguments
    ///
    /// * `k` - The token's index.
    /// * `p` - The punctuation.
    pub(super) fn is(&self, k: usize, p: &str) -> bool {
        self.toks.get(k).is_some_and(|t| t.lex == Lex::Punct) && self.word(k) == p
    }

    /// The token closing the bracket opened at `open`, if it closes.
    ///
    /// # Arguments
    ///
    /// * `open` - The index of a `(` or `[` token.
    pub(super) fn closing(&self, open: usize) -> Option<usize> {
        let mut depth = 0usize;
        for k in open..self.toks.len() {
            if self.is(k, "(") || self.is(k, "[") {
                depth += 1;
            } else if self.is(k, ")") || self.is(k, "]") {
                depth = depth.checked_sub(1)?;
                if depth == 0 {
                    return Some(k);
                }
            }
        }
        None
    }

    /// The first token at or after `from` that is the punctuation `p`.
    ///
    /// # Arguments
    ///
    /// * `from` - Where the search starts.
    /// * `p` - The punctuation.
    fn find(&self, from: usize, p: &str) -> Option<usize> {
        (from..self.toks.len()).find(|&k| self.is(k, p))
    }

    /// The span of a statement on the line: after any `case`/`default`
    /// labels and the condition of a one-line `if`.
    fn statement(&self) -> (usize, usize) {
        let mut at = 0;
        loop {
            match self.word(at) {
                "case" => match self.find(at, ":") {
                    Some(k) => at = k + 1,
                    None => break,
                },
                "default" if self.is(at + 1, ":") => at += 2,
                _ => break,
            }
        }
        if self.word(at) == "if"
            && self.is(at + 1, "(")
            && let Some(close) = self.closing(at + 1)
        {
            at = close + 1;
        }
        (at, self.toks.len())
    }

    /// The span inside the first parentheses of the line: an `if`, `while`
    /// or `switch` condition, or a `for` header.
    fn parenthesized(&self) -> Option<(usize, usize)> {
        let open = self.find(0, "(")?;
        Some((open + 1, self.closing(open)?))
    }

    /// The span after the keyword `kw` on the line, to its end.
    ///
    /// # Arguments
    ///
    /// * `kw` - `return` or `goto`.
    fn after(&self, kw: &str) -> Option<(usize, usize)> {
        let k = (0..self.toks.len()).find(|&k| self.word(k) == kw)?;
        Some((k + 1, self.toks.len()))
    }
}


/// What a node does to the tracked variables.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Form {
    /// Nothing: a label, a loop head, a join.
    Join,
    /// The function's entry, which gives every variable the value its
    /// register holds.
    Entry,
    /// The function's exit, which hands the handed-back registers to the
    /// caller.
    Exit,
    /// A statement: assignments, a call.
    Statement,
    /// An expression that is only read: a condition, a returned value.
    Expr,
    /// An unmodelled instruction, which reads and writes every register.
    Machine,
    /// A jump out of the text, after which the code reads any register.
    Leave,
}

/// One point of the text's control flow.
#[derive(Debug)]
struct Node {
    /// The body line it reads, if any.
    line: Option<usize>,
    /// The token span of the line it reads.
    span: (usize, usize),
    /// What it does.
    form: Form,
    /// The nodes that can run next.
    succ: Vec<usize>,
}

/// The control flow of a body, as its statements nest.
#[derive(Debug, Default)]
struct Graph {
    /// The nodes; the entry is the first, the exit the second.
    nodes: Vec<Node>,
    /// Each label's node, by the address it names.
    labels: BTreeMap<u64, usize>,
    /// The `goto`s: the node jumping and the label's address.
    gotos: Vec<(usize, u64)>,
}

/// The exit node's index.
const EXIT: usize = 1;

impl Graph {
    /// Adds a node and returns its index.
    ///
    /// # Arguments
    ///
    /// * `line` - The body line it reads, if any.
    /// * `span` - The token span it reads.
    /// * `form` - What it does.
    fn add(&mut self, line: Option<usize>, span: (usize, usize), form: Form) -> usize {
        self.nodes.push(Node {
            line,
            span,
            form,
            succ: Vec::new(),
        });
        self.nodes.len() - 1
    }

    /// Adds an edge from every node of `from` to `to`.
    ///
    /// # Arguments
    ///
    /// * `from` - The nodes that run first.
    /// * `to` - The node that runs next.
    fn link(&mut self, from: &[usize], to: usize) {
        for &f in from {
            if let Some(n) = self.nodes.get_mut(f)
                && !n.succ.contains(&to)
            {
                n.succ.push(to);
            }
        }
    }

    /// Adds the nodes of a run of statements.
    ///
    /// # Arguments
    ///
    /// * `stmts` - The statements, in order.
    /// * `ins` - The nodes control reaches the first from.
    /// * `brk` - Where a `break` goes, if anywhere.
    /// * `cont` - Where a `continue` goes, if anywhere.
    /// * `lines` - The body's lines.
    ///
    /// # Returns
    ///
    /// The nodes control leaves the run from, or `None` for a shape this
    /// does not read.
    fn run(
        &mut self,
        stmts: &[Stmt],
        ins: Vec<usize>,
        brk: Option<usize>,
        cont: Option<usize>,
        lines: &[Line<'_>],
    ) -> Option<Vec<usize>> {
        let mut cur = ins;
        for s in stmts {
            cur = self.stmt(s, &cur, brk, cont, lines)?;
        }
        Some(cur)
    }

    /// Adds the nodes of one statement.
    ///
    /// # Arguments
    ///
    /// * `s` - The statement.
    /// * `ins` - The nodes control reaches it from.
    /// * `brk` - Where a `break` goes, if anywhere.
    /// * `cont` - Where a `continue` goes, if anywhere.
    /// * `lines` - The body's lines.
    ///
    /// # Returns
    ///
    /// The nodes control leaves it from, or `None` for a shape this does
    /// not read.
    fn stmt(
        &mut self,
        s: &Stmt,
        ins: &[usize],
        brk: Option<usize>,
        cont: Option<usize>,
        lines: &[Line<'_>],
    ) -> Option<Vec<usize>> {
        let line_of = |n: usize| n.checked_sub(1);
        let get = |n: usize| line_of(n).and_then(|i| lines.get(i));
        Some(match s {
            Stmt::Label(addr, _) => {
                let n = self.add(None, (0, 0), Form::Join);
                self.labels.insert(*addr, n);
                self.link(ins, n);
                vec![n]
            }
            Stmt::Plain(at) => {
                let l = get(*at)?;
                let form = if l.text.trim_start().starts_with("/* asm") {
                    Form::Machine
                } else {
                    Form::Statement
                };
                let n = self.add(line_of(*at), l.statement(), form);
                self.link(ins, n);
                vec![n]
            }
            Stmt::If(at, then, other) => {
                let c = self.add(line_of(*at), get(*at)?.parenthesized()?, Form::Expr);
                self.link(ins, c);
                let mut outs = self.run(then, vec![c], brk, cont, lines)?;
                if other.is_empty() {
                    outs.push(c);
                } else {
                    outs.extend(self.run(other, vec![c], brk, cont, lines)?);
                }
                outs
            }
            Stmt::Loop(body) => {
                let head = self.add(None, (0, 0), Form::Join);
                let after = self.add(None, (0, 0), Form::Join);
                self.link(ins, head);
                let outs = self.run(body, vec![head], Some(after), Some(head), lines)?;
                self.link(&outs, head);
                vec![after]
            }
            Stmt::While(at, body) => {
                let c = self.add(line_of(*at), get(*at)?.parenthesized()?, Form::Expr);
                let after = self.add(None, (0, 0), Form::Join);
                self.link(ins, c);
                let outs = self.run(body, vec![c], Some(after), Some(c), lines)?;
                self.link(&outs, c);
                self.link(&[c], after);
                vec![after]
            }
            Stmt::For(at, body) => {
                let l = get(*at)?;
                let (open, close) = l.parenthesized()?;
                let first = l.find(open, ";").filter(|k| *k < close)?;
                let second = l.find(first + 1, ";").filter(|k| *k < close)?;
                let line = line_of(*at);
                let init = self.add(line, (open, first), Form::Statement);
                let test = self.add(line, (first + 1, second), Form::Expr);
                let step = self.add(line, (second + 1, close), Form::Statement);
                let after = self.add(None, (0, 0), Form::Join);
                self.link(ins, init);
                self.link(&[init], test);
                let outs = self.run(body, vec![test], Some(after), Some(step), lines)?;
                self.link(&outs, step);
                self.link(&[step], test);
                self.link(&[test], after);
                vec![after]
            }
            Stmt::Do(body, at) => {
                let head = self.add(None, (0, 0), Form::Join);
                let test = self.add(line_of(*at), get(*at)?.parenthesized()?, Form::Expr);
                let after = self.add(None, (0, 0), Form::Join);
                self.link(ins, head);
                let outs = self.run(body, vec![head], Some(after), Some(test), lines)?;
                self.link(&outs, test);
                self.link(&[test], head);
                self.link(&[test], after);
                vec![after]
            }
            Stmt::Switch(at, arms) => {
                let v = self.add(line_of(*at), get(*at)?.parenthesized()?, Form::Expr);
                let after = self.add(None, (0, 0), Form::Join);
                self.link(ins, v);
                let mut fall: Vec<usize> = Vec::new();
                let mut default = false;
                for (is_default, _, body) in arms {
                    let head = self.add(None, (0, 0), Form::Join);
                    self.link(&[v], head);
                    self.link(&fall, head);
                    fall = self.run(body, vec![head], Some(after), cont, lines)?;
                    default |= *is_default;
                }
                self.link(&fall, after);
                if !default {
                    self.link(&[v], after);
                }
                vec![after]
            }
            Stmt::Goto(addr) => {
                for &n in ins {
                    self.gotos.push((n, *addr));
                }
                Vec::new()
            }
            Stmt::Break => {
                self.link(ins, brk?);
                Vec::new()
            }
            Stmt::Continue => {
                self.link(ins, cont?);
                Vec::new()
            }
            Stmt::Return(at) => {
                let n = self.add(line_of(*at), get(*at)?.after("return")?, Form::Expr);
                self.link(ins, n);
                self.link(&[n], EXIT);
                Vec::new()
            }
            Stmt::Halt(at) => {
                let l = get(*at)?;
                let n = match l.after("goto") {
                    Some(span) => self.add(line_of(*at), span, Form::Leave),
                    None => self.add(line_of(*at), (0, l.toks.len()), Form::Expr),
                };
                self.link(ins, n);
                Vec::new()
            }
        })
    }
}


/// What one node reads and writes of the tracked variables: each a
/// variable and the token naming it.
#[derive(Debug, Default, Clone)]
struct Occs {
    /// Plain assignments: `v = ...`, the targets of a chain.
    defs: Vec<(usize, usize)>,
    /// Compound assignments and increments, which read the old value.
    rmw: Vec<(usize, usize)>,
    /// Reads.
    uses: Vec<(usize, usize)>,
    /// Whether it reads every variable.
    reads_all: bool,
    /// Whether it writes every variable.
    writes_all: bool,
    /// Whether the machine reads every register here, so the webs it reads
    /// keep the registers' names: an unmodelled instruction.
    pins_all: bool,
    /// The registers a call the text shows reads without passing them: a
    /// call to a thunk that jumps through a register reads that register.
    machine: Vec<usize>,
}

/// The assignment a statement node makes: the token spans of its targets,
/// each running from the target to the `=` after it, and of its right side.
#[derive(Debug, Default, Clone)]
struct Assign {
    /// Each target's first token and its `=` token.
    targets: Vec<(usize, usize)>,
    /// The right side's span, without the `;`.
    rhs: (usize, usize),
}

/// What the tracked variables are and how the text reads them.
#[derive(Debug)]
struct Vars {
    /// The tracked names, by index.
    names: Vec<String>,
    /// Each tracked name's index.
    index: BTreeMap<String, usize>,
    /// Variables this leaves alone: their address is taken, or an
    /// expression assigns them inside itself.
    unsafe_vars: BTreeSet<usize>,
}

impl Vars {
    /// The tracked variable token `k` of a line names, if it names one.
    ///
    /// A field after `->` or `.` and a part of a qualified name are not
    /// variables.
    ///
    /// # Arguments
    ///
    /// * `l` - The line.
    /// * `k` - The token's index.
    fn at(&self, l: &Line<'_>, k: usize) -> Option<usize> {
        let t = l.toks.get(k)?;
        if t.lex != Lex::Name {
            return None;
        }
        let v = *self.index.get(l.word(k))?;
        let qualified = k
            .checked_sub(1)
            .is_some_and(|p| l.is(p, "->") || l.is(p, ".") || l.is(p, "::"))
            || l.is(k + 1, "::");
        (!qualified).then_some(v)
    }

    /// Reads the variables a span of tokens reads, and marks unsafe any it
    /// writes or takes the address of inside an expression.
    ///
    /// # Arguments
    ///
    /// * `l` - The line.
    /// * `span` - The token span.
    /// * `uses` - The reads found, appended to.
    /// * `bad` - The variables found unsafe, appended to.
    fn reads(
        &self,
        l: &Line<'_>,
        span: (usize, usize),
        uses: &mut Vec<(usize, usize)>,
        bad: &mut BTreeSet<usize>,
    ) {
        for k in span.0..span.1 {
            let Some(v) = self.at(l, k) else {
                continue;
            };
            let next = if k + 1 < span.1 { l.word(k + 1) } else { "" };
            let prev = if k > span.0 { l.word(k - 1) } else { "" };
            let operand_before = k.checked_sub(2).is_some_and(|pp| {
                matches!(
                    l.toks.get(pp).map(|t| t.lex),
                    Some(Lex::Name | Lex::Number | Lex::Literal)
                ) || l.is(pp, ")")
                    || l.is(pp, "]")
            });
            let unary_amp = prev == "&" && !operand_before;
            let written = (next == "=" && l.is(k + 1, "="))
                || COMPOUND.contains(&next)
                || matches!(next, "++" | "--")
                || matches!(prev, "++" | "--");
            if unary_amp || written {
                bad.insert(v);
            }
            uses.push((v, k));
        }
    }
}

/// Reads what one node does to the tracked variables.
///
/// # Arguments
///
/// * `vars` - The tracked variables.
/// * `node` - The node.
/// * `l` - Its line, if it reads one.
/// * `bad` - The variables found unsafe, appended to.
///
/// # Returns
///
/// The reads and writes, and the assignment a statement makes.
fn occs(
    vars: &Vars,
    node: &Node,
    l: Option<&Line<'_>>,
    bad: &mut BTreeSet<usize>,
) -> (Occs, Option<Assign>) {
    let mut o = Occs::default();
    match node.form {
        Form::Join | Form::Exit => return (o, None),
        Form::Entry => {
            o.writes_all = true;
            return (o, None);
        }
        Form::Machine => {
            o.reads_all = true;
            o.writes_all = true;
            o.pins_all = true;
            return (o, None);
        }
        Form::Leave | Form::Expr | Form::Statement => {}
    }
    let Some(l) = l else {
        return (o, None);
    };
    let (start, end) = node.span;
    let end = if l.is(end.saturating_sub(1), ";") && end > start {
        end - 1
    } else {
        end
    };
    match node.form {
        Form::Leave => {
            o.reads_all = true;
            vars.reads(l, (start, end), &mut o.uses, bad);
            return (o, None);
        }
        Form::Expr => {
            vars.reads(l, (start, end), &mut o.uses, bad);
            return (o, None);
        }
        Form::Join | Form::Exit | Form::Entry | Form::Machine | Form::Statement => {}
    }
    let mut depth = 0usize;
    let mut eqs: Vec<usize> = Vec::new();
    let mut compound: Option<usize> = None;
    for k in start..end {
        if l.is(k, "(") || l.is(k, "[") {
            depth += 1;
        } else if l.is(k, ")") || l.is(k, "]") {
            depth = depth.saturating_sub(1);
        } else if depth == 0 && l.is(k, "=") {
            eqs.push(k);
        } else if depth == 0 && compound.is_none() && COMPOUND.iter().any(|c| l.is(k, c)) {
            compound = Some(k);
        }
    }
    if let (Some(&last), None) = (eqs.last(), compound) {
        let mut assign = Assign {
            targets: Vec::new(),
            rhs: (last + 1, end),
        };
        let mut from = start;
        for &eq in &eqs {
            assign.targets.push((from, eq));
            match (eq - from == 1).then(|| vars.at(l, from)).flatten() {
                Some(v) => o.defs.push((v, from)),
                None => vars.reads(l, (from, eq), &mut o.uses, bad),
            }
            from = eq + 1;
        }
        vars.reads(l, assign.rhs, &mut o.uses, bad);
        for &(v, _) in &o.defs {
            if o.uses.iter().any(|(u, k)| *u == v && *k < last) {
                bad.insert(v);
            }
        }
        return (o, Some(assign));
    }
    if let (Some(op), true) = (compound, eqs.is_empty()) {
        match (op - start == 1).then(|| vars.at(l, start)).flatten() {
            Some(v) => o.rmw.push((v, start)),
            None => vars.reads(l, (start, op), &mut o.uses, bad),
        }
        vars.reads(l, (op + 1, end), &mut o.uses, bad);
        return (o, None);
    }
    if end - start == 2 && eqs.is_empty() && compound.is_none() {
        let pair = if l.is(start + 1, "++") || l.is(start + 1, "--") {
            vars.at(l, start).map(|v| (v, start))
        } else if l.is(start, "++") || l.is(start, "--") {
            vars.at(l, start + 1).map(|v| (v, start + 1))
        } else {
            None
        };
        if let Some(p) = pair {
            o.rmw.push(p);
            return (o, None);
        }
    }
    for &eq in &eqs {
        if let Some(v) = eq.checked_sub(1).and_then(|p| vars.at(l, p)) {
            bad.insert(v);
        }
    }
    vars.reads(l, (start, end), &mut o.uses, bad);
    (o, None)
}


/// A disjoint-set forest over a variable's definitions and the points it
/// is read at.
#[derive(Debug)]
struct Sets {
    /// Each element's parent.
    parent: Vec<usize>,
}

impl Sets {
    /// A forest of `n` single elements.
    ///
    /// # Arguments
    ///
    /// * `n` - How many elements.
    fn new(n: usize) -> Self {
        Self {
            parent: (0..n).collect(),
        }
    }

    /// The root of an element's set.
    ///
    /// # Arguments
    ///
    /// * `x` - The element.
    fn find(&mut self, mut x: usize) -> usize {
        while let Some(&p) = self.parent.get(x) {
            if p == x {
                break;
            }
            let gp = self.parent.get(p).copied().unwrap_or(p);
            if let Some(slot) = self.parent.get_mut(x) {
                *slot = gp;
            }
            x = gp;
        }
        x
    }

    /// Joins two elements' sets under the smaller root.
    ///
    /// # Arguments
    ///
    /// * `a` - One element.
    /// * `b` - The other.
    fn union(&mut self, a: usize, b: usize) {
        let (ra, rb) = (self.find(a), self.find(b));
        let (lo, hi) = (ra.min(rb), ra.max(rb));
        if let Some(slot) = self.parent.get_mut(hi) {
            *slot = lo;
        }
    }
}

/// One variable's webs: the web of each definition and read.
#[derive(Debug)]
struct Webs {
    /// The forest: element `n` is the value at node `n`'s entry, `N + n`
    /// node `n`'s definition, `2N` the entry's value and `2N + 1` the
    /// machine's.
    sets: Sets,
    /// The node count `N`.
    n: usize,
    /// The roots of webs something reads outside its own compound
    /// assignments.
    read: BTreeSet<usize>,
    /// Whether the variable is live where each node starts.
    live: Vec<bool>,
}

impl Webs {
    /// The web of the value read at node `n`.
    ///
    /// # Arguments
    ///
    /// * `n` - The node.
    fn read_at(&mut self, n: usize) -> usize {
        self.sets.find(n)
    }

    /// The web of the value node `n` defines.
    ///
    /// # Arguments
    ///
    /// * `n` - The node.
    fn def_at(&mut self, n: usize) -> usize {
        self.sets.find(self.n + n)
    }

    /// Tells whether a web is the register itself: the entry's value or
    /// one the machine reads or writes.
    ///
    /// # Arguments
    ///
    /// * `root` - The web's root.
    fn pinned(&mut self, root: usize) -> bool {
        root == self.sets.find(2 * self.n) || root == self.sets.find(2 * self.n + 1)
    }
}

/// Finds one variable's webs over the graph.
///
/// The value a node reads joins every definition reaching it; a value is
/// carried across a node that does not define the variable only where the
/// variable is live, so two definitions join only when some use reads
/// both.
///
/// # Arguments
///
/// * `v` - The variable.
/// * `nodes` - The graph's nodes.
/// * `preds` - Each node's predecessors.
/// * `occs` - What each node reads and writes.
/// * `live_out` - The variables the exit reads.
fn webs_of(
    v: usize,
    nodes: &[Node],
    preds: &[Vec<usize>],
    occs: &[Occs],
    live_out: &BTreeSet<usize>,
) -> Webs {
    let n = nodes.len();
    let reads = |i: usize| {
        occs.get(i).is_some_and(|o| {
            o.reads_all
                || o.machine.contains(&v)
                || o.uses.iter().chain(&o.rmw).any(|(u, _)| *u == v)
        }) || (i == EXIT && live_out.contains(&v))
    };
    let writes = |i: usize| {
        occs.get(i)
            .is_some_and(|o| o.writes_all || o.defs.iter().chain(&o.rmw).any(|(d, _)| *d == v))
    };
    let uses: Vec<bool> = (0..n).map(reads).collect();
    let defs: Vec<bool> = (0..n).map(writes).collect();
    let mut live = uses;
    let mut work: Vec<usize> = (0..n).filter(|&i| live[i]).collect();
    while let Some(i) = work.pop() {
        for &p in preds.get(i).map_or(&[][..], Vec::as_slice) {
            if !live[p] && !defs[p] {
                live[p] = true;
                work.push(p);
            }
        }
    }
    let (entry, machine) = (2 * n, 2 * n + 1);
    let mut sets = Sets::new(2 * n + 2);
    sets.union(n, entry);
    let mut read = BTreeSet::new();
    for (i, _) in live.iter().enumerate().filter(|(_, l)| **l) {
        for &p in preds.get(i).map_or(&[][..], Vec::as_slice) {
            if defs[p] {
                sets.union(i, n + p);
            } else {
                sets.union(i, p);
            }
        }
    }
    for (i, o) in occs.iter().enumerate() {
        if o.rmw.iter().any(|(r, _)| *r == v) {
            sets.union(n + i, i);
        }
        if o.pins_all || o.machine.contains(&v) {
            sets.union(i, machine);
        }
        if o.writes_all && nodes.get(i).is_some_and(|x| x.form == Form::Machine) {
            sets.union(n + i, machine);
        }
    }
    if live_out.contains(&v) {
        sets.union(EXIT, machine);
    }
    for i in 0..n {
        let real = occs.get(i).is_some_and(|o| {
            o.reads_all || o.machine.contains(&v) || o.uses.iter().any(|(u, _)| *u == v)
        }) || (i == EXIT && live_out.contains(&v));
        if real {
            read.insert(sets.find(i));
        }
    }
    Webs {
        sets,
        n,
        read,
        live,
    }
}


/// The parts of a function's text.
#[derive(Debug)]
pub(super) struct Parts<'t> {
    /// The lines before the body: header comments and declarations.
    pub(super) head: Vec<&'t str>,
    /// Where the declarations start in `head`.
    pub(super) decls: usize,
    /// The body's lines.
    pub(super) body: Vec<&'t str>,
}

/// Splits a text into header, declarations and body.
///
/// # Arguments
///
/// * `text` - A decompiled function.
///
/// # Returns
///
/// The parts, or `None` when the text has no blank line before a body.
pub(super) fn parts(text: &str) -> Option<Parts<'_>> {
    let lines: Vec<&str> = text.lines().collect();
    let decls = header_len(&lines);
    let blank_at = decls
        + lines
            .get(decls..)?
            .iter()
            .position(|l| l.trim().is_empty())?;
    Some(Parts {
        head: lines.get(..blank_at)?.to_vec(),
        decls,
        body: lines.get(blank_at + 1..)?.to_vec(),
    })
}

/// The names the declarations declare, each with its type; a name
/// declared twice is left out.
///
/// # Arguments
///
/// * `decls` - The declaration lines.
///
/// # Returns
///
/// Name to type, a pointer's stars written after the type (`void *`).
fn declared(decls: &[&str]) -> BTreeMap<String, String> {
    let mut out: BTreeMap<String, String> = BTreeMap::new();
    let mut twice: BTreeSet<String> = BTreeSet::new();
    for d in decls {
        let Some((ty, items)) = declaration(d) else {
            continue;
        };
        for (stars, name) in items {
            let full = if stars.is_empty() {
                ty.to_owned()
            } else {
                format!("{ty} {stars}")
            };
            if out.insert(name.to_owned(), full).is_some() {
                twice.insert(name.to_owned());
            }
        }
    }
    out.retain(|n, _| !twice.contains(n));
    out
}

/// Reads a declaration line: its type and its items, each its pointer
/// stars and its name.
///
/// # Arguments
///
/// * `line` - One line of the declarations.
///
/// # Returns
///
/// The type and the items, or `None` for a line that is not a plain
/// declaration (a comment, a global with its address).
pub(super) fn declaration(line: &str) -> Option<(&str, Vec<(&str, &str)>)> {
    let t = line.strip_suffix(';')?;
    if t.contains(['/', '=', '(', '[']) || t.starts_with(' ') {
        return None;
    }
    let mut chunks = t.split(", ");
    let (ty, first) = chunks.next()?.rsplit_once(' ')?;
    let mut items = Vec::new();
    for item in std::iter::once(first).chain(chunks) {
        let name = item.trim_start_matches('*');
        if !is_ident(name) {
            return None;
        }
        items.push((item.get(..item.len() - name.len())?, name));
    }
    Some((ty, items))
}

/// The type a function's `// signature:` line says it returns.
///
/// # Arguments
///
/// * `head` - The header lines.
fn return_type(head: &[&str]) -> Option<String> {
    let sig = head.iter().find_map(|h| h.strip_prefix("// signature: "))?;
    let (ret, name) = sig.split_once('(')?.0.rsplit_once(' ')?;
    let stars = name.len() - name.trim_start_matches('*').len();
    Some(if stars == 0 {
        ret.to_owned()
    } else {
        format!("{ret} {}", "*".repeat(stars))
    })
}

/// Tells whether a name is one this pass gave a web: `var<n>`.
///
/// # Arguments
///
/// * `name` - The name.
pub(super) fn is_var_name(name: &str) -> bool {
    name.strip_prefix(PREFIX).is_some_and(|d| {
        !d.is_empty() && !d.starts_with('0') && d.bytes().all(|b| b.is_ascii_digit())
    })
}

/// Tells whether a name is a register this pass splits: every one the
/// lifters name but the stack pointer.
///
/// # Arguments
///
/// * `name` - The name.
fn splits(name: &str) -> bool {
    is_register_name(name) && !matches!(name, "rsp" | "esp")
}

/// Tells whether a name is a type word a cast or declaration spells.
///
/// # Arguments
///
/// * `w` - The word.
fn type_word(w: &str) -> bool {
    narrow_type(w).is_some()
        || matches!(
            w,
            "uint64_t"
                | "int64_t"
                | "uint128_t"
                | "uintptr_t"
                | "intptr_t"
                | "size_t"
                | "char"
                | "short"
                | "int"
                | "long"
                | "unsigned"
                | "signed"
                | "const"
                | "void"
                | "float"
                | "double"
                | "bool"
                | "wchar_t"
        )
}

/// Tells whether a type is a floating one.
///
/// # Arguments
///
/// * `ty` - The type.
fn floating(ty: &str) -> bool {
    matches!(ty, "float" | "double" | "long double" | "uint128_t")
}

/// Gives every web of a register its own variable, drops the definitions
/// nothing reads, and folds the single-use temporaries and the constants
/// it then can.
///
/// See the module documentation for what keeps a register's name.
///
/// # Arguments
///
/// * `text` - A decompiled function: header, declarations, a blank line,
///   the body.
///
/// # Returns
///
/// The text with webs as variables, or unchanged when it holds nothing to
/// split or a shape this does not read.
pub(super) fn split_webs(text: &str) -> String {
    let mut out = split(text).unwrap_or_else(|| text.to_owned());
    for _ in 0..FOLDS {
        match fold(&out) {
            Some(next) => out = next,
            None => break,
        }
    }

    if out == text {
        return out;
    }
    renumber(&out, text)
}

/// Most rounds of folding: a fold can leave its use a single-use
/// temporary in turn.
const FOLDS: usize = 6;

/// Most statements a fold carries a right side past to its one read.
const REACH: usize = 8;

/// [`split_webs`] before the folding, `None` where the text stays as it is.
///
/// # Arguments
///
/// * `text` - A decompiled function.
fn split(text: &str) -> Option<String> {
    let mut t = Text::read(text, splits)?;
    for _ in 0..ROUNDS {
        if !t.drop_dead() {
            break;
        }
    }
    t.rename(text.ends_with('\n'))
}

/// One round of folding: each single-use temporary into its use, each
/// constant into the uses that convert it.
///
/// # Arguments
///
/// * `text` - A decompiled function, its webs split.
///
/// # Returns
///
/// The folded text, or `None` when nothing folds.
/// Tells whether a condition's line short-circuits before token `k`: a
/// `&&` or `||` ahead of the use, at any depth, can skip evaluating it.
///
/// # Arguments
///
/// * `l` - The line, an `if (` or `while (` condition expected.
/// * `k` - The use's token index.
fn short_circuits_before(l: &Line<'_>, k: usize) -> bool {
    if !matches!(l.word(0), "if" | "while") {
        return false;
    }
    l.toks
        .iter()
        .take(k)
        .any(|t| t.lex == Lex::Punct && matches!(l.text.get(t.at..t.end), Some("&&" | "||")))
}

/// Folds the single-use definitions it can into their reads, and the
/// copies whose sources read the same.
///
/// # Arguments
///
/// * `text` - A decompiled function.
///
/// # Returns
///
/// The folded text, or `None` when nothing folds.
fn fold(text: &str) -> Option<String> {
    let t = Text::read(text, |n| is_var_name(n) || splits(n))?;
    let ret = return_type(&t.parts.head);
    let mut plans: Vec<Plan> = Vec::new();
    for &v in &t.tracked {
        let Some(ty) = t.vars.names.get(v).and_then(|n| t.types.get(n)) else {
            continue;
        };
        for (def, uses) in t.single_def_webs(v) {
            plans.extend(t.plan(def, &uses, ty, ret.as_deref()));
        }
    }
    plans.extend(t.merges());
    let mut edits: BTreeMap<usize, Vec<(usize, usize, String)>> = BTreeMap::new();
    let mut gone: BTreeSet<usize> = BTreeSet::new();
    let mut touched: BTreeSet<usize> = BTreeSet::new();
    for plan in plans {
        let lines: BTreeSet<usize> = std::iter::once(plan.line)
            .chain(plan.uses.iter().map(|(line, ..)| *line))
            .collect();
        if !touched.is_disjoint(&lines) {
            continue;
        }
        touched.extend(&lines);
        match plan.cut {
            Some((at, end)) => edits
                .entry(plan.line)
                .or_default()
                .push((at, end, String::new())),
            None => {
                gone.insert(plan.line);
            }
        }
        for (line, at, end, with) in plan.uses {
            edits.entry(line).or_default().push((at, end, with));
        }
    }
    if touched.is_empty() {
        return None;
    }
    Some(t.respell(&mut edits, &gone, &BTreeMap::new(), text.ends_with('\n')))
}

/// Numbers the variables this pass made `var1` up in the order the body
/// first names them, closing the gaps the folds left.
///
/// # Arguments
///
/// * `text` - The pass's output.
/// * `before` - Its input, whose own names are left alone.
///
/// # Returns
///
/// The text renumbered.
fn renumber(text: &str, before: &str) -> String {
    let theirs = names_in(before.lines());
    let Some(p) = parts(text) else {
        return text.to_owned();
    };
    let mut order: Vec<&str> = Vec::new();
    for w in names_in_order(&p.body) {
        if is_var_name(w) && !theirs.contains(w) && !order.contains(&w) {
            order.push(w);
        }
    }
    let mut map: BTreeMap<&str, String> = BTreeMap::new();
    let mut next = 1usize;
    for w in &order {
        let name = loop {
            let cand = format!("{PREFIX}{next}");
            next += 1;
            if !theirs.contains(cand.as_str()) {
                break cand;
            }
        };
        if name != *w {
            map.insert(w, name);
        }
    }
    if map.is_empty() {
        return text.to_owned();
    }
    let respelled = |line: &str| {
        let mut out = line.to_owned();
        for t in lex(line).iter().rev() {
            if let Some(new) = line.get(t.at..t.end).and_then(|w| map.get(w)) {
                out.replace_range(t.at..t.end, new);
            }
        }
        out
    };
    let mut out: Vec<String> = p
        .head
        .iter()
        .take(p.decls)
        .map(|l| (*l).to_owned())
        .collect();
    for line in p.head.iter().skip(p.decls) {
        let Some((ty, items)) = declaration(line) else {
            out.push(respelled(line));
            continue;
        };
        let mut mine: Vec<(usize, String)> = Vec::new();
        let mut rest: Vec<String> = Vec::new();
        for (stars, name) in items {
            let new = map.get(name).map_or(name, String::as_str);
            match new
                .strip_prefix(PREFIX)
                .and_then(|n| n.parse::<usize>().ok())
            {
                Some(n) if order.contains(&name) => mine.push((n, format!("{stars}{new}"))),
                Some(_) | None => rest.push(format!("{stars}{new}")),
            }
        }
        mine.sort_unstable();
        let all: Vec<String> = mine.into_iter().map(|(_, n)| n).chain(rest).collect();
        out.push(format!("{ty} {};", all.join(", ")));
    }
    out.push(String::new());
    out.extend(p.body.iter().map(|l| respelled(l)));
    let mut joined = out.join("\n");
    if text.ends_with('\n') {
        joined.push('\n');
    }
    joined
}

/// The identifiers of some lines in the order they first appear.
///
/// # Arguments
///
/// * `lines` - The lines.
fn names_in_order<'t>(lines: &[&'t str]) -> Vec<&'t str> {
    let mut out = Vec::new();
    for l in lines {
        for t in lex(l) {
            if t.lex == Lex::Name
                && let Some(w) = l.get(t.at..t.end)
            {
                out.push(w);
            }
        }
    }
    out
}

/// A fold: what of the definition's line goes and each use's new spelling.
#[derive(Debug)]
struct Plan {
    /// The definition's line.
    line: usize,
    /// The bytes of it that go, `None` for the whole line.
    cut: Option<(usize, usize)>,
    /// Each use: its line, its byte span and what replaces it.
    uses: Vec<(usize, usize, usize, String)>,
}

/// Where a use stands, which says what a fold may put there.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Place {
    /// `return v;`: converted to the return type.
    Return,
    /// `x = v;`: converted to the target's type.
    Rhs,
    /// A whole argument of a call, the callee's name at this token.
    Arg(usize),
    /// A whole `if` condition, `if (v)`.
    Truth,
    /// `!v` as a whole `if` condition.
    Not,
    /// `v == K` or `v != K` against a small literal, in an `if`.
    Compare,
}

/// A text read for this pass: its graph, its variables and what each node
/// does to them.
#[derive(Debug)]
struct Text<'t> {
    /// The text's parts.
    parts: Parts<'t>,
    /// The body's lines and their tokens.
    lines: Vec<Line<'t>>,
    /// The control flow.
    graph: Graph,
    /// Each node's predecessors.
    preds: Vec<Vec<usize>>,
    /// The tracked variables.
    vars: Vars,
    /// The variables split, the unsafe ones left out.
    tracked: Vec<usize>,
    /// What each node reads and writes.
    occs: Vec<Occs>,
    /// The assignment each statement node makes.
    assigns: Vec<Option<Assign>>,
    /// The variables the exit reads.
    live_out: BTreeSet<usize>,
    /// Every declared name's type.
    types: BTreeMap<String, String>,
    /// The nodes whose line goes.
    dropped: BTreeSet<usize>,
    /// The assignment targets that go: node and token.
    gone: BTreeSet<(usize, usize)>,
}

/// One tracked token in the final text: where it is and its web.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
struct Seen {
    /// The body line.
    line: usize,
    /// The token's index in the line.
    tok: usize,
    /// The variable.
    var: usize,
    /// The web's root.
    root: usize,
    /// Whether the web keeps the register's name.
    pinned: bool,
}

impl<'t> Text<'t> {
    /// Reads a text: its parts, its graph and what each node does to the
    /// declared names `track` accepts.
    ///
    /// # Arguments
    ///
    /// * `text` - A decompiled function.
    /// * `track` - Which declared names are variables to analyse.
    ///
    /// # Returns
    ///
    /// The reading, or `None` when the text has nothing to track, holds a
    /// shape this does not read, or is past [`WORK_MAX`].
    fn read(text: &'t str, track: fn(&str) -> bool) -> Option<Self> {
        let parts = parts(text)?;
        let types = declared(parts.head.get(parts.decls..)?);
        let names: Vec<String> = types.keys().filter(|n| track(n)).cloned().collect();
        if names.is_empty() {
            return None;
        }
        let lines: Vec<Line<'t>> = parts
            .body
            .iter()
            .map(|t| Line {
                text: t,
                toks: lex(t),
            })
            .collect();
        let blanked: Vec<String> = parts
            .body
            .iter()
            .map(|l| {
                if l.trim_start().starts_with("/* asm") {
                    "__asm;".to_owned()
                } else {
                    blank(l)
                }
            })
            .collect();
        let stmts = statements(&blanked, 0).ok()?;
        let mut graph = Graph::default();
        graph.add(None, (0, 0), Form::Entry);
        graph.add(None, (0, 0), Form::Exit);
        let outs = graph.run(&stmts, vec![0], None, None, &lines)?;
        graph.link(&outs, EXIT);
        for (from, addr) in std::mem::take(&mut graph.gotos) {
            let to = *graph.labels.get(&addr)?;
            graph.link(&[from], to);
        }
        if graph.nodes.len().saturating_mul(names.len()) > WORK_MAX {
            return None;
        }
        let mut vars = Vars {
            index: names
                .iter()
                .enumerate()
                .map(|(i, n)| (n.clone(), i))
                .collect(),
            names,
            unsafe_vars: BTreeSet::new(),
        };
        let mut bad = BTreeSet::new();
        let read: Vec<(Occs, Option<Assign>)> = graph
            .nodes
            .iter()
            .map(|n| occs(&vars, n, n.line.and_then(|i| lines.get(i)), &mut bad))
            .collect();
        vars.unsafe_vars = bad;
        let (mut occs_of, assigns): (Vec<Occs>, Vec<Option<Assign>>) = read.into_iter().unzip();
        for o in &mut occs_of {
            o.defs.retain(|(v, _)| !vars.unsafe_vars.contains(v));
            o.rmw.retain(|(v, _)| !vars.unsafe_vars.contains(v));
            o.uses.retain(|(v, _)| !vars.unsafe_vars.contains(v));
        }
        let live_out: BTreeSet<usize> = parts
            .head
            .iter()
            .filter_map(|h| {
                h.strip_prefix("// hands back ")
                    .and_then(|r| r.split_once(':'))
                    .and_then(|(reg, _)| vars.index.get(reg.trim()).copied())
            })
            .collect();
        for (thunk, reg) in parts.head.iter().filter_map(|h| {
            let (name, rest) = h
                .strip_prefix("// note: ")?
                .split_once(" only jumps through ")?;
            let reg = vars.index.get(rest.split_once(':')?.0)?;
            Some((format!("{name}("), *reg))
        }) {
            for (node, o) in graph.nodes.iter().zip(&mut occs_of) {
                if node
                    .line
                    .and_then(|i| lines.get(i))
                    .is_some_and(|l| l.text.contains(&thunk))
                {
                    o.machine.push(reg);
                }
            }
        }
        let mut preds: Vec<Vec<usize>> = vec![Vec::new(); graph.nodes.len()];
        for (i, n) in graph.nodes.iter().enumerate() {
            for &s in &n.succ {
                if let Some(ps) = preds.get_mut(s) {
                    ps.push(i);
                }
            }
        }
        let tracked: Vec<usize> = (0..vars.names.len())
            .filter(|v| !vars.unsafe_vars.contains(v))
            .collect();
        Some(Self {
            parts,
            lines,
            graph,
            preds,
            vars,
            tracked,
            occs: occs_of,
            assigns,
            live_out,
            types,
            dropped: BTreeSet::new(),
            gone: BTreeSet::new(),
        })
    }

    /// The webs of one variable over what the nodes still do.
    ///
    /// # Arguments
    ///
    /// * `v` - The variable.
    fn webs(&self, v: usize) -> Webs {
        webs_of(
            v,
            &self.graph.nodes,
            &self.preds,
            &self.occs,
            &self.live_out,
        )
    }

    /// Drops one round of definitions nothing reads.
    ///
    /// A pure line whose every target is dead goes; a lone call keeps its
    /// call and loses its targets (`f(x);`); a chain loses the dead
    /// targets and keeps the rest. A compound assignment to a dead web goes
    /// when its line is pure. A statement inside a one-line `if` or after
    /// a `case` label keeps its line.
    ///
    /// # Returns
    ///
    /// Whether anything was dropped, which can leave more dead.
    fn drop_dead(&mut self) -> bool {
        let mut changed = false;
        for at in 0..self.tracked.len() {
            let Some(&v) = self.tracked.get(at) else {
                continue;
            };
            let mut w = self.webs(v);
            for (i, node) in self.graph.nodes.iter().enumerate() {
                let Some(l) = node.line.and_then(|x| self.lines.get(x)) else {
                    continue;
                };
                let Some(o) = self.occs.get(i) else {
                    continue;
                };
                let whole = node.span.0 == 0;
                let dead = {
                    let r = w.def_at(i);
                    !w.read.contains(&r)
                };
                let dead_defs: Vec<usize> = o
                    .defs
                    .iter()
                    .filter(|(d, _)| *d == v && dead)
                    .map(|(_, k)| *k)
                    .collect();
                let dead_rmw = dead && o.rmw.iter().any(|(d, _)| *d == v);
                let mut drop_line = false;
                if let (false, Some(a)) = (
                    dead_defs.is_empty(),
                    self.assigns.get(i).and_then(Option::as_ref),
                ) {
                    let rhs = span_text(l, a.rhs);
                    let pure = !impure(rhs) || second_result(rhs);
                    let left = a
                        .targets
                        .iter()
                        .filter(|(t, _)| !self.gone.contains(&(i, *t)))
                        .count();
                    let all = left == dead_defs.len();
                    if all && pure && whole {
                        drop_line = true;
                    } else if !all || (!pure && lone_call(rhs)) {
                        self.gone.extend(dead_defs.iter().map(|k| (i, *k)));
                        if let Some(o) = self.occs.get_mut(i) {
                            o.defs.retain(|(d, k)| !(*d == v && dead_defs.contains(k)));
                        }
                        changed = true;
                    }
                } else if dead_rmw && whole && !impure(span_text(l, node.span)) {
                    drop_line = true;
                }
                if drop_line {
                    self.dropped.insert(i);
                    if let Some(o) = self.occs.get_mut(i) {
                        *o = Occs::default();
                    }
                    changed = true;
                }
            }
        }
        changed
    }

    /// Lists every tracked token left in the text with its web, in text
    /// order.
    fn seen(&self) -> Vec<Seen> {
        let mut seen: Vec<Seen> = Vec::new();
        for &v in &self.tracked {
            let mut w = self.webs(v);
            for (i, o) in self.occs.iter().enumerate() {
                let Some(line) = self.graph.nodes.get(i).and_then(|n| n.line) else {
                    continue;
                };
                let defs = o
                    .defs
                    .iter()
                    .filter(|(x, _)| *x == v)
                    .map(|(_, k)| (*k, true));
                let reads = o
                    .rmw
                    .iter()
                    .chain(&o.uses)
                    .filter(|(x, _)| *x == v)
                    .map(|(_, k)| (*k, false));
                for (tok, def) in defs.chain(reads).collect::<Vec<_>>() {
                    let root = if def { w.def_at(i) } else { w.read_at(i) };
                    let pinned = w.pinned(root);
                    seen.push(Seen {
                        line,
                        tok,
                        var: v,
                        root,
                        pinned,
                    });
                }
            }
        }
        seen.sort_unstable();
        seen
    }

    /// Spells the settled webs: each web the entry and the machine do not
    /// pin takes a new name, the dead lines and targets go, and the
    /// declarations follow.
    ///
    /// # Arguments
    ///
    /// * `newline` - Whether the text ends in a newline.
    ///
    /// # Returns
    ///
    /// The new text, or `None` when nothing changes.
    fn rename(&self, newline: bool) -> Option<String> {
        let seen = self.seen();
        let mut taken: BTreeSet<&str> = BTreeSet::new();
        for l in &self.lines {
            for (k, t) in l.toks.iter().enumerate() {
                if t.lex == Lex::Name {
                    taken.insert(l.word(k));
                }
            }
        }
        for h in &self.parts.head {
            taken.extend(tokens(h));
        }
        let mut named: BTreeMap<(usize, usize), (usize, String)> = BTreeMap::new();
        let mut next = 1usize;
        for s in &seen {
            if s.pinned || named.contains_key(&(s.var, s.root)) {
                continue;
            }
            let (number, name) = loop {
                let cand = format!("{PREFIX}{next}");
                next += 1;
                if !taken.contains(cand.as_str()) {
                    break (next - 1, cand);
                }
            };
            named.insert((s.var, s.root), (number, name));
        }
        if named.is_empty() && self.dropped.is_empty() && self.gone.is_empty() {
            return None;
        }
        let mut edits: BTreeMap<usize, Vec<(usize, usize, String)>> = BTreeMap::new();
        for s in &seen {
            if let (Some((_, name)), Some(t)) = (
                named.get(&(s.var, s.root)),
                self.lines.get(s.line).and_then(|l| l.toks.get(s.tok)),
            ) {
                edits
                    .entry(s.line)
                    .or_default()
                    .push((t.at, t.end, name.clone()));
            }
        }
        for &(i, k) in &self.gone {
            let (Some(line), Some(a)) = (
                self.graph.nodes.get(i).and_then(|n| n.line),
                self.assigns.get(i).and_then(Option::as_ref),
            ) else {
                continue;
            };
            let Some(&(_, eq)) = a.targets.iter().find(|(t, _)| *t == k) else {
                continue;
            };
            let Some(l) = self.lines.get(line) else {
                continue;
            };
            if let (Some(from), Some(to)) = (l.toks.get(k), l.toks.get(eq + 1)) {
                edits
                    .entry(line)
                    .or_default()
                    .push((from.at, to.at, String::new()));
            }
        }
        let gone_lines: BTreeSet<usize> = self
            .dropped
            .iter()
            .filter_map(|&i| self.graph.nodes.get(i).and_then(|n| n.line))
            .collect();
        let mut fresh_of: BTreeMap<String, Vec<(usize, String)>> = BTreeMap::new();
        for ((v, _), (number, name)) in &named {
            if let Some(var) = self.vars.names.get(*v) {
                fresh_of
                    .entry(var.clone())
                    .or_default()
                    .push((*number, name.clone()));
            }
        }
        Some(self.respell(&mut edits, &gone_lines, &fresh_of, newline))
    }

    /// Writes the text out with byte edits on its body lines, some lines
    /// gone, and the declarations rewritten to match: a variable split into
    /// webs declares their names at its type, and a name the body no
    /// longer mentions is no longer declared.
    ///
    /// # Arguments
    ///
    /// * `edits` - Per body line, byte spans and what replaces each.
    /// * `gone` - The body lines that go.
    /// * `fresh_of` - Per split variable, its webs' numbers and names.
    /// * `newline` - Whether the text ends in a newline.
    fn respell(
        &self,
        edits: &mut BTreeMap<usize, Vec<(usize, usize, String)>>,
        gone: &BTreeSet<usize>,
        fresh_of: &BTreeMap<String, Vec<(usize, String)>>,
        newline: bool,
    ) -> String {
        let mut body: Vec<String> = Vec::with_capacity(self.lines.len());
        for (i, l) in self.lines.iter().enumerate() {
            if gone.contains(&i) {
                continue;
            }
            let mut text = l.text.to_owned();
            if let Some(es) = edits.get_mut(&i) {
                es.sort_unstable_by_key(|e| std::cmp::Reverse(e.0));
                for (at, end, with) in es.iter() {
                    if text.get(*at..*end).is_some() {
                        text.replace_range(*at..*end, with);
                    }
                }
            }
            body.push(text);
        }
        let before = names_in(self.parts.body.iter().copied());
        let after = names_in(body.iter().map(String::as_str));
        let gone_name = |n: &str| before.contains(n) && !after.contains(n);
        let mut out: Vec<String> = self
            .parts
            .head
            .iter()
            .take(self.parts.decls)
            .map(|l| (*l).to_owned())
            .collect();
        for line in self.parts.head.iter().skip(self.parts.decls) {
            let global = line
                .split_once("; //")
                .and_then(|(decl, _)| decl.rsplit(' ').next())
                .map(|n| n.trim_start_matches('*'));
            if global.is_some_and(gone_name) {
                continue;
            }
            let Some((ty, items)) = declaration(line) else {
                out.push((*line).to_owned());
                continue;
            };
            let mut fresh: Vec<(usize, String)> = Vec::new();
            let mut kept: Vec<String> = Vec::new();
            for (stars, name) in items {
                for (number, n) in fresh_of.get(name).map_or(&[][..], Vec::as_slice) {
                    if after.contains(n.as_str()) {
                        fresh.push((*number, format!("{stars}{n}")));
                    }
                }
                if !gone_name(name) {
                    kept.push(format!("{stars}{name}"));
                }
            }
            fresh.sort_unstable();
            let all: Vec<String> = fresh.into_iter().map(|(_, n)| n).chain(kept).collect();
            if !all.is_empty() {
                out.push(format!("{ty} {};", all.join(", ")));
            }
        }
        out.push(String::new());
        out.extend(body);
        let mut joined = out.join("\n");
        if newline {
            joined.push('\n');
        }
        joined
    }

    /// The webs of a variable with exactly one definition, a plain one, and
    /// no compound assignment, which the machine and the entry do not pin.
    ///
    /// # Arguments
    ///
    /// * `v` - The variable.
    ///
    /// # Returns
    ///
    /// Each web's defining node and its reads: node and token.
    fn single_def_webs(&self, v: usize) -> Vec<(usize, Vec<(usize, usize)>)> {
        /// One web's definitions and reads, as found.
        #[derive(Debug, Default)]
        struct Web {
            /// The nodes defining it.
            defs: Vec<usize>,
            /// Its reads: node and token.
            uses: Vec<(usize, usize)>,
            /// Whether a compound assignment writes it.
            rmw: bool,
        }
        let mut w = self.webs(v);
        let mut webs: BTreeMap<usize, Web> = BTreeMap::new();
        for (i, o) in self.occs.iter().enumerate() {
            for _ in o.defs.iter().filter(|(x, _)| *x == v) {
                let r = w.def_at(i);
                webs.entry(r).or_default().defs.push(i);
            }
            if o.rmw.iter().any(|(x, _)| *x == v) {
                let r = w.read_at(i);
                webs.entry(r).or_default().rmw = true;
            }
            for &(_, k) in o.uses.iter().filter(|(x, _)| *x == v) {
                let r = w.read_at(i);
                webs.entry(r).or_default().uses.push((i, k));
            }
        }
        webs.into_iter()
            .filter_map(|(root, web)| {
                let [def] = web.defs.as_slice() else {
                    return None;
                };
                (!web.rmw && !w.pinned(root) && !web.uses.is_empty()).then_some((*def, web.uses))
            })
            .collect()
    }

    /// The statements control runs between `d` and `u` when the code
    /// runs straight from one to the other: each step the only way out of
    /// the last and the only way into the next, joins passed, unless the
    /// right side calls: a call a block's jumps lead around is a statement
    /// of the block the binary has it in, so a calling right side crosses
    /// no join.
    ///
    /// # Arguments
    ///
    /// * `d` - The node control leaves.
    /// * `u` - The node control reaches.
    /// * `calls` - Whether the right side being carried calls.
    ///
    /// # Returns
    ///
    /// The nodes in between, none of them joins, or `None` when control
    /// does not run straight from `d` to `u` within [`REACH`] statements,
    /// or a calling right side would cross a join.
    fn between(&self, d: usize, u: usize, calls: bool) -> Option<Vec<usize>> {
        let mut out = Vec::new();
        let mut cur = d;
        for _ in 0..self.graph.nodes.len() {
            let [s] = self.graph.nodes.get(cur)?.succ.as_slice() else {
                return None;
            };
            if self.preds.get(*s)?.len() != 1 {
                return None;
            }
            if *s == u {
                return Some(out);
            }
            match self.graph.nodes.get(*s)?.form {
                Form::Join if !calls => {}
                Form::Join => return None,
                _ if out.len() == REACH => return None,
                _ => out.push(*s),
            }
            cur = *s;
        }
        None
    }

    /// Tells whether a fold may carry a right side past node `m`: it writes
    /// no variable the right side reads, and nothing it does changes what
    /// the right side computes or runs out of order with it.
    ///
    /// # Arguments
    ///
    /// * `m` - The statement passed.
    /// * `reads` - The variables the right side reads.
    /// * `rhs` - What evaluating the right side does.
    fn passes(&self, m: usize, reads: &BTreeSet<usize>, rhs: Effects) -> bool {
        let (Some(node), Some(o)) = (self.graph.nodes.get(m), self.occs.get(m)) else {
            return false;
        };
        let Some(l) = node.line.and_then(|i| self.lines.get(i)) else {
            return false;
        };
        if node.form != Form::Statement
            || node.span.0 != 0
            || o.defs.iter().chain(&o.rmw).any(|(v, _)| reads.contains(v))
        {
            return false;
        }
        if rhs == Effects::default() {
            return true;
        }
        let span = trimmed(l, node.span);
        let mut skip = Vec::new();
        let stores = match self.assigns.get(m).and_then(Option::as_ref) {
            Some(a) => {
                let mut stores = false;
                for &(from, eq) in &a.targets {
                    skip.push(eq);
                    if eq == from + 1 && self.vars.at(l, from).is_some() {
                        skip.push(from);
                    } else {
                        stores = true;
                    }
                }
                stores
            }
            None => {
                o.rmw.is_empty()
                    && (span.0..span.1).any(|k| {
                        COMPOUND.iter().any(|c| l.is(k, c)) || l.is(k, "++") || l.is(k, "--")
                    })
            }
        };
        let here = self.effects(l, span, &skip);
        if rhs.calls {
            !(stores || here.calls || here.loads)
        } else {
            !(stores || here.calls)
        }
    }

    /// Plans a fold of a web defined once at node `d`.
    ///
    /// A constant (a literal from 0 to `INT_MAX` the variable's type holds)
    /// replaces every read when each converts the value whole: a returned
    /// value, an assignment's right side, a call's argument. Any other
    /// right side folds into its one read when control runs straight from
    /// the definition to the read past statements that cannot change what
    /// it computes ([`Text::passes`]), in a place where the value converts
    /// the same ([`Text::converts`]), and nothing evaluated beside it on
    /// the read's line could run out of order with it ([`Text::effects`]):
    /// a call folds beside no load and no other call, a load beside no
    /// call. A second result (`f__rdx(..)`) stays on its own line, right
    /// after the call it is the second half of.
    ///
    /// # Arguments
    ///
    /// * `d` - The defining node.
    /// * `uses` - The web's reads: node and token.
    /// * `ty` - The variable's type.
    /// * `ret` - The function's return type, if the signature says.
    ///
    /// # Returns
    ///
    /// The fold, or `None` when none is safe.
    fn plan(&self, d: usize, uses: &[(usize, usize)], ty: &str, ret: Option<&str>) -> Option<Plan> {
        let node = self.graph.nodes.get(d)?;
        let line = node.line?;
        let l = self.lines.get(line)?;
        let a = self.assigns.get(d)?.as_ref()?;
        let rhs = span_text(l, a.rhs);
        if node.form != Form::Statement
            || node.span.0 != 0
            || a.targets.len() != 1
            || rhs.contains("__rdx(")
        {
            return None;
        }
        let literal = (a.rhs.1 == a.rhs.0 + 1)
            .then(|| l.toks.get(a.rhs.0))
            .flatten()
            .filter(|t| t.lex == Lex::Number)
            .and_then(|_| parse_const(rhs))
            .filter(|v| *v <= 0x7fff_ffff && fits(*v, ty));
        if literal.is_some() {
            let mut out = Vec::with_capacity(uses.len());
            for &(u, k) in uses {
                let place = self.place(u, k)?;
                if !matches!(place, Place::Return | Place::Rhs | Place::Arg(_)) {
                    return None;
                }
                let (ul, t) = self.token(u, k)?;
                out.push((ul, t.at, t.end, rhs.to_owned()));
            }
            return Some(Plan {
                line,
                cut: None,
                uses: out,
            });
        }
        let [(u, k)] = uses else {
            return None;
        };
        let (u, k) = (*u, *k);
        if floating(ty) || self.float_in(l, a.rhs) {
            return None;
        }
        let rhs_does = self.effects(l, a.rhs, &[]);
        let reads: BTreeSet<usize> = self
            .occs
            .get(d)?
            .uses
            .iter()
            .filter(|(_, t)| *t >= a.rhs.0 && *t < a.rhs.1)
            .map(|(v, _)| *v)
            .collect();
        if !self
            .between(d, u, rhs_does.calls)?
            .iter()
            .all(|m| self.passes(*m, &reads, rhs_does))
        {
            return None;
        }
        let place = self.place(u, k)?;
        let un = self.graph.nodes.get(u)?;
        let ul = self.lines.get(un.line?)?;
        if rhs_does.calls
            && matches!(place, Place::Truth | Place::Not | Place::Compare)
            && short_circuits_before(ul, k)
        {
            return None;
        }
        if !self.converts(place, u, ty, ret) {
            return None;
        }
        let un = self.graph.nodes.get(u)?;
        let ul = self.lines.get(un.line?)?;
        let span = trimmed(ul, un.span);
        let mut skip = vec![k];
        if let Place::Arg(callee) = place {
            skip.push(callee);
        }
        if let (Place::Rhs, Some(ua)) = (place, self.assigns.get(u).and_then(Option::as_ref)) {
            for &(from, eq) in &ua.targets {
                skip.push(eq);
                if eq == from + 1 {
                    skip.push(from);
                }
            }
        }
        let beside = self.effects(ul, span, &skip);
        if (rhs_does.calls && (beside.calls || beside.loads)) || (rhs_does.loads && beside.calls) {
            return None;
        }
        let tight = a.rhs.1 == a.rhs.0 + 1 || lone_call(rhs) || {
            l.is(a.rhs.0, "(") && l.closing(a.rhs.0) == Some(a.rhs.1 - 1)
        };
        let with = if matches!(place, Place::Not | Place::Compare) && !tight {
            format!("({rhs})")
        } else {
            rhs.to_owned()
        };
        let t = ul.toks.get(k)?;
        Some(Plan {
            line,
            cut: None,
            uses: vec![(un.line?, t.at, t.end, with)],
        })
    }

    /// Plans merging copies: `a = b;`, where the copy is the only value
    /// `a` ever holds and no write to `b` comes while `a` is live, makes
    /// `a` and `b` one variable, so the copy goes and `a` reads as `b`.
    ///
    /// Only this pass's own variables of one type merge; a register's name
    /// is never spread.
    ///
    /// # Returns
    ///
    /// The merges, at most one per copy line.
    fn merges(&self) -> Vec<Plan> {
        let mut out = Vec::new();
        for (c, node) in self.graph.nodes.iter().enumerate() {
            let (Some(line), Some(a)) = (node.line, self.assigns.get(c).and_then(Option::as_ref))
            else {
                continue;
            };
            let Some(l) = self.lines.get(line) else {
                continue;
            };
            if node.form != Form::Statement || node.span.0 != 0 || a.rhs.1 != a.rhs.0 + 1 {
                continue;
            }
            let Some(b) = self
                .vars
                .at(l, a.rhs.0)
                .filter(|b| self.tracked.contains(b))
            else {
                continue;
            };
            let Some(b_name) = self.vars.names.get(b).filter(|n| is_var_name(n)) else {
                continue;
            };
            let Some(o) = self.occs.get(c) else {
                continue;
            };
            for &(av, tok) in &o.defs {
                if let Some(plan) = self.merge(c, (av, tok), b, b_name, a) {
                    out.push(plan);
                    break;
                }
            }
        }
        out
    }

    /// Plans merging the target `av` of the copy at node `c` into `b`.
    ///
    /// # Arguments
    ///
    /// * `c` - The copy's node.
    /// * `target` - The copied-to variable and its token.
    /// * `b` - The copied variable.
    /// * `b_name` - Its name.
    /// * `copy` - The copy's assignment.
    fn merge(
        &self,
        c: usize,
        target: (usize, usize),
        b: usize,
        b_name: &str,
        copy: &Assign,
    ) -> Option<Plan> {
        let (av, tok) = target;
        let a_name = self.vars.names.get(av)?;
        if av == b
            || !is_var_name(a_name)
            || self.types.get(a_name.as_str()) != self.types.get(b_name)
        {
            return None;
        }
        let defines = |i: usize, v: usize| {
            self.occs
                .get(i)
                .is_some_and(|o| o.writes_all || o.defs.iter().chain(&o.rmw).any(|(x, _)| *x == v))
        };
        let n = self.graph.nodes.len();
        if (1..n).any(|i| i != c && defines(i, av)) {
            return None;
        }
        let mut w = self.webs(av);
        let root = w.def_at(c);
        if w.pinned(root) {
            return None;
        }
        let clash = (0..n).filter(|&m| defines(m, b)).any(|m| {
            self.graph
                .nodes
                .get(m)
                .is_some_and(|x| x.succ.iter().any(|s| w.live.get(*s) == Some(&true)))
        });
        if clash {
            return None;
        }
        let line = self.graph.nodes.get(c)?.line?;
        let l = self.lines.get(line)?;
        let cut = if copy.targets.len() == 1 {
            None
        } else {
            let &(_, eq) = copy.targets.iter().find(|(t, _)| *t == tok)?;
            Some((l.toks.get(tok)?.at, l.toks.get(eq + 1)?.at))
        };
        let mut uses = Vec::new();
        for (i, o) in self.occs.iter().enumerate() {
            for &(_, k) in o.uses.iter().filter(|(x, _)| *x == av) {
                if w.read_at(i) != root {
                    return None;
                }
                let (ul, t) = self.token(i, k)?;
                uses.push((ul, t.at, t.end, b_name.to_owned()));
            }
        }
        Some(Plan { line, cut, uses })
    }

    /// A token of a node's line, with the line's index.
    ///
    /// # Arguments
    ///
    /// * `u` - The node.
    /// * `k` - The token's index.
    fn token(&self, u: usize, k: usize) -> Option<(usize, Tok)> {
        let line = self.graph.nodes.get(u)?.line?;
        Some((line, *self.lines.get(line)?.toks.get(k)?))
    }

    /// Where the read at token `k` of node `u` stands.
    ///
    /// # Arguments
    ///
    /// * `u` - The node.
    /// * `k` - The token's index.
    ///
    /// # Returns
    ///
    /// The place, or `None` for one a fold does not go into.
    fn place(&self, u: usize, k: usize) -> Option<Place> {
        let node = self.graph.nodes.get(u)?;
        let l = self.lines.get(node.line?)?;
        let (s, e) = trimmed(l, node.span);
        let first = l.word(0);
        let lone = e == s + 1 && k == s;
        if node.form == Form::Expr && lone && s > 0 && l.word(s - 1) == "return" {
            return Some(Place::Return);
        }
        if node.form == Form::Statement
            && self
                .assigns
                .get(u)
                .and_then(Option::as_ref)
                .is_some_and(|a| a.rhs == (k, k + 1))
        {
            return Some(Place::Rhs);
        }
        let prev = k.checked_sub(1).filter(|p| *p >= s);
        if prev.is_some_and(|p| l.is(p, "(") || l.is(p, ","))
            && k + 1 < e
            && (l.is(k + 1, ")") || l.is(k + 1, ","))
        {
            let mut depth = 0usize;
            let mut open = None;
            for p in (s..k).rev() {
                if l.is(p, ")") || l.is(p, "]") {
                    depth += 1;
                } else if l.is(p, "(") || l.is(p, "[") {
                    if depth == 0 {
                        open = Some(p);
                        break;
                    }
                    depth -= 1;
                }
            }
            let callee = open
                .filter(|o| l.is(*o, "("))
                .and_then(|o| o.checked_sub(1));
            if let Some(c) = callee.filter(|c| *c >= s)
                && l.toks.get(c).is_some_and(|t| t.lex == Lex::Name)
                && !type_word(l.word(c))
                && !matches!(l.word(c), "sizeof" | "if" | "while" | "return" | "switch")
            {
                return Some(Place::Arg(c));
            }
        }
        if node.form != Form::Expr || first != "if" {
            return None;
        }
        if lone {
            return Some(Place::Truth);
        }
        if e == s + 2 && k == s + 1 && l.is(s, "!") {
            return Some(Place::Not);
        }
        let opens =
            |p: Option<usize>| p.is_none_or(|p| l.is(p, "(") || l.is(p, "&&") || l.is(p, "||"));
        let small = l
            .toks
            .get(k + 2)
            .filter(|t| t.lex == Lex::Number && k + 2 < e)
            .and_then(|_| parse_const(l.word(k + 2)))
            .is_some_and(|v| v <= 0x7fff_ffff);
        let closes = k + 3 >= e || l.is(k + 3, ")") || l.is(k + 3, "&&") || l.is(k + 3, "||");
        ((l.is(k + 1, "==") || l.is(k + 1, "!=")) && small && opens(prev) && closes)
            .then_some(Place::Compare)
    }

    /// Tells whether a value of type `ty` reads the same at `place` as the
    /// right side it was assigned from.
    ///
    /// Assigning to `ty` converts the right side; folding it drops that
    /// conversion. `uint64_t` holds any integer the text computes, wrapped
    /// the way any narrower conversion after it wraps, so a returned value,
    /// an assignment to an integer and a test against zero or a small
    /// literal read the same; a call's argument too, since a run passes
    /// every argument as a machine word. A type exactly the target's
    /// converts the same either way.
    ///
    /// # Arguments
    ///
    /// * `place` - Where the read stands.
    /// * `u` - The reading node.
    /// * `ty` - The variable's type.
    /// * `ret` - The function's return type, if the signature says.
    fn converts(&self, place: Place, u: usize, ty: &str, ret: Option<&str>) -> bool {
        let word = ty == "uint64_t";
        match place {
            Place::Return => ret.is_some_and(|r| r == ty || (word && !floating(r))),
            Place::Rhs => {
                let (Some(a), Some(l)) = (
                    self.assigns.get(u).and_then(Option::as_ref),
                    self.graph
                        .nodes
                        .get(u)
                        .and_then(|n| n.line)
                        .and_then(|i| self.lines.get(i)),
                ) else {
                    return false;
                };
                a.targets.iter().all(|&(from, eq)| {
                    if eq == from + 1 {
                        self.types
                            .get(l.word(from))
                            .is_some_and(|t| t == ty || (word && !floating(t)))
                    } else {
                        word && !self.float_in(l, (from, eq))
                    }
                })
            }
            Place::Arg(_) | Place::Truth | Place::Not | Place::Compare => word,
        }
    }

    /// Tells whether a span of tokens may compute in floating point: a
    /// floating type, variable or literal.
    ///
    /// # Arguments
    ///
    /// * `l` - The line.
    /// * `span` - The token span.
    fn float_in(&self, l: &Line<'_>, span: (usize, usize)) -> bool {
        (span.0..span.1).any(|k| {
            let w = l.word(k);
            floating(w)
                || matches!(w, "NAN" | "INFINITY")
                || self.types.get(w).is_some_and(|t| floating(t))
                || l.toks.get(k).is_some_and(|t| t.lex == Lex::Number)
                    && !w.starts_with("0x")
                    && w.contains(['.', 'e', 'E'])
        })
    }

    /// What evaluating a span of tokens does besides computing: whether it
    /// calls, and whether it reads memory.
    ///
    /// Reading variables, parameters and literals, taking an address,
    /// casting and computing do neither; a load (`*p`, `p->f`, `p[i]`, a
    /// stack slot or a global by name) reads memory.
    ///
    /// # Arguments
    ///
    /// * `l` - The line.
    /// * `span` - The token span.
    /// * `skip` - Tokens left out of the reckoning.
    fn effects(&self, l: &Line<'_>, span: (usize, usize), skip: &[usize]) -> Effects {
        let mut out = Effects::default();
        for k in (span.0..span.1).filter(|k| !skip.contains(k)) {
            let Some(t) = l.toks.get(k) else {
                continue;
            };
            let w = l.word(k);
            match t.lex {
                Lex::Number | Lex::Literal => {}
                Lex::Punct => {
                    let deref =
                        w == "*" && unary(l, k, span.0) && !(l.is(k + 1, ")") || l.is(k + 1, "*"));
                    out.loads |= deref || matches!(w, "->" | "." | "[");
                    let cast = k > 0
                        && (l.is(k - 1, "*")
                            || l.toks.get(k - 1).is_some_and(
                                |p| matches!(p.lex, Lex::Name if type_word(l.word(k - 1))),
                            ));
                    out.calls |= w == ")" && l.is(k + 1, "(") && !cast;
                }
                Lex::Name if l.is(k + 1, "::") => {}
                Lex::Name => {
                    let named = self.vars.index.contains_key(w)
                        || is_param_name(w)
                        || w == "this"
                        || type_word(w)
                        || w.bytes()
                            .all(|b| b.is_ascii_uppercase() || b.is_ascii_digit() || b == b'_')
                        || (k > span.0 && l.is(k - 1, "&") && unary(l, k - 1, span.0));
                    let call = l.is(k + 1, "(") && !type_word(w);
                    out.calls |= call;
                    out.loads |= !named && !call;
                }
            }
        }
        out
    }
}

/// What evaluating an expression does besides computing a value.
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
struct Effects {
    /// It calls a function, which may read and write any memory.
    calls: bool,
    /// It reads memory.
    loads: bool,
}

/// Tells whether the operator at token `k` is a prefix one: nothing that
/// ends an operand comes before it in its span.
///
/// # Arguments
///
/// * `l` - The line.
/// * `k` - The operator's token.
/// * `start` - Where its span starts.
fn unary(l: &Line<'_>, k: usize, start: usize) -> bool {
    let Some(p) = k.checked_sub(1).filter(|p| *p >= start) else {
        return true;
    };
    let ends_operand = matches!(
        l.toks.get(p).map(|t| t.lex),
        Some(Lex::Name | Lex::Number | Lex::Literal)
    ) || l.is(p, ")")
        || l.is(p, "]");
    !ends_operand || l.word(p) == "return"
}

/// A node's span without the `;` that ends its statement.
///
/// # Arguments
///
/// * `l` - The line.
/// * `span` - The token span.
fn trimmed(l: &Line<'_>, span: (usize, usize)) -> (usize, usize) {
    if span.1 > span.0 && l.is(span.1 - 1, ";") {
        (span.0, span.1 - 1)
    } else {
        span
    }
}

/// Tells whether a variable of type `ty` holds a non-negative value
/// unchanged.
///
/// # Arguments
///
/// * `v` - The value.
/// * `ty` - The type.
fn fits(v: u64, ty: &str) -> bool {
    match ty {
        "uint8_t" => v <= 0xff,
        "int8_t" => v <= 0x7f,
        "uint16_t" => v <= 0xffff,
        "int16_t" => v <= 0x7fff,
        "uint32_t" | "int32_t" | "uint64_t" | "int64_t" => true,
        _ => false,
    }
}

/// The text of a token span of a line.
///
/// # Arguments
///
/// * `l` - The line.
/// * `span` - The token span.
fn span_text<'t>(l: &Line<'t>, span: (usize, usize)) -> &'t str {
    let (Some(a), Some(z)) = (
        l.toks.get(span.0),
        span.1.checked_sub(1).and_then(|e| l.toks.get(e)),
    ) else {
        return "";
    };
    l.text.get(a.at..z.end).unwrap_or("")
}

/// The identifiers a run of lines names outside strings and comments.
///
/// # Arguments
///
/// * `lines` - The lines.
fn names_in<'t>(lines: impl Iterator<Item = &'t str>) -> BTreeSet<&'t str> {
    let mut out = BTreeSet::new();
    for l in lines {
        for t in lex(l) {
            if t.lex == Lex::Name
                && let Some(w) = l.get(t.at..t.end)
            {
                out.insert(w);
            }
        }
    }
    out
}

#[cfg(test)]
#[expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]
mod tests {
    use super::{fold, split, split_webs};

    /// A function text: a header, the declarations, a blank line, the body.
    ///
    /// # Arguments
    ///
    /// * `decls` - The declaration lines.
    /// * `body` - The body lines.
    fn function(decls: &[&str], body: &[&str]) -> String {
        let mut out = String::from(
            "// f @ 0x1000: 9 instructions, 1 blocks\n// signature: uint64_t f(uint64_t a1, uint64_t a2)\n",
        );
        for l in decls.iter().chain(&[""]).chain(body) {
            out.push_str(l);
            out.push('\n');
        }
        out
    }

    /// The body of a function text: the lines after the first blank one.
    ///
    /// # Arguments
    ///
    /// * `text` - The text.
    fn body(text: &str) -> Vec<&str> {
        text.lines().skip_while(|l| !l.is_empty()).skip(1).collect()
    }

    /// Two values a register holds one after the other become two
    /// variables, each declared at the register's type.
    #[test]
    fn two_values_in_one_register_become_two_variables() {
        let t = function(
            &["uint64_t rax;"],
            &[
                "rax = sub_1(a1);",
                "sub_2(rax, rax);",
                "rax = sub_3(a2);",
                "sub_4(rax, rax);",
                "return 0;",
            ],
        );
        let out = split(&t).expect("splits");
        assert!(out.contains("uint64_t var1, var2;\n"), "{out}");
        assert_eq!(
            body(&out),
            [
                "var1 = sub_1(a1);",
                "sub_2(var1, var1);",
                "var2 = sub_3(a2);",
                "sub_4(var2, var2);",
                "return 0;",
            ],
            "{out}"
        );
    }

    /// A web the entry reaches keeps the register's name: on the path
    /// where nothing set it, it holds what the caller left there.
    #[test]
    fn a_web_the_entry_reaches_keeps_the_register_name() {
        let t = function(
            &["uint64_t rbx;"],
            &[
                "if (a1 != 0) {",
                "  rbx = 5;",
                "}",
                "sub_1(rbx);",
                "return 0;",
            ],
        );
        assert_eq!(split_webs(&t), t);
    }

    /// A value nothing reads goes: a pure line whole, a call's result
    /// target, leaving the call; the declaration goes with the last use.
    #[test]
    fn a_value_nothing_reads_goes() {
        let t = function(
            &["uint64_t rax, rcx;"],
            &[
                "rax = a1 + 1;",
                "rax = sub_1(a1);",
                "rcx = sub_2(a2);",
                "return 0;",
            ],
        );
        let out = split(&t).expect("drops");
        assert_eq!(
            body(&out),
            ["sub_1(a1);", "sub_2(a2);", "return 0;"],
            "{out}"
        );
        assert_eq!(out.lines().nth(2), Some(""), "{out}");
    }

    /// A chain keeps the targets something reads.
    #[test]
    fn a_chain_keeps_the_targets_something_reads() {
        let t = function(
            &["uint64_t rax, rcx;"],
            &["rcx = rax = sub_1(a1);", "sub_2(rcx);", "return 0;"],
        );
        let out = split(&t).expect("drops");
        assert_eq!(
            body(&out),
            ["var1 = sub_1(a1);", "sub_2(var1);", "return 0;"],
            "{out}"
        );
    }

    /// A value a loop carries around is one variable.
    #[test]
    fn a_loop_carried_value_is_one_variable() {
        let t = function(
            &["uint64_t rax;"],
            &[
                "rax = 0;",
                "while (rax < a1) {",
                "  rax += 1;",
                "}",
                "return rax;",
            ],
        );
        let out = split(&t).expect("splits");
        assert_eq!(
            body(&out),
            [
                "var1 = 0;",
                "while (var1 < a1) {",
                "  var1 += 1;",
                "}",
                "return var1;",
            ],
            "{out}"
        );
    }

    /// The register a function hands back as a second result is read by
    /// its caller: it keeps its name and its last value.
    #[test]
    fn a_handed_back_register_keeps_its_name() {
        let t = function(&["uint64_t rdx;"], &["rdx = a1 + 1;", "return 0;"]).replace(
            "// signature:",
            "// hands back rdx: a caller reads it after the call\n// signature:",
        );
        assert_eq!(split_webs(&t), t);
    }

    /// An unmodelled instruction reads and writes the machine's registers,
    /// so the webs it touches keep the registers' names.
    #[test]
    fn an_unmodelled_instruction_pins_the_registers() {
        let t = function(
            &["uint64_t rax;"],
            &["rax = a1;", "/* asm: cpuid */", "return rax;"],
        );
        assert_eq!(split_webs(&t), t);
    }

    /// A register whose address the text takes is left as it is.
    #[test]
    fn a_register_whose_address_is_taken_is_left_alone() {
        let t = function(
            &["uint64_t rax;"],
            &["rax = a1;", "sub_1(&rax);", "return rax;"],
        );
        assert_eq!(split_webs(&t), t);
    }

    /// A store through a register is a read of it, not a write.
    #[test]
    fn a_store_through_a_register_reads_it() {
        let t = function(
            &["uint64_t rsi;"],
            &[
                "rsi = a2;",
                "*(uint8_t*)rsi = 0;",
                "rsi += 1;",
                "return rsi;",
            ],
        );
        let out = split(&t).expect("splits");
        assert_eq!(
            body(&out),
            [
                "var1 = a2;",
                "*(uint8_t*)var1 = 0;",
                "var1 += 1;",
                "return var1;"
            ],
            "{out}"
        );
    }

    /// A text with no blank line before a body is left as it is.
    #[test]
    fn a_text_it_cannot_read_is_left_alone() {
        let t = "// f @ 0x1000\nuint64_t rax;\nrax = 1;\n";
        assert_eq!(split_webs(t), t);
    }

    /// A call's result read once by the test right after it folds into
    /// the test.
    #[test]
    fn a_result_read_once_by_the_next_test_folds_into_it() {
        let t = function(
            &["uint64_t var1;"],
            &[
                "var1 = sub_1(a1);",
                "if (var1 != 0) {",
                "  return 1;",
                "}",
                "return 0;",
            ],
        );
        let out = fold(&t).expect("folds");
        assert_eq!(
            body(&out),
            ["if (sub_1(a1) != 0) {", "  return 1;", "}", "return 0;"],
            "{out}"
        );
        assert!(!out.contains("var1"), "{out}");
    }

    /// A load folds into no line whose calls could change the memory it
    /// reads before it is read.
    #[test]
    fn a_load_does_not_fold_past_a_call() {
        let t = function(
            &["uint64_t var1;"],
            &[
                "var1 = *(uint64_t*)a1;",
                "sub_1(sub_2(a2), var1);",
                "return 0;",
            ],
        );
        assert_eq!(fold(&t), None);
    }

    /// A call does not fold across a join: the label starts another
    /// block, and the call belongs where the binary has it, before the
    /// jump that reaches the label, not after the label itself.
    #[test]
    fn a_call_does_not_fold_across_a_join() {
        let t = function(
            &["uint64_t var1;"],
            &[
                "if (a1 == 13) {",
                "  var1 = sub_1(a2);",
                "  goto L_1004;",
                "}",
                "sub_2(a2);",
                "goto L_1005;",
                "L_1004:",
                "sub_3(var1);",
                "return 0;",
                "L_1005:",
                "return 1;",
            ],
        );
        assert_eq!(fold(&t), None);
    }

    /// A narrow variable's assignment truncates, so it folds into no
    /// argument, where the call would see the whole value.
    #[test]
    fn a_narrow_variable_does_not_fold_into_an_argument() {
        let t = function(
            &["uint32_t var1;"],
            &["var1 = sub_1(a1);", "sub_2(var1);", "return 0;"],
        );
        assert_eq!(fold(&t), None);
    }

    /// A variable set once to a small constant reads as the constant where
    /// the value converts whole.
    #[test]
    fn a_constant_folds_into_its_reads() {
        let t = function(
            &["uint64_t var1;"],
            &["var1 = 0;", "sub_1(a1);", "return var1;"],
        );
        let out = fold(&t).expect("folds");
        assert_eq!(body(&out), ["sub_1(a1);", "return 0;"], "{out}");
    }

    /// Folding runs to a fixed point: a fold can make its use foldable.
    #[test]
    fn folds_chain() {
        let t = function(
            &["uint64_t rax, rcx;"],
            &[
                "rax = sub_1(a1);",
                "rcx = sub_2(rax);",
                "if (rcx == 0) {",
                "  return 1;",
                "}",
                "return 0;",
            ],
        );
        let out = split_webs(&t);
        assert_eq!(
            body(&out),
            [
                "if (sub_2(sub_1(a1)) == 0) {",
                "  return 1;",
                "}",
                "return 0;"
            ],
            "{out}"
        );
    }

    /// The same text splits the same way twice.
    #[test]
    fn the_pass_is_deterministic() {
        let t = function(
            &["uint64_t rax, rbx;"],
            &[
                "rax = sub_1(a1);",
                "rbx = rax;",
                "rax = sub_2(rbx);",
                "sub_3(rax, rbx);",
                "return rbx;",
            ],
        );
        assert_eq!(split_webs(&t), split_webs(&t));
    }

    /// A copy that is the only value its target holds, made while the
    /// source is not written again, merges the two into one variable.
    #[test]
    fn a_copy_merges_into_its_source() {
        let t = function(
            &["uint64_t var1, var2, home_10;"],
            &[
                "var1 = sub_1(a1);",
                "if (var1 == 0) {",
                "  return 8;",
                "}",
                "var2 = home_10 = var1;",
                "sub_2(var1);",
                "sub_3(*(uint64_t*)var2);",
                "return 0;",
            ],
        );
        let out = fold(&t).expect("merges");
        assert_eq!(
            body(&out),
            [
                "var1 = sub_1(a1);",
                "if (var1 == 0) {",
                "  return 8;",
                "}",
                "home_10 = var1;",
                "sub_2(var1);",
                "sub_3(*(uint64_t*)var1);",
                "return 0;",
            ],
            "{out}"
        );
        assert!(out.contains("uint64_t var1, home_10;"), "{out}");
    }

    /// A copy whose source is written again while the copy is still read
    /// stays a variable of its own.
    #[test]
    fn a_copy_outliving_its_source_stays() {
        let t = function(
            &["uint64_t var1, var2;"],
            &[
                "var1 = sub_1(a1);",
                "sub_0(var1);",
                "var2 = var1;",
                "var1 = sub_2(a2);",
                "sub_3(var1);",
                "sub_4(var1, var2);",
                "return var2;",
            ],
        );
        let out = split_webs(&t);
        assert!(out.contains("var2 = var1;"), "{out}");
    }

    /// The variables are numbered in the order the body first names them,
    /// with no gaps the folds left.
    #[test]
    fn the_variables_are_numbered_without_gaps() {
        let t = function(
            &["uint64_t rax, rbx;"],
            &[
                "rax = sub_1(a1);",
                "rbx = sub_2(rax);",
                "rax = sub_3(a2);",
                "sub_4(rbx, rax);",
                "sub_5(rbx, rax);",
                "return 0;",
            ],
        );
        let out = split_webs(&t);
        assert_eq!(
            body(&out),
            [
                "var1 = sub_2(sub_1(a1));",
                "var2 = sub_3(a2);",
                "sub_4(var1, var2);",
                "sub_5(var1, var2);",
                "return 0;",
            ],
            "{out}"
        );
        assert!(out.contains("uint64_t var1, var2;"), "{out}");
    }

    /// A jump out of the text keeps every value alive for the code it
    /// reaches, each under its own name.
    #[test]
    fn a_jump_out_keeps_values_alive() {
        let t = function(
            &["uint64_t rcx;"],
            &["rcx = sub_1(a1);", "sub_2(a2);", "goto *0x1234;"],
        );
        let out = split(&t).expect("splits");
        assert_eq!(
            body(&out),
            ["var1 = sub_1(a1);", "sub_2(a2);", "goto *0x1234;"],
            "{out}"
        );
    }

    /// A call to a thunk that only jumps through a register reads that
    /// register, which keeps its name and its value.
    #[test]
    fn a_thunk_call_reads_its_register() {
        let t = function(&["uint64_t rax;"], &["rax = a1 + 8;", "sub_9(a2);", "return 0;"])
            .replace(
                "// signature:",
                "// note: sub_9 only jumps through rax: a call to it is the call through rax\n// signature:",
            );
        assert_eq!(split_webs(&t), t);
    }

    /// A second result stays on its own line after its call.
    #[test]
    fn a_second_result_does_not_fold() {
        let t = function(
            &["uint64_t var1, var2;"],
            &[
                "var1 = sub_1(a1);",
                "var2 = sub_1__rdx(a1);",
                "return sub_2(var1, var2);",
            ],
        );
        assert_eq!(fold(&t), None);
    }

    /// A value folds past statements that cannot change it: a sum of
    /// variables past a call, but a load past no store.
    #[test]
    fn a_fold_passes_only_what_cannot_change_it() {
        let t = function(
            &["uint64_t var1, var2;"],
            &[
                "var1 = a1 + 8;",
                "sub_1(a2);",
                "sub_2(var1);",
                "var2 = *(uint64_t*)a1;",
                "*(uint64_t*)a2 = 0;",
                "sub_3(var2);",
                "return 0;",
            ],
        );
        let out = fold(&t).expect("folds");
        assert_eq!(
            body(&out),
            [
                "sub_1(a2);",
                "sub_2(a1 + 8);",
                "var2 = *(uint64_t*)a1;",
                "*(uint64_t*)a2 = 0;",
                "sub_3(var2);",
                "return 0;",
            ],
            "{out}"
        );
    }
}
