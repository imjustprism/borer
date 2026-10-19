//! Reading the structurer's text into the tree.
//!
//! The text is line-structured: one statement per line, two spaces per
//! nesting level, a block opened by a line ending in `{` and closed by one
//! starting with `}`. Each line becomes a statement, and each expression on
//! it an [`Expr`] read with C's precedence. An expression whose reading
//! does not print back as written stays [`ExprKind::Raw`], and a line no
//! statement form matches stays [`StmtKind::Raw`], so [`build`] then
//! [`super::print()`] gives back the text byte for byte. A body whose
//! nesting does not read (an indentation that is not its depth, a brace
//! that does not close) becomes one raw line per line.

use super::{
    Arm, ArmBody, BinOp, Body, CTy, CaseLabel, Else, Expr, ExprKind, Handler, Head, Label, LitKind,
    Literal, Name, PostOp, Prov, Stmt, StmtKind, UnOp, print,
};

/// Deepest nesting an expression or a block is read to, so a hostile text
/// cannot run the reader out of stack.
const DEPTH_MAX: usize = 200;

/// Reads a body's text into a tree.
///
/// # Arguments
///
/// * `text` - The structurer's text: lines, each ending in a newline.
///
/// # Returns
///
/// The tree, which prints back as `text`.
pub(in crate::analysis::decompile) fn build(text: &str) -> Body {
    let lines: Vec<&str> = text.lines().collect();
    let mut reader = Reader {
        lines: &lines,
        at: 0,
        prov: Prov::ENTRY,
        sets: vec![Vec::new()],
    };
    let stmts = reader
        .block(0)
        .filter(|_| reader.at == lines.len() && text.ends_with('\n'));
    match stmts {
        Some(stmts) => Body {
            stmts,
            prov: reader.sets,
        },
        None => Body {
            stmts: lines
                .iter()
                .map(|l| Stmt {
                    kind: if l.is_empty() {
                        StmtKind::Blank
                    } else {
                        StmtKind::Raw((*l).to_owned())
                    },
                    prov: Prov::ENTRY,
                })
                .collect(),
            prov: vec![Vec::new()],
        },
    }
}

/// The state of reading a body's lines.
struct Reader<'t> {
    /// The lines, without their newlines.
    lines: &'t [&'t str],
    /// The next line to read.
    at: usize,
    /// The provenance of the statements being read: the last label's.
    prov: Prov,
    /// The addresses of each provenance id so far.
    sets: Vec<Vec<u64>>,
}

impl<'t> Reader<'t> {
    /// Reads statements at a depth up to the line that closes the block
    /// (left unread) or the end.
    ///
    /// # Arguments
    ///
    /// * `depth` - The nesting depth the lines must be indented to.
    ///
    /// # Returns
    ///
    /// The statements, or `None` when a line's indentation is not the
    /// depth or a block inside does not close.
    fn block(&mut self, depth: usize) -> Option<Vec<Stmt>> {
        if depth > DEPTH_MAX {
            return None;
        }
        let mut out = Vec::new();
        while let Some(&l) = self.lines.get(self.at) {
            if l.is_empty() {
                self.at += 1;
                out.push(self.stmt(StmtKind::Blank));
                continue;
            }
            if l.trim_start().starts_with('}') {
                break;
            }
            let t = indented(l, depth)?;
            self.at += 1;
            let s = self.line(t, depth)?;
            out.push(s);
        }
        Some(out)
    }

    /// Wraps a statement kind in the current provenance.
    ///
    /// # Arguments
    ///
    /// * `kind` - The statement.
    fn stmt(&self, kind: StmtKind) -> Stmt {
        Stmt {
            kind,
            prov: self.prov,
        }
    }

    /// Wraps an expression read from text in the current provenance.
    ///
    /// # Arguments
    ///
    /// * `text` - The expression's text.
    fn expr(&self, text: &str) -> Expr {
        expression(text, self.prov)
    }

    /// Reads the closing line of a block at a depth.
    ///
    /// # Arguments
    ///
    /// * `depth` - The depth of the line that opened the block.
    ///
    /// # Returns
    ///
    /// The closing line without its indentation, or `None` when there is
    /// none.
    fn closer(&mut self, depth: usize) -> Option<&'t str> {
        let line: &'t str = self.lines.get(self.at)?;
        let t = indented(line, depth)?;
        self.at += 1;
        Some(t)
    }

    /// Reads a block's statements one level deeper and its bare `}`.
    ///
    /// # Arguments
    ///
    /// * `depth` - The depth of the line that opened the block.
    fn braced(&mut self, depth: usize) -> Option<Vec<Stmt>> {
        let body = self.block(depth + 1)?;
        (self.closer(depth)? == "}").then_some(body)
    }

    /// Reads one line's statement, and the lines of the block it opens.
    ///
    /// # Arguments
    ///
    /// * `t` - The line without its indentation.
    /// * `depth` - Its depth.
    ///
    /// # Returns
    ///
    /// The statement, or `None` when the block it opens does not read.
    fn line(&mut self, t: &str, depth: usize) -> Option<Stmt> {
        if let Some(va) = t
            .strip_prefix("L_")
            .and_then(|h| h.strip_suffix(':'))
            .and_then(|h| u64::from_str_radix(h, 16).ok())
            .filter(|va| format!("L_{va:x}:") == t)
        {
            self.prov = Prov(u32::try_from(self.sets.len()).unwrap_or(u32::MAX));
            self.sets.push(vec![va]);
            return Some(self.stmt(StmtKind::Label(Label(va))));
        }
        if let Some(cond) = t.strip_prefix("if (").and_then(|r| r.strip_suffix(") {")) {
            return self.if_chain(cond, depth);
        }
        if let Some(cond) = t
            .strip_prefix("while (")
            .and_then(|r| r.strip_suffix(") {"))
        {
            let cond = self.expr(cond);
            let body = self.braced(depth)?;
            return Some(self.stmt(StmtKind::While { cond, body }));
        }
        if t == "do {" {
            let body = self.block(depth + 1)?;
            let cond = self
                .closer(depth)?
                .strip_prefix("} while (")?
                .strip_suffix(");")?;
            let cond = self.expr(cond);
            return Some(self.stmt(StmtKind::DoWhile { body, cond }));
        }
        if let Some(head) = t.strip_prefix("for (").and_then(|r| r.strip_suffix(") {"))
            && let [init, cond, step] = top_level(head, "; ").as_slice()
        {
            let (init, cond, step) = (self.expr(init), self.expr(cond), self.expr(step));
            let body = self.braced(depth)?;
            return Some(self.stmt(StmtKind::For {
                init,
                cond,
                step,
                body,
            }));
        }
        if let Some(value) = t
            .strip_prefix("switch (")
            .and_then(|r| r.strip_suffix(") {"))
        {
            let value = self.expr(value);
            let mut arms = Vec::new();
            loop {
                let line: &'t str = self.lines.get(self.at)?;
                let line = indented(line, depth)?;
                self.at += 1;
                if line == "}" {
                    break;
                }
                arms.push(self.arm(line, depth)?);
            }
            return Some(self.stmt(StmtKind::Switch { value, arms }));
        }
        if t == "{" {
            let body = self.braced(depth)?;
            return Some(self.stmt(StmtKind::Block(body)));
        }
        if t == "try {" || t == "__try {" {
            return self.try_block(t == "__try {", depth);
        }
        if let Some(text) = t.strip_prefix("//") {
            return Some(self.stmt(StmtKind::Comment(text.to_owned())));
        }
        if let Some(text) = t
            .strip_prefix("/* asm: ")
            .and_then(|r| r.strip_suffix(" */"))
            .filter(|r| !r.contains("*/"))
        {
            return Some(self.stmt(StmtKind::Asm(text.to_owned())));
        }
        if let Some((cond, rest)) = guard(t) {
            let cond = self.expr(cond);
            if let Some(then) = self.simple(rest) {
                return Some(self.stmt(StmtKind::Guard {
                    cond,
                    then: Box::new(then),
                }));
            }
        }
        Some(
            self.simple(t)
                .unwrap_or_else(|| self.stmt(StmtKind::Raw(t.to_owned()))),
        )
    }

    /// Reads an `if` whose `if (cond) {` line was just read, with its
    /// `else if` and `else` arms.
    ///
    /// # Arguments
    ///
    /// * `cond` - The condition's text.
    /// * `depth` - The depth of the `if`.
    fn if_chain(&mut self, cond: &str, depth: usize) -> Option<Stmt> {
        let cond = self.expr(cond);
        let prov = self.prov;
        let then = self.block(depth + 1)?;
        let closing = self.closer(depth)?;
        let other = if closing == "}" {
            None
        } else if closing == "} else {" {
            Some(Else::Block(self.braced(depth)?))
        } else {
            let next = closing.strip_prefix("} else if (")?.strip_suffix(") {")?;
            Some(Else::If(Box::new(self.if_chain(next, depth)?)))
        };
        Some(Stmt {
            kind: StmtKind::If { cond, then, other },
            prov,
        })
    }

    /// Reads a guarded region whose `try {` or `__try {` line was just
    /// read, with its handlers: `} catch (decl) {`, `} __except (filter) {`
    /// and `} __finally {`, up to the bare `}`.
    ///
    /// # Arguments
    ///
    /// * `seh` - Whether the opening line was `__try {`.
    /// * `depth` - The depth of the opening line.
    ///
    /// # Returns
    ///
    /// The statement, or `None` when a handler line does not read or no
    /// handler follows the body.
    fn try_block(&mut self, seh: bool, depth: usize) -> Option<Stmt> {
        let prov = self.prov;
        let body = self.block(depth + 1)?;
        let mut handlers = Vec::new();
        loop {
            let closing = self.closer(depth)?;
            if closing == "}" {
                break;
            }
            let head = if closing == "} __finally {" {
                Head::Finally
            } else if let Some(filter) = closing
                .strip_prefix("} __except (")
                .and_then(|r| r.strip_suffix(") {"))
            {
                Head::Except(self.expr(filter))
            } else {
                let decl = closing.strip_prefix("} catch (")?.strip_suffix(") {")?;
                Head::Catch(decl.to_owned())
            };
            handlers.push(Handler {
                head,
                body: self.block(depth + 1)?,
            });
        }
        (!handlers.is_empty()).then_some(Stmt {
            kind: StmtKind::Try {
                seh,
                body,
                handlers,
            },
            prov,
        })
    }

    /// Reads one `switch` arm from its labels' line.
    ///
    /// # Arguments
    ///
    /// * `t` - The line without its indentation.
    /// * `depth` - The depth of the `switch`.
    fn arm(&mut self, t: &str, depth: usize) -> Option<Arm> {
        let mut labels = Vec::new();
        let mut rest = t;
        loop {
            if let Some(r) = rest.strip_prefix("default: ") {
                labels.push(CaseLabel::Default);
                rest = r;
            } else if let Some(r) = rest.strip_prefix("case ") {
                let (value, after) = case_value(r)?;
                labels.push(CaseLabel::Value(self.expr(value)));
                rest = after;
            } else {
                break;
            }
        }
        if labels.is_empty() {
            return None;
        }
        let prov = self.prov;
        let body = if rest == "{" {
            ArmBody::Block(self.braced(depth)?)
        } else {
            ArmBody::Inline(Box::new(self.simple(rest)?))
        };
        Some(Arm { labels, body, prov })
    }

    /// Reads a statement that opens no block: a jump, a `return`, an
    /// expression statement.
    ///
    /// # Arguments
    ///
    /// * `t` - The statement's text.
    ///
    /// # Returns
    ///
    /// The statement, or `None` when no such form matches.
    fn simple(&self, t: &str) -> Option<Stmt> {
        let kind = match t {
            "break;" => StmtKind::Break,
            "continue;" => StmtKind::Continue,
            "return;" => StmtKind::Return(None),
            _ => {
                if let Some(va) = t
                    .strip_prefix("goto L_")
                    .and_then(|h| h.strip_suffix(';'))
                    .and_then(|h| u64::from_str_radix(h, 16).ok())
                    .filter(|va| format!("goto L_{va:x};") == t)
                {
                    StmtKind::Goto(Label(va))
                } else if let Some(v) = t.strip_prefix("return ").and_then(|r| r.strip_suffix(';'))
                {
                    StmtKind::Return(Some(self.expr(v)))
                } else {
                    let e = t.strip_suffix(';')?;
                    let e = self.expr(e);
                    if matches!(e.kind, ExprKind::Raw(_)) {
                        return None;
                    }
                    StmtKind::Expr(e)
                }
            }
        };
        Some(self.stmt(kind))
    }
}

/// Returns a line without its indentation when that is exactly `depth`
/// levels.
///
/// # Arguments
///
/// * `line` - The line.
/// * `depth` - The expected depth.
fn indented(line: &str, depth: usize) -> Option<&str> {
    let pad = depth.checked_mul(2)?;
    let (lead, t) = (line.get(..pad)?, line.get(pad..)?);
    (lead.bytes().all(|b| b == b' ') && !t.starts_with(' ')).then_some(t)
}

/// Splits an `if (cond) stmt` line into its condition and statement.
///
/// # Arguments
///
/// * `t` - The line without its indentation.
///
/// # Returns
///
/// The condition's text and the statement's, or `None` when the line is
/// not such a guard.
fn guard(t: &str) -> Option<(&str, &str)> {
    let rest = t.strip_prefix("if (")?;
    let close = closing_paren(rest)?;
    Some((rest.get(..close)?, rest.get(close..)?.strip_prefix(") ")?))
}

/// Splits a `case` label's value from the rest of its line.
///
/// # Arguments
///
/// * `r` - The text after `case `.
///
/// # Returns
///
/// The value's text and what follows the label's `: `.
fn case_value(r: &str) -> Option<(&str, &str)> {
    let toks = lex(r)?;
    let mut depth = 0usize;
    for (tok, at) in &toks {
        match tok {
            Tok::Punct("(" | "[") => depth += 1,
            Tok::Punct(")" | "]") => depth = depth.checked_sub(1)?,
            Tok::Punct(":") if depth == 0 => {
                return Some((r.get(..*at)?, r.get(*at..)?.strip_prefix(": ")?));
            }
            Tok::Punct(_) | Tok::Word(_) | Tok::Lit(..) => {}
        }
    }
    None
}

/// Returns where the parenthesis closing an opened one stands.
///
/// # Arguments
///
/// * `rest` - The text after an opening parenthesis.
///
/// # Returns
///
/// The byte offset of the closing parenthesis.
fn closing_paren(rest: &str) -> Option<usize> {
    let mut depth = 0usize;
    for (tok, at) in lex(rest)? {
        match tok {
            Tok::Punct("(") => depth += 1,
            Tok::Punct(")") if depth == 0 => return Some(at),
            Tok::Punct(")") => depth -= 1,
            Tok::Punct(_) | Tok::Word(_) | Tok::Lit(..) => {}
        }
    }
    None
}

/// Splits text at each separator that stands outside every bracket and
/// literal.
///
/// # Arguments
///
/// * `text` - The text.
/// * `sep` - The separator: `"; "` between a `for` header's parts.
fn top_level<'t>(text: &'t str, sep: &str) -> Vec<&'t str> {
    let Some(toks) = lex(text) else {
        return Vec::new();
    };
    let mut parts = Vec::new();
    let (mut depth, mut from) = (0usize, 0usize);
    let first = sep.trim_end();
    for (tok, at) in toks {
        match tok {
            Tok::Punct("(" | "[") => depth += 1,
            Tok::Punct(")" | "]") => depth = depth.saturating_sub(1),
            Tok::Punct(p) if depth == 0 && p == first && text[at..].starts_with(sep) => {
                parts.push(&text[from..at]);
                from = at + sep.len();
            }
            Tok::Punct(_) | Tok::Word(_) | Tok::Lit(..) => {}
        }
    }
    parts.push(&text[from..]);
    parts
}

/// A token of an expression, borrowing its spelling.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Tok<'t> {
    /// A name: a `Class::method` or `operator new` is one.
    Word(&'t str),
    /// A literal of the kind.
    Lit(LitKind, &'t str),
    /// An operator or punctuation.
    Punct(&'static str),
}

/// The operators and punctuation, longest first.
const PUNCTS: [&str; 47] = [
    "<<=", ">>=", "...", "->", "++", "--", "<<", ">>", "<=", ">=", "==", "!=", "&&", "||", "+=",
    "-=", "*=", "/=", "%=", "&=", "|=", "^=", "::", "+", "-", "*", "/", "%", "&", "|", "^", "~",
    "!", "<", ">", "=", "?", ":", "(", ")", "[", "]", "{", "}", ",", ";", ".",
];

/// Splits text into tokens with the byte offset each starts at.
///
/// # Arguments
///
/// * `text` - The text.
///
/// # Returns
///
/// The tokens, or `None` at a comment, a literal that does not end or a
/// character no token starts with.
fn lex(text: &str) -> Option<Vec<(Tok<'_>, usize)>> {
    let bytes = text.as_bytes();
    let mut out = Vec::new();
    let mut at = 0;
    while let Some(&c) = bytes.get(at) {
        let rest = &text[at..];
        if c == b' ' {
            at += 1;
            continue;
        }
        if rest.starts_with("//") || rest.starts_with("/*") {
            return None;
        }
        let len = if c == b'"' || c == b'\'' || rest.starts_with("L\"") {
            let open = usize::from(c == b'L');
            let quote = bytes[at + open];
            let mut k = at + open + 1;
            loop {
                match bytes.get(k)? {
                    b'\\' => k += 2,
                    q if *q == quote => break,
                    _ => k += 1,
                }
            }
            let kind = if quote == b'"' {
                LitKind::Str
            } else {
                LitKind::Char
            };
            out.push((Tok::Lit(kind, &text[at..=k]), at));
            k + 1 - at
        } else if c.is_ascii_digit()
            || (c == b'.' && bytes.get(at + 1).is_some_and(u8::is_ascii_digit))
        {
            let hex = rest.starts_with("0x") || rest.starts_with("0X");
            let mut k = 0;
            while let Some(&d) = bytes.get(at + k) {
                let sign = matches!(d, b'+' | b'-')
                    && k > 0
                    && match bytes[at + k - 1] {
                        b'p' | b'P' => hex,
                        b'e' | b'E' => !hex,
                        _ => false,
                    };
                if !(d.is_ascii_alphanumeric() || d == b'.' || d == b'_' || sign) {
                    break;
                }
                k += 1;
            }
            let lit = &rest[..k];
            let float = lit.contains('.')
                || (hex && lit.contains(['p', 'P']))
                || (!hex && lit.contains(['e', 'E']));
            let kind = if float { LitKind::Float } else { LitKind::Int };
            out.push((Tok::Lit(kind, lit), at));
            k
        } else if c.is_ascii_alphabetic() || c == b'_' {
            let word = |s: &str| {
                s.find(|d: char| !(d.is_ascii_alphanumeric() || d == '_'))
                    .unwrap_or(s.len())
            };
            let mut end = word(rest);
            while rest[end..].starts_with("::") {
                let tail = &rest[end + 2..];
                let skip = usize::from(tail.starts_with('~'));
                let n = word(&tail[skip..]);
                if n == 0 {
                    break;
                }
                end += 2 + skip + n;
            }
            if rest[..end].ends_with("operator") {
                for op in [" new", " delete"] {
                    if rest[end..].starts_with(op)
                        && !rest[end + op.len()..]
                            .starts_with(|d: char| d.is_ascii_alphanumeric() || d == '_')
                    {
                        end += op.len();
                    }
                }
            }
            out.push((Tok::Word(&rest[..end]), at));
            end
        } else {
            let p = PUNCTS.iter().find(|p| rest.starts_with(**p))?;
            out.push((Tok::Punct(p), at));
            p.len()
        };
        at += len;
    }
    Some(out)
}

/// Reads an expression's text into a tree that prints back as the text.
///
/// # Arguments
///
/// * `text` - The expression's text.
/// * `prov` - The provenance of every node.
///
/// # Returns
///
/// The tree, or [`ExprKind::Raw`] holding the text when it does not read
/// as C or its reading prints otherwise.
fn expression(text: &str, prov: Prov) -> Expr {
    let read = lex(text).and_then(|toks| {
        let mut p = Parser {
            src: text,
            toks: &toks,
            at: 0,
            prov,
            depth: 0,
        };
        let e = p.assign()?;
        (p.at == toks.len()).then_some(e)
    });
    if let Some(e) = read {
        let mut back = String::with_capacity(text.len());
        print::expr(&e, &mut back);
        if back == text {
            return e;
        }
    }
    Expr {
        kind: ExprKind::Raw(text.to_owned()),
        ty: None,
        prov,
    }
}

/// A reader of one expression's tokens, by precedence climbing.
struct Parser<'p, 't> {
    /// The expression's text, which the tokens' offsets index.
    src: &'t str,
    /// The tokens.
    toks: &'p [(Tok<'t>, usize)],
    /// The next one to read.
    at: usize,
    /// The provenance of every node.
    prov: Prov,
    /// How deep the reading is nested.
    depth: usize,
}

/// The binary operator a token spells, with its precedence (higher binds
/// tighter).
///
/// # Arguments
///
/// * `p` - The token.
fn binary(p: &str) -> Option<(BinOp, u8)> {
    Some(match p {
        "*" => (BinOp::Mul, 10),
        "/" => (BinOp::Div, 10),
        "%" => (BinOp::Rem, 10),
        "+" => (BinOp::Add, 9),
        "-" => (BinOp::Sub, 9),
        "<<" => (BinOp::Shl, 8),
        ">>" => (BinOp::Shr, 8),
        "<" => (BinOp::Lt, 7),
        "<=" => (BinOp::Le, 7),
        ">" => (BinOp::Gt, 7),
        ">=" => (BinOp::Ge, 7),
        "==" => (BinOp::Eq, 6),
        "!=" => (BinOp::Ne, 6),
        "&" => (BinOp::BitAnd, 5),
        "^" => (BinOp::BitXor, 4),
        "|" => (BinOp::BitOr, 3),
        "&&" => (BinOp::And, 2),
        "||" => (BinOp::Or, 1),
        _ => return None,
    })
}

/// The operator a compound assignment applies, `None` inside for `=`.
///
/// # Arguments
///
/// * `p` - The token.
fn assignment(p: &str) -> Option<Option<BinOp>> {
    Some(match p {
        "=" => None,
        "+=" => Some(BinOp::Add),
        "-=" => Some(BinOp::Sub),
        "*=" => Some(BinOp::Mul),
        "/=" => Some(BinOp::Div),
        "%=" => Some(BinOp::Rem),
        "&=" => Some(BinOp::BitAnd),
        "|=" => Some(BinOp::BitOr),
        "^=" => Some(BinOp::BitXor),
        "<<=" => Some(BinOp::Shl),
        ">>=" => Some(BinOp::Shr),
        _ => return None,
    })
}

/// The words a cast's type may be made of besides one name.
const TYPE_WORDS: [&str; 11] = [
    "unsigned", "signed", "const", "volatile", "struct", "union", "enum", "long", "short", "int",
    "char",
];

impl<'t> Parser<'_, 't> {
    /// Returns the next token without reading it.
    fn peek(&self) -> Option<Tok<'t>> {
        self.toks.get(self.at).map(|(t, _)| *t)
    }

    /// Reads the next token when it is the punctuation.
    ///
    /// # Arguments
    ///
    /// * `p` - The punctuation.
    fn eat(&mut self, p: &str) -> bool {
        let hit = matches!(self.peek(), Some(Tok::Punct(q)) if q == p);
        self.at += usize::from(hit);
        hit
    }

    /// Builds a node with the reader's provenance.
    ///
    /// # Arguments
    ///
    /// * `kind` - The node.
    fn node(&self, kind: ExprKind) -> Expr {
        Expr {
            kind,
            ty: None,
            prov: self.prov,
        }
    }

    /// Reads an assignment or anything tighter.
    fn assign(&mut self) -> Option<Expr> {
        self.depth += 1;
        if self.depth > DEPTH_MAX {
            return None;
        }
        let place = self.cond()?;
        let op = match self.peek() {
            Some(Tok::Punct(p)) => assignment(p),
            Some(Tok::Word(_) | Tok::Lit(..)) | None => None,
        };
        let e = match op {
            Some(op) => {
                self.at += 1;
                let value = self.assign()?;
                self.node(ExprKind::Assign(op, Box::new(place), Box::new(value)))
            }
            None => place,
        };
        self.depth -= 1;
        Some(e)
    }

    /// Reads a `c ? a : b` or anything tighter.
    fn cond(&mut self) -> Option<Expr> {
        let c = self.binary(1)?;
        if !self.eat("?") {
            return Some(c);
        }
        let a = self.assign()?;
        if !self.eat(":") {
            return None;
        }
        let b = self.cond()?;
        Some(self.node(ExprKind::Cond(Box::new(c), Box::new(a), Box::new(b))))
    }

    /// Reads binary operators binding at least as tight as `min`.
    ///
    /// # Arguments
    ///
    /// * `min` - The lowest precedence to take.
    fn binary(&mut self, min: u8) -> Option<Expr> {
        let mut l = self.unary()?;
        while let Some(Tok::Punct(p)) = self.peek()
            && let Some((op, prec)) = binary(p)
            && prec >= min
        {
            self.at += 1;
            let r = self.binary(prec + 1)?;
            l = self.node(ExprKind::Binary(op, Box::new(l), Box::new(r)));
        }
        Some(l)
    }

    /// Tells whether the tokens at the reader open a cast: a parenthesized
    /// type followed by an operand.
    ///
    /// # Returns
    ///
    /// The type's text span (from the first token to past the last) and
    /// the token index after the closing parenthesis.
    fn cast_at(&self) -> Option<(usize, usize, usize)> {
        if !matches!(self.peek(), Some(Tok::Punct("("))) {
            return None;
        }
        let mut k = self.at + 1;
        let mut words = 0usize;
        let mut known = false;
        while let Some((Tok::Word(w), _)) = self.toks.get(k) {
            known |= TYPE_WORDS.contains(w)
                || w.ends_with("_t")
                || w.starts_with("__m")
                || matches!(*w, "void" | "float" | "double" | "bool");
            words += 1;
            k += 1;
        }
        let mut stars = 0usize;
        while let Some((Tok::Punct("*"), _)) = self.toks.get(k) {
            stars += 1;
            k += 1;
        }
        if words == 0 {
            return None;
        }
        if let Some(after) = self.fn_ptr_end(k) {
            k = after;
        } else if !(known || stars > 0 || words > 1) {
            return None;
        }
        let (Tok::Punct(")"), close) = *self.toks.get(k)? else {
            return None;
        };
        let operand = matches!(
            self.toks.get(k + 1),
            Some((
                Tok::Word(_)
                    | Tok::Lit(..)
                    | Tok::Punct("(" | "-" | "+" | "!" | "~" | "*" | "&" | "++" | "--"),
                _
            ))
        );
        operand.then(|| (self.toks[self.at + 1].1, close, k + 1))
    }

    /// Tells whether the tokens at `k` finish a function pointer type,
    /// `(*)(params)`, each parameter a name or words and its `*`s.
    ///
    /// # Arguments
    ///
    /// * `k` - The token index after the return type.
    ///
    /// # Returns
    ///
    /// The token index after the parameters' closing parenthesis.
    fn fn_ptr_end(&self, k: usize) -> Option<usize> {
        let punct =
            |i: usize, p: &str| matches!(self.toks.get(i), Some((Tok::Punct(q), _)) if *q == p);
        if !(punct(k, "(") && punct(k + 1, "*") && punct(k + 2, ")") && punct(k + 3, "(")) {
            return None;
        }
        let mut i = k + 4;
        loop {
            let from = i;
            while let Some((Tok::Word(_), _)) = self.toks.get(i) {
                i += 1;
            }
            if i == from {
                return None;
            }
            while punct(i, "*") {
                i += 1;
            }
            if punct(i, ")") {
                return Some(i + 1);
            }
            if !punct(i, ",") {
                return None;
            }
            i += 1;
        }
    }

    /// Reads a prefix operator, a cast, or anything tighter.
    fn unary(&mut self) -> Option<Expr> {
        self.depth += 1;
        if self.depth > DEPTH_MAX {
            return None;
        }
        let e = if let Some((from, to, next)) = self.cast_at() {
            self.at = next;
            let text = self.text(from, to)?;
            let operand = self.unary()?;
            self.node(ExprKind::Cast(CTy::parse(text), Box::new(operand)))
        } else {
            let op = match self.peek() {
                Some(Tok::Punct("-")) => Some(UnOp::Neg),
                Some(Tok::Punct("+")) => Some(UnOp::Plus),
                Some(Tok::Punct("~")) => Some(UnOp::BitNot),
                Some(Tok::Punct("!")) => Some(UnOp::Not),
                Some(Tok::Punct("*")) => Some(UnOp::Deref),
                Some(Tok::Punct("&")) => Some(UnOp::AddrOf),
                Some(Tok::Punct("++")) => Some(UnOp::PreInc),
                Some(Tok::Punct("--")) => Some(UnOp::PreDec),
                Some(Tok::Punct(_) | Tok::Word(_) | Tok::Lit(..)) | None => None,
            };
            match op {
                Some(op) => {
                    self.at += 1;
                    let operand = self.unary()?;
                    self.node(ExprKind::Unary(op, Box::new(operand)))
                }
                None => self.postfix()?,
            }
        };
        self.depth -= 1;
        Some(e)
    }

    /// The source text between two byte offsets of the expression.
    ///
    /// # Arguments
    ///
    /// * `from` - The first byte.
    /// * `to` - Past the last byte.
    fn text(&self, from: usize, to: usize) -> Option<&'t str> {
        self.src.get(from..to)
    }

    /// Reads a primary expression and the calls, indexes, members and
    /// postfix steps after it.
    fn postfix(&mut self) -> Option<Expr> {
        let mut e = match self.peek()? {
            Tok::Word(w) => {
                self.at += 1;
                self.node(ExprKind::Name(Name::of(w)))
            }
            Tok::Lit(kind, text) => {
                self.at += 1;
                self.node(ExprKind::Lit(Literal {
                    kind,
                    text: text.to_owned(),
                }))
            }
            Tok::Punct("(") => {
                self.at += 1;
                let inner = self.assign()?;
                if !self.eat(")") {
                    return None;
                }
                self.node(ExprKind::Paren(Box::new(inner)))
            }
            Tok::Punct(_) => return None,
        };
        loop {
            if self.eat("(") {
                let mut args = Vec::new();
                if !self.eat(")") {
                    loop {
                        args.push(self.assign()?);
                        if self.eat(")") {
                            break;
                        }
                        if !self.eat(",") {
                            return None;
                        }
                    }
                }
                e = self.node(ExprKind::Call(Box::new(e), args));
            } else if self.eat("[") {
                let i = self.assign()?;
                if !self.eat("]") {
                    return None;
                }
                e = self.node(ExprKind::Index(Box::new(e), Box::new(i)));
            } else if matches!(self.peek(), Some(Tok::Punct("->" | ".")))
                && let Some((Tok::Word(field), _)) = self.toks.get(self.at + 1)
            {
                let arrow = self.eat("->");
                self.at += usize::from(!arrow) + 1;
                e = self.node(ExprKind::Member {
                    base: Box::new(e),
                    field: Name::of(field),
                    arrow,
                });
            } else if self.eat("++") {
                e = self.node(ExprKind::Postfix(PostOp::Inc, Box::new(e)));
            } else if self.eat("--") {
                e = self.node(ExprKind::Postfix(PostOp::Dec, Box::new(e)));
            } else {
                return Some(e);
            }
        }
    }
}
