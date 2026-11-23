//! Which sums on a variable count bytes: the one rule the byte arithmetic
//! pass ([`super::byte_arithmetic`]), which writes the decompiled text in
//! GNU C, and the C export, which writes standard C, share.

use super::*;
use crate::analysis::decompile::lexer::{self, Lex};

/// The pointees whose arithmetic both dialects count in bytes.
pub(super) const BYTE_POINTEES: [&str; 6] = [
    "uint8_t",
    "int8_t",
    "char",
    "signed char",
    "unsigned char",
    "bool",
];

/// The C a text is written in, which decides how a `void *` steps.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(in crate::analysis::decompile) enum Dialect {
    /// GNU C, the decompiled text's: a `void *` steps by bytes.
    Gnu,
    /// Standard C, the export's: a `void *` has no arithmetic.
    Iso,
}

/// Tells whether `value + n` is `n` bytes past `value` for a value of a
/// declared type: an integer, whose sum stays in its own arithmetic, a
/// pointer to a byte, and in GNU C a `void *`.
///
/// A pointer to anything wider, a floating type and a type this does not
/// know are not: their sums are spelled through `(uintptr_t)`.
///
/// # Arguments
///
/// * `ty` - The declared type, as the text spells it.
/// * `dialect` - The C the sum is written in.
pub(in crate::analysis::decompile) fn steps_bytes(ty: &str, dialect: Dialect) -> bool {
    let ty = ty.trim();
    match pointee_of(ty) {
        Some(p) => BYTE_POINTEES.contains(&p) || (p == "void" && dialect == Dialect::Gnu),
        None => {
            BYTE_POINTEES.contains(&ty)
                || SCALARS.iter().any(|(names, cast, size)| {
                    names.contains(&ty) && *size <= 8 && cast.contains("int")
                })
        }
    }
}

/// Rewrites a GNU C text's arithmetic on a `void *` as standard C, with the
/// pointer type and the GNU meaning kept.
///
/// Each `void *` parameter or local (a pointer whose sum counts bytes in
/// GNU C but not in standard C, [`steps_bytes`]) is summed through `char
/// *`, which steps bytes as GNU C steps a `void *`:
///
/// - `p + n`, `p - n` and a chain `p + n - m` become `(void *)((char *)p +
///   n - m)`, still a `void *`; so does a parenthesized `void *` sum that
///   begins such a chain, after an operator, a delimiter or `return`,
///   `case`, `else` or `do`;
/// - `p - q` of two of them becomes `(char *)p - (char *)q`, the signed
///   difference GNU C gives, and so does a chain holding such a
///   difference, without the `void *` cast;
/// - `s - p`, a `void *` subtracted from a declared byte pointer, becomes
///   `s - (char *)p`;
/// - `p += n` and `p -= n` become `p = (void *)((char *)p + (n))`,
///   parenthesized when they stand inside an expression;
/// - `p++;`, `++p;`, `p--;` and `--p;` as statements become `p = (void
///   *)((char *)p + 1);` or `- 1`;
/// - `&p[i]` becomes `(void *)((char *)p + i)`.
///
/// A chain is rewritten all or nothing: only when every operand is typed
/// from the declarations ([`Kind`]: a name the signature or a declaration
/// types, a number, a cast, a load, or a parenthesized sum of those), and
/// then every `void *` in it is cast; a chain with an operand it cannot
/// type, or a `void *` added to a pointer, keeps every token as written. So is a `void *` added to a number
/// from the right (`n + p`, `x + p + 4`), a step inside a larger
/// expression (`f(p++)`), `p[i]` without `&`, a global `void *` (its
/// declaration carries an address comment, which this does not read), a
/// `void **`, and everything in a literal or a comment. Each line stays a
/// line.
///
/// # Arguments
///
/// * `text` - A finished decompiled function, header lines first.
///
/// # Returns
///
/// The text with every rewrite above applied; the arithmetic left as
/// written stays GNU C.
pub(in crate::analysis::decompile) fn iso_arithmetic(text: &str) -> String {
    let differs = |ty: &str| steps_bytes(ty, Dialect::Gnu) && !steps_bytes(ty, Dialect::Iso);
    let (mut voids, mut ints, mut bytes) = (BTreeSet::new(), BTreeSet::new(), BTreeSet::new());
    let mut note = |name: &str, ty: &str| {
        if differs(ty) {
            voids.insert(name.to_owned());
        } else if !ty.contains('*') {
            ints.insert(name.to_owned());
        } else if steps_bytes(ty, Dialect::Iso) {
            bytes.insert(name.to_owned());
        }
    };
    for (name, ty) in signature_params(text) {
        note(&name, &ty);
    }
    for (ty, items) in text.lines().filter_map(|l| vars::declaration(l.trim())) {
        for (stars, name) in items {
            note(name, &format!("{ty} {stars}"));
        }
    }
    if voids.is_empty() {
        return text.to_owned();
    }
    let lines: Vec<String> = text
        .lines()
        .map(|l| {
            if l.trim_start().starts_with("//") {
                l.to_owned()
            } else {
                Iso {
                    voids: &voids,
                    ints: &ints,
                    bytes: &bytes,
                }
                .rewrite(l)
            }
        })
        .collect();
    rejoin(&lines, text)
}

/// The tokens that end an operand of `+` or `-` at its own depth: every
/// operator that binds as loosely or more loosely, and the closers.
const LOOSER: [&str; 30] = [
    "+", "-", "<<", ">>", "<", ">", "<=", ">=", "==", "!=", "&", "^", "|", "&&", "||", "?", ":",
    "=", "+=", "-=", "*=", "/=", "%=", "&=", "|=", "^=", "<<=", ">>=", ",", ";",
];

/// The `void *` variables of one function, and the rewriting of their
/// arithmetic ([`iso_arithmetic`]).
struct Iso<'v> {
    /// The names declared `void *`.
    voids: &'v BTreeSet<String>,
    /// The names declared as no pointer.
    ints: &'v BTreeSet<String>,
    /// The names declared as pointers to a byte.
    bytes: &'v BTreeSet<String>,
}

/// What an operand of `+` or `-` is, as far as the text tells.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Kind {
    /// A `void *`.
    Pointer,
    /// No pointer: a number, or the difference of two pointers.
    Number,
    /// Something the declarations do not type.
    Unknown,
}

/// One piece of code and its tokens.
struct Code<'s> {
    /// The code.
    s: &'s str,
    /// Its tokens.
    toks: Vec<lexer::Tok>,
}

impl<'s> Code<'s> {
    /// Returns the text of token `k`, empty past the end.
    ///
    /// # Arguments
    ///
    /// * `k` - The token.
    fn word(&self, k: usize) -> &'s str {
        self.toks
            .get(k)
            .and_then(|t| self.s.get(t.at..t.end))
            .unwrap_or("")
    }

    /// Tells whether token `k` is of kind `l`.
    ///
    /// # Arguments
    ///
    /// * `k` - The token.
    /// * `l` - The kind.
    fn is(&self, k: usize, l: Lex) -> bool {
        self.toks.get(k).is_some_and(|t| t.lex == l)
    }

    /// Tells whether token `k` is the punctuation `p`.
    ///
    /// # Arguments
    ///
    /// * `k` - The token.
    /// * `p` - The punctuation.
    fn punct(&self, k: usize, p: &str) -> bool {
        self.is(k, Lex::Punct) && self.word(k) == p
    }

    /// Returns the code tokens `a..b` span.
    ///
    /// # Arguments
    ///
    /// * `a`, `b` - The first token and one past the last.
    fn span(&self, a: usize, b: usize) -> &'s str {
        let (Some(x), Some(y)) = (
            self.toks.get(a),
            b.checked_sub(1).and_then(|e| self.toks.get(e)),
        ) else {
            return "";
        };
        self.s.get(x.at..y.end).unwrap_or("")
    }

    /// Returns the index of the token closing the bracket at `open`.
    ///
    /// # Arguments
    ///
    /// * `open` - The index of a `(` or `[`.
    fn closing(&self, open: usize) -> Option<usize> {
        closing(&self.toks, self.s, open)
    }

    /// Tells whether token `k` opens a statement: after `;`, a brace,
    /// `else`, or the condition of an `if`, `while` or `for`.
    ///
    /// # Arguments
    ///
    /// * `k` - The token.
    fn starts(&self, k: usize) -> bool {
        k.checked_sub(1).is_none_or(|j| {
            [";", "{", "}"].iter().any(|p| self.punct(j, p))
                || self.word(j) == "else"
                || (self.punct(j, ")")
                    && (0..j)
                        .rev()
                        .find(|&o| self.closing(o) == Some(j))
                        .and_then(|o| o.checked_sub(1))
                        .is_some_and(|o| matches!(self.word(o), "if" | "while" | "for")))
        })
    }

    /// Tells whether token `k` can begin an operand of `+` or `-` that
    /// binds no tighter: no cast, member access, unary operator or left
    /// operand of `+` or `-` stands before it.
    ///
    /// # Arguments
    ///
    /// * `k` - The token.
    fn free(&self, k: usize) -> bool {
        k.checked_sub(1).is_none_or(|j| {
            let w = self.word(j);
            if self.is(j, Lex::Punct) {
                ![
                    ")", "]", ".", "->", "*", "&", "!", "~", "++", "--", "+", "-",
                ]
                .contains(&w)
            } else {
                w != "sizeof"
            }
        })
    }
}

/// The keywords a parenthesized operand may follow, which are no callee.
const KEYWORDS: [&str; 4] = ["return", "case", "else", "do"];

/// What a rewriting rule makes of the code at one token.
enum Found {
    /// No rule applies there.
    Nothing,
    /// The tokens up to this one stay as written.
    Keep(usize),
    /// The tokens up to this one become this text.
    Text(String, usize),
}

impl Iso<'_> {
    /// Returns a piece of code with its `void *` arithmetic in standard C.
    ///
    /// # Arguments
    ///
    /// * `s` - A line, or an operand cut from one.
    fn rewrite(&self, s: &str) -> String {
        let code = Code {
            s,
            toks: lexer::lex(s),
        };
        let mut out = String::with_capacity(s.len() + 32);
        let (mut cursor, mut k) = (0, 0);
        while k < code.toks.len() {
            match self.at(&code, k) {
                Found::Nothing => k += 1,
                Found::Keep(next) => k = next.max(k + 1),
                Found::Text(text, next) => {
                    let Some(first) = code.toks.get(k) else {
                        break;
                    };
                    out.push_str(s.get(cursor..first.at).unwrap_or_default());
                    out.push_str(&text);
                    cursor = next
                        .checked_sub(1)
                        .and_then(|e| code.toks.get(e))
                        .map_or(s.len(), |t| t.end);
                    k = next;
                }
            }
        }
        out.push_str(s.get(cursor..).unwrap_or_default());
        out
    }

    /// Returns what the rules make of the code at token `k`.
    ///
    /// # Arguments
    ///
    /// * `code` - The code.
    /// * `k` - The token.
    fn at(&self, code: &Code<'_>, k: usize) -> Found {
        let named = |k: usize| code.is(k, Lex::Name) && self.voids.contains(code.word(k));
        let stepped = ["+=", "-=", "++", "--"]
            .iter()
            .any(|p| code.punct(k + 1, p));
        if named(k) && (code.free(k) || (code.starts(k) && stepped)) {
            return self.at_name(code, k);
        }
        if code.is(k, Lex::Name) && self.bytes.contains(code.word(k)) && code.free(k) {
            return self.chain(code, k + 1, code.word(k), true);
        }
        let callee = k
            .checked_sub(1)
            .is_some_and(|j| code.is(j, Lex::Name) && !KEYWORDS.contains(&code.word(j)));
        if code.punct(k, "(") && code.free(k) && !callee {
            let Some(c) = code.closing(k) else {
                return Found::Nothing;
            };
            let follows = code.punct(c + 1, "+") || code.punct(c + 1, "-");
            if !follows || self.kind(code.span(k, c + 1)) != Kind::Pointer {
                return Found::Nothing;
            }
            let base = format!("(char *){}", whole(&self.rewrite(code.span(k, c + 1))));
            return self.chain(code, c + 1, &base, false);
        }
        if (code.punct(k, "++") || code.punct(k, "--"))
            && named(k + 1)
            && code.starts(k)
            && code.punct(k + 2, ";")
        {
            let sign = if code.punct(k, "++") { '+' } else { '-' };
            let p = code.word(k + 1);
            return Found::Text(format!("{p} = (void *)((char *){p} {sign} 1)"), k + 2);
        }
        let after = k.checked_sub(1).is_none_or(|j| {
            (code.is(j, Lex::Punct) && ![")", "]"].contains(&code.word(j)))
                || KEYWORDS.contains(&code.word(j))
        });
        if code.punct(k, "&") && named(k + 1) && code.punct(k + 2, "[") && after {
            let Some(c) = code.closing(k + 2) else {
                return Found::Nothing;
            };
            let p = code.word(k + 1);
            let i = self.rewrite(code.span(k + 3, c));
            return Found::Text(format!("(void *)((char *){p} + {})", whole(&i)), c + 1);
        }
        Found::Nothing
    }

    /// Returns what the rules make of the arithmetic a `void *` named at
    /// token `k` begins: a step, a compound assignment, or a chain.
    ///
    /// # Arguments
    ///
    /// * `code` - The code.
    /// * `k` - The name's token.
    fn at_name(&self, code: &Code<'_>, k: usize) -> Found {
        let (p, statement) = (code.word(k), code.starts(k));
        if code.punct(k + 1, "+=") || code.punct(k + 1, "-=") {
            let sign = if code.punct(k + 1, "+=") { '+' } else { '-' };
            let end = assignment_end(&code.toks, code.s, k + 2);
            let step = self.rewrite(code.span(k + 2, end));
            let set = format!("{p} = (void *)((char *){p} {sign} {})", whole(&step));
            let alone = statement && (end == code.toks.len() || code.punct(end, ";"));
            return Found::Text(if alone { set } else { format!("({set})") }, end);
        }
        if (code.punct(k + 1, "++") || code.punct(k + 1, "--"))
            && statement
            && code.punct(k + 2, ";")
        {
            let sign = if code.punct(k + 1, "++") { '+' } else { '-' };
            return Found::Text(format!("{p} = (void *)((char *){p} {sign} 1)"), k + 2);
        }
        self.chain(code, k + 1, &format!("(char *){p}"), false)
    }

    /// Returns what the rules make of a chain of `+` and `-` operands that
    /// follows a pointer base, all or nothing: rewritten only when every
    /// operand is typed ([`Kind`]), a `void *` only subtracted, else kept
    /// as written whole.
    ///
    /// # Arguments
    ///
    /// * `code` - The code.
    /// * `j` - The token after the base.
    /// * `base` - The base, as a `char *`.
    /// * `bytes` - Whether the base is a byte pointer already, whose chain
    ///   is rewritten only when it subtracts a `void *`.
    fn chain(&self, code: &Code<'_>, mut j: usize, base: &str, bytes: bool) -> Found {
        let (first, mut terms, mut difference, mut typed) = (j, String::new(), false, true);
        while code.punct(j, "+") || code.punct(j, "-") {
            let minus = code.punct(j, "-");
            let end = operand_end(&code.toks, code.s, j + 1);
            if end == j + 1 {
                break;
            }
            let operand = code.span(j + 1, end);
            match (minus, self.kind(operand)) {
                (true, Kind::Pointer) => {
                    difference = true;
                    let text = self.rewrite(operand);
                    terms.push_str(&format!(" - (char *){}", whole(&text)));
                }
                (_, Kind::Number) => {
                    let text = self.rewrite(operand);
                    terms.push_str(&format!(" {} {text}", if minus { '-' } else { '+' }));
                }
                (false, Kind::Pointer) | (_, Kind::Unknown) => typed = false,
            }
            j = end;
        }
        match (j == first, typed, difference, bytes) {
            (true, ..) | (false, true, false, true) => Found::Nothing,
            (false, false, ..) => Found::Keep(j),
            (false, true, true, _) => Found::Text(format!("{base}{terms}"), j),
            (false, true, false, false) => Found::Text(format!("(void *)({base}{terms})"), j),
        }
    }

    /// Returns what an expression is ([`Kind`]): a `void *` for one such
    /// pointer plus or minus numbers, a number for no pointer or the
    /// difference of two, unknown for anything else.
    ///
    /// # Arguments
    ///
    /// * `code` - The expression.
    fn kind(&self, code: &str) -> Kind {
        let code = unwrap(code);
        let toks = lexer::lex(code);
        let word = |k: usize| {
            toks.get(k)
                .and_then(|t| code.get(t.at..t.end))
                .unwrap_or("")
        };
        let (mut sign, mut from, mut depth, mut ended) = (1i32, 0usize, 0usize, false);
        let mut terms: Vec<(i32, usize, usize)> = Vec::new();
        for (k, t) in toks.iter().enumerate() {
            let (w, punct) = (word(k), t.lex == Lex::Punct);
            match w {
                "(" | "[" if punct => depth += 1,
                ")" | "]" if punct => depth = depth.saturating_sub(1),
                "+" | "-" if punct && depth == 0 && ended => {
                    terms.push((sign, from, k));
                    sign = if w == "-" { -1 } else { 1 };
                    from = k + 1;
                }
                _ => {}
            }
            ended = !punct
                || (matches!(w, ")" | "]" | "++" | "--")
                    && !(w == ")" && cast_ends(&toks, code, k)));
        }
        terms.push((sign, from, toks.len()));
        if let [(_, a, b)] = terms[..] {
            return self.term(&toks, code, a, b);
        }
        let mut net = 0i32;
        for (sign, a, b) in terms {
            match self.term(&toks, code, a, b) {
                Kind::Pointer => net += sign,
                Kind::Number => {}
                Kind::Unknown => return Kind::Unknown,
            }
        }
        match net {
            0 => Kind::Number,
            1 => Kind::Pointer,
            _ => Kind::Unknown,
        }
    }

    /// Returns what one term, tokens `a..b` of `code`, is ([`Iso::kind`]):
    /// a name by its declaration, a number, a parenthesized expression by
    /// its own kind, a cast or a load by its type.
    ///
    /// # Arguments
    ///
    /// * `toks`, `code` - The tokens and the code they span.
    /// * `a`, `b` - The term's tokens.
    fn term(&self, toks: &[lexer::Tok], code: &str, a: usize, b: usize) -> Kind {
        let words: Vec<&str> = toks
            .get(a..b)
            .unwrap_or_default()
            .iter()
            .filter_map(|t| code.get(t.at..t.end))
            .collect();
        let close = |o: usize| closing(toks, code, o);
        let inside = |x: usize, y: usize| words.get(x - a..y - a).unwrap_or_default();
        let parts = factors(toks, code, a, b);
        if parts.len() > 1 {
            let numbers = parts
                .iter()
                .all(|&(x, y)| self.term(toks, code, x, y) == Kind::Number);
            return if numbers { Kind::Number } else { Kind::Unknown };
        }
        match words.as_slice() {
            [w] if self.voids.contains(*w) => Kind::Pointer,
            [w] if self.ints.contains(*w) || w.starts_with(|c: char| c.is_ascii_digit()) => {
                Kind::Number
            }
            ["(", ..] if close(a) == Some(b - 1) => {
                let (Some(f), Some(l)) = (toks.get(a), toks.get(b - 1)) else {
                    return Kind::Unknown;
                };
                self.kind(code.get(f.at..l.end).unwrap_or_default())
            }
            ["(", ..] => match close(a) {
                Some(c)
                    if cast_inside(toks, code, a + 1, c) && !inside(a + 1, c).contains(&"*") =>
                {
                    Kind::Number
                }
                _ => Kind::Unknown,
            },
            ["*", "(", ..] => match close(a + 1) {
                Some(c)
                    if cast_inside(toks, code, a + 2, c)
                        && inside(a + 2, c).iter().filter(|w| **w == "*").count() == 1
                        && !inside(a + 2, c).contains(&"void") =>
                {
                    Kind::Number
                }
                _ => Kind::Unknown,
            },
            _ => {
                let typed = toks.get(a..b).unwrap_or_default().iter().all(|t| {
                    let w = code.get(t.at..t.end).unwrap_or_default();
                    match t.lex {
                        Lex::Name => {
                            self.ints.contains(w) || w.ends_with("_t") || TYPE_WORDS.contains(&w)
                        }
                        Lex::Number => true,
                        Lex::Literal => false,
                        Lex::Punct => matches!(w, "*" | "/" | "%" | "(" | ")" | "~" | "<<" | ">>"),
                    }
                });
                if typed { Kind::Number } else { Kind::Unknown }
            }
        }
    }
}

/// Returns the factors of a term, tokens `a..b`: its parts between the
/// `*`, `/` and `%` that multiply at its own depth.
///
/// # Arguments
///
/// * `toks`, `code` - The tokens and the code they span.
/// * `a`, `b` - The term's tokens.
fn factors(toks: &[lexer::Tok], code: &str, a: usize, b: usize) -> Vec<(usize, usize)> {
    let (mut out, mut from, mut depth, mut ended) = (Vec::new(), a, 0usize, false);
    for k in a..b {
        let Some(t) = toks.get(k) else {
            break;
        };
        let (w, punct) = (
            code.get(t.at..t.end).unwrap_or_default(),
            t.lex == Lex::Punct,
        );
        match w {
            "(" | "[" if punct => depth += 1,
            ")" | "]" if punct => depth = depth.saturating_sub(1),
            "*" | "/" | "%" if punct && depth == 0 && ended => {
                out.push((from, k));
                from = k + 1;
            }
            _ => {}
        }
        ended = !punct
            || (matches!(w, ")" | "]" | "++" | "--") && !(w == ")" && cast_ends(toks, code, k)));
    }
    out.push((from, b));
    out
}

/// Tells whether the `)` at token `k` closes a cast.
///
/// # Arguments
///
/// * `toks`, `code` - The tokens and the code they span.
/// * `k` - The index of a `)`.
fn cast_ends(toks: &[lexer::Tok], code: &str, k: usize) -> bool {
    (0..k)
        .rev()
        .find(|&o| closing(toks, code, o) == Some(k))
        .is_some_and(|o| cast_inside(toks, code, o + 1, k))
}

/// Returns an expression without the parentheses that enclose it whole.
///
/// # Arguments
///
/// * `code` - The expression.
fn unwrap(code: &str) -> &str {
    let mut code = code.trim();
    loop {
        let toks = lexer::lex(code);
        let enclosed = toks
            .first()
            .is_some_and(|t| code.get(t.at..t.end) == Some("("))
            && closing(&toks, code, 0) == Some(toks.len().saturating_sub(1));
        match code
            .get(1..code.len().saturating_sub(1))
            .filter(|_| enclosed)
        {
            Some(inner) => code = inner.trim(),
            None => return code,
        }
    }
}

/// Type words a cast's parentheses open with.
const TYPE_WORDS: [&str; 12] = [
    "char", "short", "int", "long", "unsigned", "signed", "void", "bool", "float", "double",
    "struct", "const",
];

/// Returns the index of the token closing the bracket opened at `open`.
///
/// # Arguments
///
/// * `toks`, `s` - The tokens and the code they span.
/// * `open` - The index of a `(` or `[`.
fn closing(toks: &[lexer::Tok], s: &str, open: usize) -> Option<usize> {
    let mut depth = 0usize;
    for (k, t) in toks.iter().enumerate().skip(open) {
        match s.get(t.at..t.end) {
            Some("(" | "[") if t.lex == Lex::Punct => depth += 1,
            Some(")" | "]") if t.lex == Lex::Punct => {
                depth = depth.checked_sub(1)?;
                if depth == 0 {
                    return Some(k);
                }
            }
            _ => {}
        }
    }
    None
}

/// Tells whether tokens `a..b` spell a type, the inside of a cast.
///
/// # Arguments
///
/// * `toks`, `s` - The tokens and the code they span.
/// * `a`, `b` - The tokens inside the parentheses.
fn cast_inside(toks: &[lexer::Tok], s: &str, a: usize, b: usize) -> bool {
    let words: Vec<&str> = toks
        .get(a..b)
        .unwrap_or_default()
        .iter()
        .filter_map(|t| s.get(t.at..t.end))
        .collect();
    words
        .first()
        .is_some_and(|w| w.ends_with("_t") || TYPE_WORDS.contains(w))
        && words
            .iter()
            .all(|w| *w == "*" || w.chars().all(|c| c.is_ascii_alphanumeric() || c == '_'))
}

/// Returns one past the last token of the operand of `+` or `-` that
/// starts at token `j`: a product of unary, cast and postfix terms.
///
/// # Arguments
///
/// * `toks`, `s` - The tokens and the code they span.
/// * `j` - The operand's first token.
fn operand_end(toks: &[lexer::Tok], s: &str, j: usize) -> usize {
    let (mut depth, mut expect, mut k) = (0usize, true, j);
    while let Some(t) = toks.get(k) {
        let w = s.get(t.at..t.end).unwrap_or_default();
        if t.lex != Lex::Punct {
            expect &= depth > 0;
            k += 1;
            continue;
        }
        match w {
            "(" if depth == 0 && expect => match closing(toks, s, k) {
                Some(c) if cast_inside(toks, s, k + 1, c) => {
                    k = c;
                }
                _ => depth += 1,
            },
            "(" | "[" => depth += 1,
            ")" | "]" => {
                let Some(d) = depth.checked_sub(1) else {
                    break;
                };
                depth = d;
                expect &= depth > 0;
            }
            _ if depth > 0 => {}
            "+" | "-" | "*" | "&" if expect => {}
            "!" | "~" | "++" | "--" => {}
            "*" | "/" | "%" | "->" | "." => expect = true,
            _ if LOOSER.contains(&w) => break,
            _ => {}
        }
        k += 1;
    }
    k
}

/// Returns one past the last token of the right side of an assignment
/// that starts at token `j`: up to a `,`, `;` or closer at its depth.
///
/// # Arguments
///
/// * `toks`, `s` - The tokens and the code they span.
/// * `j` - The right side's first token.
fn assignment_end(toks: &[lexer::Tok], s: &str, j: usize) -> usize {
    let (mut depth, mut k) = (0usize, j);
    while let Some(t) = toks.get(k) {
        match s.get(t.at..t.end).filter(|_| t.lex == Lex::Punct) {
            Some("(" | "[" | "{") => depth += 1,
            Some(")" | "]" | "}") if depth == 0 => break,
            Some(")" | "]" | "}") => depth -= 1,
            Some("," | ";") if depth == 0 => break,
            _ => {}
        }
        k += 1;
    }
    k
}

/// Returns code as one term: itself when it is one name or number or is
/// parenthesized whole, else parenthesized.
///
/// # Arguments
///
/// * `code` - The code.
fn whole(code: &str) -> String {
    let code = code.trim();
    let toks = lexer::lex(code);
    let one = match toks.as_slice() {
        [t] => matches!(t.lex, Lex::Name | Lex::Number),
        [t, ..] => {
            code.get(t.at..t.end) == Some("(") && closing(&toks, code, 0) == Some(toks.len() - 1)
        }
        [] => false,
    };
    if one {
        code.to_owned()
    } else {
        format!("({code})")
    }
}

/// The variables a declaration line types as a byte, whose address counts
/// bytes already.
///
/// # Arguments
///
/// * `text` - A decompiled function, declarations included.
pub(super) fn byte_variables(text: &str) -> BTreeSet<&str> {
    let mut out = BTreeSet::new();
    for line in text.lines() {
        let code = line.split(" //").next().unwrap_or(line).trim_end();
        let Some(names) = BYTE_POINTEES
            .iter()
            .find_map(|ty| code.strip_prefix(ty)?.strip_prefix(' ')?.strip_suffix(';'))
        else {
            continue;
        };
        if names.split(", ").all(is_ident) {
            out.extend(names.split(", "));
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
    use super::{Dialect, iso_arithmetic, steps_bytes};
    use crate::analysis::decompile::interp::{End, Script};
    use crate::analysis::{Analysis, Overlay};
    use crate::program::Program;

    /// An integer and a pointer to a byte step bytes in both dialects, a
    /// `void *` only in GNU C, and a wider pointer, a float and an unknown
    /// type in neither.
    #[test]
    fn a_sum_steps_bytes_as_the_dialect_says() {
        for ty in [
            "uint64_t",
            "uint32_t",
            "int",
            "char",
            "uint8_t *",
            "const char *",
        ] {
            assert!(
                steps_bytes(ty, Dialect::Gnu) && steps_bytes(ty, Dialect::Iso),
                "{ty}"
            );
        }
        assert!(steps_bytes("void *", Dialect::Gnu) && !steps_bytes("void *", Dialect::Iso));
        for ty in ["uint32_t *", "double", "Foo", "uint8_t **", "uint128_t"] {
            assert!(
                !steps_bytes(ty, Dialect::Gnu) && !steps_bytes(ty, Dialect::Iso),
                "{ty}"
            );
        }
    }

    /// Returns a function's last line after [`iso_arithmetic`].
    ///
    /// # Arguments
    ///
    /// * `line` - The line, under a header declaring `a1` and `var1`
    ///   `void *`, `a2` and `c` integers, `a3` a `void **` and `s` a
    ///   `char *`.
    fn iso(line: &str) -> String {
        let text = format!(
            "// signature: uint64_t f(void *a1, uint64_t a2, void **a3, uint64_t c)
void *var1;
char *s;

{line}
"
        );
        let out = iso_arithmetic(&text);
        out.lines().last().unwrap_or_default().to_owned()
    }

    /// Each kind of `void *` arithmetic is written as standard C that keeps
    /// the pointer type and the bytes GNU C steps, and what is no such
    /// arithmetic stays as it was.
    #[test]
    fn void_pointer_arithmetic_is_standard_c_of_the_same_meaning() {
        for (line, want) in [
            ("var1 = a1 + 8;", "var1 = (void *)((char *)a1 + 8);"),
            ("f(a1 + 8, 2);", "f((void *)((char *)a1 + 8), 2);"),
            ("return var1 - a1;", "return (char *)var1 - (char *)a1;"),
            ("return s - a1;", "return s - (char *)a1;"),
            ("return s + a1;", "return s + a1;"),
            ("x = a2 + a1;", "x = a2 + a1;"),
            (
                "x = *(uint32_t*)(a1 - (var1 - a1));",
                "x = *(uint32_t*)((void *)((char *)a1 - ((char *)var1 - (char *)a1)));",
            ),
            (
                "x = a1 + (var1 - a1);",
                "x = (void *)((char *)a1 + ((char *)var1 - (char *)a1));",
            ),
            (
                "x = (a1 + 4) - (var1 + 8);",
                "x = (char *)((void *)((char *)a1 + 4)) - (char *)((void *)((char *)var1 + 8));",
            ),
            (
                "x = a1 - (var1 + 4);",
                "x = (char *)a1 - (char *)((void *)((char *)var1 + 4));",
            ),
            ("x = a1 - (a2 - 4);", "x = (void *)((char *)a1 - (a2 - 4));"),
            ("x = a1 + g;", "x = a1 + g;"),
            (
                "if (c) var1 += 4;",
                "if (c) var1 = (void *)((char *)var1 + 4);",
            ),
            ("return &a1[a2];", "return (void *)((char *)a1 + a2);"),
            ("x = a1 - var1 + g;", "x = a1 - var1 + g;"),
            ("x = a1 - var1 - f(1);", "x = a1 - var1 - f(1);"),
            (
                "return (a1 + 4) - var1;",
                "return (char *)((void *)((char *)a1 + 4)) - (char *)var1;",
            ),
            (
                "return (a1 + 4) - 2;",
                "return (void *)((char *)((void *)((char *)a1 + 4)) - 2);",
            ),
            ("return a1 - var1;", "return (char *)a1 - (char *)var1;"),
            (
                "case 2: return a1 + 4;",
                "case 2: return (void *)((char *)a1 + 4);",
            ),
            (
                "else (a1 + 4) - var1;",
                "else (char *)((void *)((char *)a1 + 4)) - (char *)var1;",
            ),
            ("x = s - a1 + g;", "x = s - a1 + g;"),
            ("x = s + 4;", "x = s + 4;"),
            ("*(uint64_t*)a1 += a2;", "*(uint64_t*)a1 += a2;"),
            ("(uint8_t*)a1++;", "(uint8_t*)a1++;"),
            (
                "x = *(uint16_t*)(a1 + 4 + ((int64_t)a2 + 0x34) * 4);",
                "x = *(uint16_t*)((void *)((char *)a1 + 4 + ((int64_t)a2 + 0x34) * 4));",
            ),
            (
                "return a1 - (var1 + 4);",
                "return (char *)a1 - (char *)((void *)((char *)var1 + 4));",
            ),
            (
                "var1 -= a2 + 3;",
                "var1 = (void *)((char *)var1 - (a2 + 3));",
            ),
            (
                "var1 += c ? 1 : 2;",
                "var1 = (void *)((char *)var1 + (c ? 1 : 2));",
            ),
            (
                "var1 += 4; // note",
                "var1 = (void *)((char *)var1 + 4); // note",
            ),
            (
                "x = (var1 += 4);",
                "x = ((var1 = (void *)((char *)var1 + 4)));",
            ),
            ("var1++;", "var1 = (void *)((char *)var1 + 1);"),
            ("--var1;", "var1 = (void *)((char *)var1 - 1);"),
            ("x = &a1[a2];", "x = (void *)((char *)a1 + a2);"),
            (
                "x = *(uint8_t*)(a1 + (int32_t)a2);",
                "x = *(uint8_t*)((void *)((char *)a1 + (int32_t)a2));",
            ),
            (
                "y = a1 + 4 + a2 * 2 < c;",
                "y = (void *)((char *)a1 + 4 + a2 * 2) < c;",
            ),
            ("y = a1 + 4 - var1;", "y = (char *)a1 + 4 - (char *)var1;"),
            ("x = a3 + 1;", "x = a3 + 1;"),
            ("x = *(uint64_t*)a1 + 1;", "x = *(uint64_t*)a1 + 1;"),
            ("puts(\"a1 + 8\");", "puts(\"a1 + 8\");"),
        ] {
            assert_eq!(iso(line), want, "{line}");
        }
    }

    /// The standard C reads the same bytes as the GNU C: the text check
    /// runs both to the same answer, and no line moves.
    #[test]
    fn void_pointer_arithmetic_in_standard_c_reads_the_same_bytes() {
        let p = Program::raw_x64(&[0xc3]);
        let a = Analysis::compute(&p);
        let o = Overlay::default();
        let text = "// signature: uint64_t f(void *a1)
void *var1;

var1 = a1 + 8;
var1 += 4;
return *(uint32_t*)(a1 + 0x14) + *(uint32_t*)(var1 - 4) + (var1 - a1);
";
        let out = iso_arithmetic(text);
        assert_eq!(out.lines().count(), text.lines().count(), "{out}");
        let mem: Vec<u8> = (0..0x20).collect();
        let pokes = [(0x5000, mem)];
        let read = |t: &str| Script::read(&p, &a, &o, 0x1000, t).expect("reads");
        let run = |t: &str| read(t).run(&[0x5000], &pokes, 100).map(|r| r.end);
        assert!(matches!(run(text), Some(End::Returned(Some(_)))), "{text}");
        assert_eq!(run(&out), run(text), "{out}");
    }
}
