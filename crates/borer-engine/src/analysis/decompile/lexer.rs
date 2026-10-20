//! The tokens of one line of decompiled text, as C reads them.

/// The operators and punctuation of more than one character, longest first.
const PUNCTS: [&str; 22] = [
    "<<=", ">>=", "->", "++", "--", "<<", ">>", "<=", ">=", "==", "!=", "&&", "||", "+=", "-=",
    "*=", "/=", "%=", "&=", "|=", "^=", "::",
];

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

    /// Lists the identifiers among the line's tokens.
    ///
    /// # Returns
    ///
    /// Each identifier's text, in line order.
    pub(super) fn names(&self) -> impl Iterator<Item = &str> {
        self.toks
            .iter()
            .filter(|t| t.lex == Lex::Name)
            .filter_map(|t| self.text.get(t.at..t.end))
    }

    /// The first token at or after `from` that is the punctuation `p`.
    ///
    /// # Arguments
    ///
    /// * `from` - Where the search starts.
    /// * `p` - The punctuation.
    pub(super) fn find(&self, from: usize, p: &str) -> Option<usize> {
        (from..self.toks.len()).find(|&k| self.is(k, p))
    }

    /// The span of a statement on the line: after any `case`/`default`
    /// labels and the condition of a one-line `if`.
    pub(super) fn statement(&self) -> (usize, usize) {
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
    pub(super) fn parenthesized(&self) -> Option<(usize, usize)> {
        let open = self.find(0, "(")?;
        Some((open + 1, self.closing(open)?))
    }

    /// The span after the keyword `kw` on the line, to its end.
    ///
    /// # Arguments
    ///
    /// * `kw` - `return` or `goto`.
    pub(super) fn after(&self, kw: &str) -> Option<(usize, usize)> {
        let k = (0..self.toks.len()).find(|&k| self.word(k) == kw)?;
        Some((k + 1, self.toks.len()))
    }
}
