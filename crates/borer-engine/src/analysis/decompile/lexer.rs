//! The tokens of one line of decompiled text, as C reads them, and the
//! whitespace and comments between them.
//!
//! One scanner reads a line ([`scan`]): every byte lands in one piece, in
//! order, so the pieces spell the line back. The text passes read the
//! tokens alone ([`lex`]), the same scanner with the whitespace and the
//! comments left out.

use std::ops::Range;

/// The operators and punctuation of more than one character, longest first.
const PUNCTS: [&str; 22] = [
    "<<=", ">>=", "->", "++", "--", "<<", ">>", "<=", ">=", "==", "!=", "&&", "||", "+=", "-=",
    "*=", "/=", "%=", "&=", "|=", "^=", "::",
];

/// What a token is.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Lex {
    /// An identifier.
    Name,
    /// A numeric literal.
    Number,
    /// A string or character literal.
    Literal,
    /// An operator or punctuation.
    Punct,
}

/// What a run of a line's bytes is: a token, or what lies between tokens.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Piece {
    /// A run of whitespace.
    Space,
    /// `//` to the end of the line, `/*` through its `*/`, or a `/*` the
    /// line does not close, to the end of the line.
    Comment,
    /// A token.
    Token(Lex),
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

/// Reads one line as the pieces that tile it ([`scan`]).
#[derive(Debug, Clone)]
pub(crate) struct Scan<'t> {
    /// The line.
    line: &'t str,
    /// Where the next piece starts.
    at: usize,
}

/// Returns the pieces of a line from byte `at` on, each with the bytes it
/// spans.
///
/// The pieces tile what they read: each starts where the one before
/// ended and the last ends the line, and from a character boundary each
/// ends on one.
///
/// # Arguments
///
/// * `line` - One line of the text.
/// * `at` - Where to start, a character boundary: 0 for the whole line.
///
/// # Returns
///
/// The scanner, which yields each piece in order.
pub(crate) fn scan(line: &str, at: usize) -> Scan<'_> {
    Scan { line, at }
}

impl Iterator for Scan<'_> {
    type Item = (Piece, Range<usize>);

    fn next(&mut self) -> Option<Self::Item> {
        let (b, i) = (self.line.as_bytes(), self.at);
        let &c = b.get(i)?;
        let rest = self.line.get(i..).unwrap_or("");
        let (piece, end) = if c.is_ascii_whitespace() {
            let run = rest.bytes().take_while(u8::is_ascii_whitespace).count();
            (Piece::Space, i + run)
        } else if rest.starts_with("//") {
            (Piece::Comment, b.len())
        } else if rest.starts_with("/*") {
            let close = rest.get(2..).and_then(|r| r.find("*/"));
            (Piece::Comment, close.map_or(b.len(), |k| i + k + 4))
        } else {
            let (lex, end) = token(b, rest, i, c);
            (Piece::Token(lex), end)
        };
        self.at = end;
        Some((piece, i..end))
    }
}

/// Returns the token a line has at byte `i`, which is no whitespace and
/// opens no comment, and where it ends.
///
/// # Arguments
///
/// * `b` - The line's bytes.
/// * `rest` - The line from `i` on.
/// * `i` - Where the token starts.
/// * `c` - The byte there.
///
/// # Returns
///
/// What the token is, and one past its last byte: a literal that does not
/// end runs to the end of the line.
fn token(b: &[u8], rest: &str, i: usize, c: u8) -> (Lex, usize) {
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
        return (Lex::Literal, j.min(b.len()));
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
        return (Lex::Number, j);
    }
    if c.is_ascii_alphabetic() || c == b'_' {
        let mut j = i + 1;
        while b
            .get(j)
            .is_some_and(|d| d.is_ascii_alphanumeric() || *d == b'_')
        {
            j += 1;
        }
        return (Lex::Name, j);
    }
    let len = PUNCTS.iter().find(|p| rest.starts_with(**p)).map_or_else(
        || rest.chars().next().map_or(1, char::len_utf8),
        |p| p.len(),
    );
    (Lex::Punct, i + len)
}

/// Splits a line into tokens, leaving out whitespace and comments: the
/// tokens of [`scan`], in one pass.
///
/// # Arguments
///
/// * `line` - One line of the text.
///
/// # Returns
///
/// The tokens in order; a comment that does not end ends the line.
pub(super) fn lex(line: &str) -> Vec<Tok> {
    scan(line, 0)
        .filter_map(|(piece, span)| match piece {
            Piece::Token(lex) => Some(Tok {
                lex,
                at: span.start,
                end: span.end,
            }),
            Piece::Space | Piece::Comment => None,
        })
        .collect()
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

#[cfg(test)]
mod tests {
    use super::{Lex, Piece, lex, scan};

    /// The pieces of a line tile it on character boundaries, whitespace and
    /// comments included, and the tokens are the rest.
    ///
    /// Each line's tokens are pinned here to the very ones [`lex`] gave
    /// before [`scan`] kept whitespace and comments.
    ///
    /// A closed comment ends at its `*/`, an open one and a `//` one at the
    /// end of the line; a literal's escape and a character past ASCII stay
    /// inside their piece.
    ///
    /// # Panics
    ///
    /// When a piece is lost, overlaps another or splits a character, or a
    /// token is not the one pinned.
    #[test]
    fn the_pieces_tile_the_line_and_the_tokens_are_the_rest() {
        let lines = [
            "  x->f = g(\"a\\\"é\", 1.5e-3); // note",
            "a /* b */ c /* open",
            "\t*/ L\"wide\" naïve ;",
            "",
        ];
        let (name, number, literal, punct) = (Lex::Name, Lex::Number, Lex::Literal, Lex::Punct);
        let pinned: [&[(Lex, usize, usize)]; 4] = [
            &[
                (name, 2, 3),
                (punct, 3, 5),
                (name, 5, 6),
                (punct, 7, 8),
                (name, 9, 10),
                (punct, 10, 11),
                (literal, 11, 18),
                (punct, 18, 19),
                (number, 20, 26),
                (punct, 26, 27),
                (punct, 27, 28),
            ],
            &[(name, 0, 1), (name, 10, 11)],
            &[
                (punct, 1, 2),
                (punct, 2, 3),
                (literal, 4, 11),
                (name, 12, 14),
                (punct, 14, 16),
                (name, 16, 18),
                (punct, 19, 20),
            ],
            &[],
        ];
        for (line, want) in lines.into_iter().zip(pinned) {
            let pieces: Vec<(Piece, std::ops::Range<usize>)> = scan(line, 0).collect();
            let mut at = 0;
            for (_, span) in &pieces {
                assert_eq!(span.start, at, "{line:?}");
                assert!(
                    span.end > span.start && line.is_char_boundary(span.end),
                    "{line:?}"
                );
                at = span.end;
            }
            assert_eq!(at, line.len(), "{line:?}");
            let tokens: Vec<(Lex, usize, usize)> = pieces
                .iter()
                .filter_map(|(p, s)| match p {
                    Piece::Token(lex) => Some((*lex, s.start, s.end)),
                    Piece::Space | Piece::Comment => None,
                })
                .collect();
            assert_eq!(tokens, want, "{line:?}");
            let lexed: Vec<(Lex, usize, usize)> =
                lex(line).iter().map(|t| (t.lex, t.at, t.end)).collect();
            assert_eq!(lexed, want, "{line:?}");
        }
        let comments: Vec<&str> = scan(lines[1], 0)
            .filter(|(p, _)| *p == Piece::Comment)
            .filter_map(|(_, s)| lines[1].get(s))
            .collect();
        assert_eq!(comments, ["/* b */", "/* open"]);
        assert_eq!(
            scan(lines[0], 0).last(),
            Some((Piece::Comment, 29..36)),
            "{:?}",
            lines[0]
        );
    }
}
