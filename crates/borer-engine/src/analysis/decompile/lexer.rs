//! The tokens of one line of decompiled text, as C reads them, and the
//! whitespace and comments between them.
//!
//! One scanner reads a line ([`scan`]): every byte lands in one piece, in
//! order, so the pieces spell the line back. The text passes read the
//! tokens alone ([`lex`]), the same scanner with the whitespace and the
//! comments left out. A line of C from anywhere reads as kinds of tokens
//! ([`c_kinds`]) from the line alone.

use std::ops::Range;

use super::{cir, ctext, unit};
use crate::view::Kind;

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

/// One piece of a line and the bytes it spans ([`scan`]).
pub(super) type Spanned = (Piece, Range<usize>);

/// Bits of a pointer a line read alone ([`c_kinds`]) sizes the types it
/// names for: a code block anyone wrote names no target.
const ALONE_WORD: u8 = 64;

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

/// Returns the text of piece `k` of a line, empty past the last.
///
/// # Arguments
///
/// * `line` - The line.
/// * `pieces` - Its pieces.
/// * `k` - The piece.
pub(super) fn word<'t>(line: &'t str, pieces: &[Spanned], k: usize) -> &'t str {
    pieces
        .get(k)
        .and_then(|(_, s)| line.get(s.clone()))
        .unwrap_or_default()
}

/// Returns the last piece before `k` that is code: no whitespace and no
/// comment.
///
/// # Arguments
///
/// * `pieces` - A line's pieces.
/// * `k` - The piece to look before.
pub(super) fn code_before(pieces: &[Spanned], k: usize) -> Option<usize> {
    (0..k).rev().find(|&j| {
        pieces
            .get(j)
            .is_some_and(|(p, _)| !matches!(p, Piece::Space | Piece::Comment))
    })
}

/// Returns whether piece `k` of a line names a preprocessor directive: the
/// `#` before it is the line's first code piece.
///
/// # Arguments
///
/// * `line` - The line.
/// * `pieces` - Its pieces.
/// * `k` - The name's piece.
pub(super) fn directive(line: &str, pieces: &[Spanned], k: usize) -> bool {
    code_before(pieces, k)
        .is_some_and(|j| word(line, pieces, j) == "#" && code_before(pieces, j).is_none())
}

/// Returns the kind a name has by its spelling alone: a type borer names,
/// else a keyword when it is a C keyword or word or names a directive;
/// `None` for any other name, which its place decides.
///
/// # Arguments
///
/// * `w` - The name.
/// * `directive` - Whether it names a directive ([`directive`]).
/// * `word_bits` - Bits of a pointer the types are sized for.
pub(super) fn spelled(w: &str, directive: bool, word_bits: u8) -> Option<Kind> {
    if ctext::named_type(w, word_bits).is_some() {
        Some(Kind::Type)
    } else if directive || cir::KEYWORDS.contains(&w) || unit::C_WORDS.contains(&w) {
        Some(Kind::Keyword)
    } else {
        None
    }
}

/// Returns whether a name after `prev` names a tagged type: `prev` is
/// `struct`, `union` or `enum`.
///
/// # Arguments
///
/// * `prev` - The code piece before the name, if any.
pub(super) fn tagged(prev: Option<&str>) -> bool {
    matches!(prev, Some("struct" | "union" | "enum"))
}

/// Returns each piece of one line of C with the kind it reads as from the
/// line alone, as a code block anyone wrote is colored.
///
/// A name reads by its spelling first ([`spelled`]), as the decompile view
/// reads it; else a name after `struct`, `union` or `enum` is a type, one
/// before `(` a function and any other text. No name is looked up in a
/// binary. A block comment the line leaves open runs to its end, and the
/// next line does not know it is inside one.
///
/// # Arguments
///
/// * `line` - One line of C, any text.
///
/// # Returns
///
/// The pieces in order with their kinds, which tile the line.
#[must_use]
pub fn c_kinds(line: &str) -> Vec<(Range<usize>, Kind)> {
    let pieces: Vec<Spanned> = scan(line, 0).collect();
    let code = |k: &usize| {
        pieces
            .get(*k)
            .is_some_and(|(p, _)| matches!(p, Piece::Token(_)))
    };
    pieces
        .iter()
        .enumerate()
        .map(|(k, (piece, span))| {
            let kind = match piece {
                Piece::Space => Kind::Space,
                Piece::Comment => Kind::Comment,
                Piece::Token(Lex::Number) => Kind::Number,
                Piece::Token(Lex::Literal) => Kind::String,
                Piece::Token(Lex::Punct) => Kind::Punct,
                Piece::Token(Lex::Name) => {
                    let w = word(line, &pieces, k);
                    let prev = code_before(&pieces, k).map(|j| word(line, &pieces, j));
                    let next = (k.saturating_add(1)..pieces.len()).find(code);
                    spelled(w, directive(line, &pieces, k), ALONE_WORD).unwrap_or(if tagged(prev) {
                        Kind::Type
                    } else if next.map(|j| word(line, &pieces, j)) == Some("(") {
                        Kind::Function
                    } else {
                        Kind::Text
                    })
                }
            };
            (span.clone(), kind)
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::{Lex, Piece, c_kinds, lex, scan};
    use crate::view::Kind;

    /// A line of C reads as keywords, types, functions, literals and
    /// comments from the line alone, and its pieces spell it back.
    ///
    /// # Panics
    ///
    /// When a piece reads as another kind than pinned, or the pieces do not
    /// spell their line.
    #[test]
    fn a_line_of_c_reads_as_kinds_from_itself() {
        let line = "if (x) return WinMain(\"a\", 0x10); // go";
        let kinds: Vec<(&str, Kind)> = c_kinds(line)
            .into_iter()
            .filter(|(_, k)| *k != Kind::Space)
            .map(|(s, k)| (&line[s], k))
            .collect();
        assert_eq!(
            kinds,
            [
                ("if", Kind::Keyword),
                ("(", Kind::Punct),
                ("x", Kind::Text),
                (")", Kind::Punct),
                ("return", Kind::Keyword),
                ("WinMain", Kind::Function),
                ("(", Kind::Punct),
                ("\"a\"", Kind::String),
                (",", Kind::Punct),
                ("0x10", Kind::Number),
                (")", Kind::Punct),
                (";", Kind::Punct),
                ("// go", Kind::Comment),
            ]
        );
        let typed: Vec<Kind> = c_kinds("struct S *p; uint32_t n;")
            .into_iter()
            .map(|(_, k)| k)
            .filter(|k| matches!(k, Kind::Type | Kind::Keyword))
            .collect();
        assert_eq!(typed, [Kind::Keyword, Kind::Type, Kind::Type]);
        let define = "#define S(x) #x";
        let kinds: Vec<(&str, Kind)> = c_kinds(define)
            .into_iter()
            .filter(|(_, k)| matches!(k, Kind::Keyword | Kind::Text | Kind::Function))
            .map(|(s, k)| (&define[s], k))
            .collect();
        assert_eq!(
            kinds,
            [
                ("define", Kind::Keyword),
                ("S", Kind::Function),
                ("x", Kind::Text),
                ("x", Kind::Text),
            ]
        );
        for text in ["", "\u{0}\u{ffff}\"\\", "/* open", "é'"] {
            let spans = c_kinds(text);
            let spelled: String = spans.iter().map(|(s, _)| &text[s.clone()]).collect();
            assert_eq!(spelled, text);
        }
    }

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
