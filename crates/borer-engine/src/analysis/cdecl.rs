//! C declarations read into user types, laid out by the binary's ABI.
//!
//! Agents write C fluently, and a struct stated as `offset:name:type` rows
//! makes them compute every offset by hand, which is where mistakes come
//! from. This reads a small, documented subset of C and lays each struct
//! out by the ABI's alignment rules, producing the same [`UserType`]s the
//! structured form does. It is a recursive-descent reader over a token
//! list with no recursion of its own, so no input nests it deep.
//!
//! The subset, statement by statement:
//!
//! - `struct Name { fields };` and `typedef struct [Tag] { fields } Name;`.
//!   A field is `type declarator[, declarator];`, a declarator being stars,
//!   a name and `[N]` dimensions, or `(*name)(...)` for a function pointer,
//!   which reads as `u8 *`.
//! - `enum Name { A, B = 5, C };` and `typedef enum [Tag] {...} Name;`:
//!   4 bytes wide unless a value needs 8, or `: T` states the width.
//! - `typedef type declarator[, declarator];`, and `struct Name;`, a
//!   forward declaration, so a pointer may name a struct defined later.
//! - Packing: `#pragma pack(N)`, `#pragma pack(push[, N])`,
//!   `#pragma pack(pop)`, `#pragma pack()`, and `__attribute__((packed))`
//!   on one struct. `#pragma once` is ignored.
//! - Offset assertions: a `// @0x10` or `/* @0x10 */` comment after a
//!   field's `;` on the same line asserts the offset of the last field that
//!   statement declares; `static_assert(offsetof(S, f) == N)` and
//!   `static_assert(sizeof(S) == N)` (or `_Static_assert`, with an optional
//!   message after a comma) assert a field's offset or a struct's size. A
//!   failing assertion refuses the whole text, naming the field and both
//!   numbers.
//!
//! Type words are C's integer keywords, `float`, `double`, `_Bool`, the
//! fixed-width and Windows type names the type library knows
//! ([`typelib::pass_of`]), and the user types already defined or defined
//! earlier in the text; `const` and `volatile` are dropped.
//!
//! Layout ([`Abi`]): a scalar aligns to its size and a pointer to the word,
//! except that 32-bit System V (an x86 ELF or Mach-O) aligns an 8-byte
//! scalar to 4; `long` is 4 bytes on Windows and on any 32-bit target and 8
//! elsewhere, `wchar_t` 2 bytes on Windows and 4 elsewhere. A struct aligns
//! to its widest member, each member's alignment and the struct's capped
//! by the packing in force, and its size rounds up to its alignment. A
//! struct defined before the text aligns as its fields do, capped by the
//! largest power of two dividing its size.
//!
//! Refused, with a message naming what: unions, bit-fields, a struct or
//! enum defined inside a struct, `alignas` and `__declspec`, any
//! preprocessor directive but `#pragma pack` and `#pragma once`, a value
//! that is not an integer literal, `long double`, a flexible array, a
//! variable declared beside a type, a struct used by value before it is
//! defined, and a struct declared forward but never defined.

use std::collections::{BTreeMap, BTreeSet};

use super::typelib::{self, Pass};
use super::utypes::{
    self, ARRAY_LEN_MAX, TypeExpr, UserStruct, UserType, build_alias, build_enum, build_struct,
};
use crate::program::{BinaryFormat, Program};

/// Longest declaration text read, in bytes.
pub const TEXT_MAX: usize = 1 << 16;

/// The packings `#pragma pack` takes.
const PACKS: [u64; 5] = [1, 2, 4, 8, 16];

/// Deepest chain of typedefs and nested structs an alignment follows.
const ALIGN_DEPTH_MAX: usize = 32;

/// The ABI a layout follows: the pointer width and the platform.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Abi {
    /// The pointer width in bytes, 4 or 8.
    pub word: u64,
    /// Windows rules (`long` and `wchar_t` narrow, 8-byte scalars aligned
    /// to 8 on x86), else System V's.
    pub windows: bool,
}

impl Abi {
    /// The ABI a loaded program's structs follow: a PE (and a raw image,
    /// which borer reads as one) by Windows rules, an ELF or Mach-O by
    /// System V's.
    ///
    /// # Arguments
    ///
    /// * `program` - The loaded image.
    #[must_use]
    pub fn of(program: &Program) -> Self {
        Self {
            word: if program.is_64 { 8 } else { 4 },
            windows: match program.format {
                BinaryFormat::Pe | BinaryFormat::Raw | BinaryFormat::Archive => true,
                BinaryFormat::Elf | BinaryFormat::MachO => false,
            },
        }
    }

    /// Names the rules, as a reply says which it laid a struct out by.
    #[must_use]
    pub fn name(self) -> &'static str {
        match (self.word, self.windows) {
            (8, true) => "x64 Windows",
            (8, false) => "x64 System V",
            (_, true) => "x86 Windows",
            (_, false) => "x86 System V",
        }
    }

    /// The alignment of an 8-byte scalar.
    fn wide_align(self) -> u64 {
        if self.word == 4 && !self.windows {
            4
        } else {
            8
        }
    }
}

/// What a text declared: the types in the order it defined them, with
/// each struct's alignment, and what it read loosely.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Declared {
    /// `(name, type, alignment)` per type defined, in text order.
    pub types: Vec<(String, UserType, u64)>,
    /// One line per thing read loosely: a pointer to a struct the text
    /// never defines reads as `u8 *`.
    pub notes: Vec<String>,
}

/// One piece of the text.
#[derive(Debug, Clone, PartialEq, Eq)]
enum Tok {
    /// An identifier or a keyword.
    Word(String),
    /// An integer literal.
    Num(u64),
    /// A string literal, whose text nothing reads.
    Str,
    /// One punctuation character.
    Sym(char),
    /// A preprocessor line, without its `#`.
    Directive(String),
    /// An `@offset` comment.
    At(u64),
}

/// A piece of the text and the line it is on, from 1.
#[derive(Debug, Clone, PartialEq, Eq)]
struct Token {
    /// The piece.
    tok: Tok,
    /// Its line.
    line: usize,
}

/// Splits a declaration text into tokens.
///
/// # Arguments
///
/// * `text` - The declarations.
///
/// # Errors
///
/// When a comment, a string or a number does not end, a number overflows,
/// or a character is not one C declarations use; the message names the
/// line.
fn lex(text: &str) -> anyhow::Result<Vec<Token>> {
    let bytes = text.as_bytes();
    let mut out: Vec<Token> = Vec::new();
    let mut line = 1usize;
    let mut i = 0usize;
    let mut line_start = true;
    while let Some(&b) = bytes.get(i) {
        let rest = text.get(i..).unwrap_or("");
        if b == b'\n' {
            line += 1;
            line_start = true;
            i += 1;
            continue;
        }
        if b.is_ascii_whitespace() {
            i += 1;
            continue;
        }
        if rest.starts_with("//") {
            let end = rest.find('\n').unwrap_or(rest.len());
            push_at(&mut out, rest.get(2..end).unwrap_or(""), line)?;
            i += end;
            continue;
        }
        if rest.starts_with("/*") {
            let end = rest
                .find("*/")
                .ok_or_else(|| anyhow::anyhow!("line {line}: a /* comment does not end"))?;
            let body = rest.get(2..end).unwrap_or("");
            push_at(&mut out, body, line)?;
            line += body.matches('\n').count();
            i += end + 2;
            continue;
        }
        let first = line_start;
        line_start = false;
        if b == b'#' {
            if !first {
                return Err(anyhow::anyhow!("line {line}: a # starts a line of its own"));
            }
            let end = rest.find('\n').unwrap_or(rest.len());
            let directive = rest.get(1..end).unwrap_or("").trim().to_owned();
            out.push(Token {
                tok: Tok::Directive(directive),
                line,
            });
            i += end;
            continue;
        }
        if b.is_ascii_alphabetic() || b == b'_' {
            let len = rest
                .find(|c: char| !(c.is_ascii_alphanumeric() || c == '_'))
                .unwrap_or(rest.len());
            out.push(Token {
                tok: Tok::Word(rest.get(..len).unwrap_or("").to_owned()),
                line,
            });
            i += len;
            continue;
        }
        if b.is_ascii_digit() {
            let len = rest
                .find(|c: char| !c.is_ascii_alphanumeric())
                .unwrap_or(rest.len());
            let n = number(rest.get(..len).unwrap_or("")).ok_or_else(|| {
                anyhow::anyhow!(
                    "line {line}: {} is not a number",
                    crate::text::quoted(rest.get(..len).unwrap_or(""))
                )
            })?;
            out.push(Token {
                tok: Tok::Num(n),
                line,
            });
            i += len;
            continue;
        }
        if b == b'"' {
            let mut j = i + 1;
            loop {
                match bytes.get(j) {
                    Some(b'\\') => j += 2,
                    Some(b'"') => break,
                    Some(b'\n') | None => {
                        return Err(anyhow::anyhow!("line {line}: a string does not end"));
                    }
                    Some(_) => j += 1,
                }
            }
            out.push(Token {
                tok: Tok::Str,
                line,
            });
            i = j + 1;
            continue;
        }
        if b"{}()[];,*=:-".contains(&b) {
            out.push(Token {
                tok: Tok::Sym(char::from(b)),
                line,
            });
            i += 1;
            continue;
        }
        let shown = rest.chars().next().map(String::from).unwrap_or_default();
        return Err(anyhow::anyhow!(
            "line {line}: {} is not part of the C declarations this reads",
            crate::text::quoted(&shown)
        ));
    }
    Ok(out)
}

/// Records a comment that asserts an offset (`@0x10`); any other comment
/// is dropped.
///
/// # Arguments
///
/// * `out` - The tokens so far.
/// * `body` - The comment's text, without its markers.
/// * `line` - The line it starts on.
///
/// # Errors
///
/// When the text after `@` is no number.
fn push_at(out: &mut Vec<Token>, body: &str, line: usize) -> anyhow::Result<()> {
    let Some(at) = body.trim().strip_prefix('@') else {
        return Ok(());
    };
    let word = at.split_whitespace().next().unwrap_or("");
    let n = number(word).ok_or_else(|| {
        anyhow::anyhow!(
            "line {line}: the offset comment @{} is not a number",
            crate::text::one_line(word)
        )
    })?;
    out.push(Token {
        tok: Tok::At(n),
        line,
    });
    Ok(())
}

/// Reads an integer literal: decimal, `0x` hex or `0` octal, with any
/// `u`/`l` suffix.
///
/// # Arguments
///
/// * `text` - The literal.
///
/// # Returns
///
/// The value, or `None` when the text is no literal or overflows.
fn number(text: &str) -> Option<u64> {
    let digits = text.trim_end_matches(['u', 'U', 'l', 'L']);
    if let Some(hex) = digits
        .strip_prefix("0x")
        .or_else(|| digits.strip_prefix("0X"))
    {
        return u64::from_str_radix(hex, 16).ok();
    }
    if digits.len() > 1
        && let Some(oct) = digits.strip_prefix('0')
    {
        return u64::from_str_radix(oct, 8).ok();
    }
    digits.parse::<u64>().ok()
}

/// The base of a type before its declarator: a tag, C keywords, or one
/// name.
#[derive(Debug, Clone, PartialEq, Eq)]
enum Base {
    /// `struct X` or `enum X`.
    Tag(String),
    /// C type keywords, joined by single spaces (`unsigned int`).
    Words(String),
    /// A typedef, user type or library type name.
    Name(String),
}

/// One declarator: what a declaration adds to its base, and its name.
#[derive(Debug, Clone, PartialEq, Eq)]
struct Declarator {
    /// The declared name.
    name: String,
    /// Pointers over the base.
    stars: usize,
    /// Array dimensions, outermost first.
    dims: Vec<u64>,
    /// A function pointer, `(*name)(...)`, which reads as `u8 *`.
    function: bool,
    /// The line it is on.
    line: usize,
}

/// One field of a struct being read.
struct Field {
    /// Its declarator.
    decl: Declarator,
    /// Its type.
    ty: TypeExpr,
    /// The offset an `@` comment asserts for it.
    asserted: Option<u64>,
}

/// C keywords that make up a type's base.
const KEYWORDS: [&str; 11] = [
    "char", "short", "int", "long", "signed", "unsigned", "float", "double", "void", "_Bool",
    "__int64",
];

/// The reader's state over one text.
struct Reader<'t> {
    /// The tokens.
    toks: &'t [Token],
    /// The next token's index.
    pos: usize,
    /// The ABI structs are laid out by.
    abi: Abi,
    /// Every type known: the overlay's, then the text's as they are
    /// defined, with a placeholder for each struct the text defines further
    /// down, so a pointer may name it.
    known: BTreeMap<String, UserType>,
    /// The alignment of each type the text defined.
    aligns: BTreeMap<String, u64>,
    /// Struct names the text defines further down and has not yet.
    later: BTreeSet<String>,
    /// The packing in force, `None` for the ABI's natural alignment.
    pack: Option<u64>,
    /// Packings `#pragma pack(push)` saved.
    saved: Vec<Option<u64>>,
    /// What the text defined, in order.
    out: Declared,
}

impl<'t> Reader<'t> {
    /// The next token, unconsumed.
    fn peek(&self) -> Option<&'t Token> {
        self.toks.get(self.pos)
    }

    /// The line of the next token, or of the last one at the end.
    fn line(&self) -> usize {
        self.peek()
            .or_else(|| self.toks.last())
            .map_or(1, |t| t.line)
    }

    /// Consumes the next token.
    fn next(&mut self) -> Option<&'t Token> {
        let t = self.toks.get(self.pos);
        self.pos += 1;
        t
    }

    /// Tells whether the next token is the symbol `c`, consuming it if so.
    ///
    /// # Arguments
    ///
    /// * `c` - The symbol.
    fn eat(&mut self, c: char) -> bool {
        let hit = matches!(self.peek(), Some(Token { tok: Tok::Sym(s), .. }) if *s == c);
        if hit {
            self.pos += 1;
        }
        hit
    }

    /// Tells whether the next token is the word `w`, consuming it if so.
    ///
    /// # Arguments
    ///
    /// * `w` - The word.
    fn eat_word(&mut self, w: &str) -> bool {
        let hit = matches!(self.peek(), Some(Token { tok: Tok::Word(s), .. }) if s == w);
        if hit {
            self.pos += 1;
        }
        hit
    }

    /// Consumes the symbol `c`, refusing anything else.
    ///
    /// # Arguments
    ///
    /// * `c` - The symbol.
    /// * `what` - What it closes or separates, for the message.
    ///
    /// # Errors
    ///
    /// When the next token is not `c`.
    fn expect(&mut self, c: char, what: &str) -> anyhow::Result<()> {
        if self.eat(c) {
            return Ok(());
        }
        Err(self.unexpected(&format!("`{c}` {what}")))
    }

    /// The error for a token that is not what the grammar wants there.
    ///
    /// # Arguments
    ///
    /// * `wanted` - What was wanted.
    fn unexpected(&self, wanted: &str) -> anyhow::Error {
        let found = match self.peek().map(|t| &t.tok) {
            Some(Tok::Word(w)) => crate::text::quoted(w),
            Some(Tok::Num(n)) => format!("{n:#x}"),
            Some(Tok::Str) => "a string".to_owned(),
            Some(Tok::Sym(c)) => format!("`{c}`"),
            Some(Tok::Directive(d)) => format!("#{}", crate::text::one_line(d)),
            Some(Tok::At(n)) => format!("the offset comment @{n:#x}"),
            None => "the end".to_owned(),
        };
        anyhow::anyhow!("line {}: wanted {wanted}, found {found}", self.line())
    }

    /// Consumes an identifier.
    ///
    /// # Arguments
    ///
    /// * `what` - What it names, for the message.
    ///
    /// # Errors
    ///
    /// When the next token is no identifier.
    fn ident(&mut self, what: &str) -> anyhow::Result<String> {
        if let Some(Token {
            tok: Tok::Word(w), ..
        }) = self.peek()
        {
            let w = w.clone();
            self.pos += 1;
            return Ok(w);
        }
        Err(self.unexpected(what))
    }

    /// Consumes an integer, a leading `-` allowed.
    ///
    /// # Errors
    ///
    /// When the next tokens are no integer literal.
    fn integer(&mut self) -> anyhow::Result<i128> {
        let negative = self.eat('-');
        match self.peek().map(|t| &t.tok) {
            Some(Tok::Num(n)) => {
                let n = i128::from(*n);
                self.pos += 1;
                Ok(if negative { -n } else { n })
            }
            Some(_) | None => Err(self.unexpected("an integer literal")),
        }
    }

    /// Reads every statement of the text.
    ///
    /// # Errors
    ///
    /// The first statement refused.
    fn statements(&mut self) -> anyhow::Result<()> {
        while let Some(t) = self.peek() {
            let line = t.line;
            match &t.tok {
                Tok::Directive(d) => {
                    let d = d.clone();
                    self.pos += 1;
                    self.pragma(&d, line)?;
                }
                Tok::Sym(';') => self.pos += 1,
                Tok::Word(w) => match w.as_str() {
                    "typedef" => {
                        self.pos += 1;
                        self.typedef()?;
                    }
                    "struct" => {
                        self.pos += 1;
                        self.struct_statement()?;
                    }
                    "enum" => {
                        self.pos += 1;
                        let (name, ty) = self.enum_body(None)?;
                        let name = name.ok_or_else(|| {
                            anyhow::anyhow!("line {line}: an enum outside a typedef needs a name")
                        })?;
                        self.define(&name, ty, line)?;
                        self.expect(';', "after the enum")?;
                    }
                    "static_assert" | "_Static_assert" => {
                        self.pos += 1;
                        self.static_assert(line)?;
                    }
                    "union" => {
                        return Err(anyhow::anyhow!(
                            "line {line}: unions are not read; a user struct's fields do not overlap, so state the largest member"
                        ));
                    }
                    _ => {
                        return Err(self
                            .unexpected("a struct, enum, typedef, static_assert or #pragma pack"));
                    }
                },
                Tok::At(n) => {
                    return Err(anyhow::anyhow!(
                        "line {line}: the offset comment @{n:#x} follows no field on its line"
                    ));
                }
                Tok::Num(_) | Tok::Str | Tok::Sym(_) => {
                    return Err(
                        self.unexpected("a struct, enum, typedef, static_assert or #pragma pack")
                    );
                }
            }
        }
        Ok(())
    }

    /// Reads a preprocessor line: `#pragma pack` changes the packing,
    /// `#pragma once` is ignored, anything else is refused.
    ///
    /// # Arguments
    ///
    /// * `d` - The line without its `#`.
    /// * `line` - Its line number.
    ///
    /// # Errors
    ///
    /// When it is another directive, or the packing is not one of
    /// [`PACKS`].
    fn pragma(&mut self, d: &str, line: usize) -> anyhow::Result<()> {
        let refused = || {
            anyhow::anyhow!(
                "line {line}: #{} is not read; only #pragma pack is (no preprocessor)",
                crate::text::one_line(d)
            )
        };
        let Some(rest) = d.strip_prefix("pragma") else {
            return Err(refused());
        };
        let rest = rest.trim();
        if rest == "once" {
            return Ok(());
        }
        let args = rest
            .strip_prefix("pack")
            .map(str::trim)
            .and_then(|r| r.strip_prefix('('))
            .and_then(|r| r.strip_suffix(')'))
            .ok_or_else(refused)?;
        let parts: Vec<&str> = args.split(',').map(str::trim).collect();
        let value = |text: &str| {
            number(text).filter(|n| PACKS.contains(n)).ok_or_else(|| {
                anyhow::anyhow!(
                    "line {line}: #pragma pack takes 1, 2, 4, 8 or 16, not {}",
                    crate::text::quoted(text)
                )
            })
        };
        match parts.as_slice() {
            [""] => self.pack = None,
            ["push"] => self.saved.push(self.pack),
            ["push", n] => {
                let n = value(n)?;
                self.saved.push(self.pack);
                self.pack = Some(n);
            }
            ["pop"] => self.pack = self.saved.pop().flatten(),
            [n] => self.pack = Some(value(n)?),
            _ => return Err(refused()),
        }
        Ok(())
    }

    /// Reads `__attribute__((packed))`, the one attribute read.
    ///
    /// # Returns
    ///
    /// Whether one was there.
    ///
    /// # Errors
    ///
    /// When it states another attribute, or `alignas`/`__declspec` is
    /// there.
    fn attribute(&mut self) -> anyhow::Result<bool> {
        let line = self.line();
        if matches!(self.peek().map(|t| &t.tok), Some(Tok::Word(w)) if matches!(w.as_str(), "alignas" | "_Alignas" | "__declspec"))
        {
            return Err(anyhow::anyhow!(
                "line {line}: alignas and __declspec are not read; state the packing with #pragma pack"
            ));
        }
        if !self.eat_word("__attribute__") {
            return Ok(false);
        }
        self.expect('(', "after __attribute__")?;
        self.expect('(', "after __attribute__(")?;
        let what = self.ident("an attribute")?;
        if what != "packed" && what != "__packed__" {
            return Err(anyhow::anyhow!(
                "line {line}: __attribute__(({}) is not read; only packed is",
                crate::text::one_line(&what)
            ));
        }
        self.expect(')', "closing the attribute")?;
        self.expect(')', "closing __attribute__")?;
        Ok(true)
    }

    /// Reads a statement that starts with `struct`: a definition, or a
    /// forward declaration.
    ///
    /// # Errors
    ///
    /// When the struct is refused, or a variable is declared after it.
    fn struct_statement(&mut self) -> anyhow::Result<()> {
        let line = self.line();
        let packed = self.attribute()?;
        let tag = self.ident("the struct's name")?;
        if self.eat(';') {
            return Ok(());
        }
        let ty = self.struct_body(&tag, packed)?;
        self.define(&tag, ty, line)?;
        if !self.eat(';') {
            return Err(anyhow::anyhow!(
                "line {}: struct {tag} declares a variable; only types are read, so end it with `;`",
                self.line()
            ));
        }
        Ok(())
    }

    /// Reads a struct's `{ fields }` and lays it out.
    ///
    /// # Arguments
    ///
    /// * `name` - The struct's name.
    /// * `packed` - `__attribute__((packed))` came before the body.
    ///
    /// # Returns
    ///
    /// The struct, its alignment recorded.
    ///
    /// # Errors
    ///
    /// When a field is refused, an offset assertion fails, or the struct
    /// does not build.
    fn struct_body(&mut self, name: &str, packed: bool) -> anyhow::Result<UserType> {
        let line = self.line();
        self.expect('{', "opening the struct")?;
        let mut fields: Vec<Field> = Vec::new();
        while !self.eat('}') {
            if self.peek().is_none() {
                return Err(anyhow::anyhow!("line {line}: struct {name} does not end"));
            }
            if let Some(Token {
                tok: Tok::At(n), ..
            }) = self.peek()
            {
                return Err(anyhow::anyhow!(
                    "line {}: the offset comment @{n:#x} follows no field on its line",
                    self.line()
                ));
            }
            let nested = matches!(self.peek().map(|t| &t.tok), Some(Tok::Word(w)) if matches!(w.as_str(), "struct" | "enum" | "union"))
                && matches!(
                    self.toks.get(self.pos + 2).map(|t| &t.tok),
                    Some(Tok::Sym('{'))
                )
                || matches!(
                    self.toks.get(self.pos + 1).map(|t| &t.tok),
                    Some(Tok::Sym('{'))
                );
            if nested {
                return Err(anyhow::anyhow!(
                    "line {}: a struct, enum or union defined inside struct {name} is not read; define it first and name it here",
                    self.line()
                ));
            }
            let base = self.base()?;
            let mut decls = vec![self.declarator()?];
            while self.eat(',') {
                decls.push(self.declarator()?);
            }
            let end_line = self.line();
            self.expect(';', "ending the field")?;
            let asserted = match self.peek() {
                Some(Token {
                    tok: Tok::At(n),
                    line,
                }) if *line == end_line => {
                    let n = *n;
                    self.pos += 1;
                    Some(n)
                }
                Some(_) | None => None,
            };
            let count = decls.len();
            for (i, decl) in decls.into_iter().enumerate() {
                let ty = self.declared(&base, &decl, false)?;
                fields.push(Field {
                    decl,
                    ty,
                    asserted: asserted.filter(|_| i + 1 == count),
                });
            }
        }
        if self.attribute()? {
            return self.lay_out(name, &fields, Some(1), line);
        }
        let pack = if packed { Some(1) } else { self.pack };
        self.lay_out(name, &fields, pack, line)
    }

    /// Lays a struct's fields out and builds it.
    ///
    /// # Arguments
    ///
    /// * `name` - The struct's name.
    /// * `fields` - Its fields in order.
    /// * `pack` - The packing in force, `None` for natural alignment.
    /// * `line` - Where the struct starts.
    ///
    /// # Errors
    ///
    /// When it has no fields, an offset assertion fails, a field has no
    /// size, or the struct does not build.
    fn lay_out(
        &mut self,
        name: &str,
        fields: &[Field],
        pack: Option<u64>,
        line: usize,
    ) -> anyhow::Result<UserType> {
        if fields.is_empty() {
            return Err(anyhow::anyhow!(
                "line {line}: struct {name} states no fields"
            ));
        }
        let mut offset = 0u64;
        let mut align = 1u64;
        let mut stated: Vec<(u64, String, TypeExpr)> = Vec::with_capacity(fields.len());
        for f in fields {
            let size = utypes::width_of(&self.known, &f.ty, self.abi.word).ok_or_else(|| {
                anyhow::anyhow!(
                    "line {}: field {} of struct {name} has type {}, which has no size",
                    f.decl.line,
                    f.decl.name,
                    f.ty.spell()
                )
            })?;
            let natural = self.align_of(&f.ty, 0);
            let a = pack.map_or(natural, |p| natural.min(p));
            offset = round_up(offset, a)
                .ok_or_else(|| anyhow::anyhow!("line {line}: struct {name} is too large"))?;
            if let Some(want) = f.asserted
                && want != offset
            {
                return Err(anyhow::anyhow!(
                    "line {}: field {} of struct {name} is at {offset:#x} under {} layout, not {want:#x} as its comment asserts",
                    f.decl.line,
                    f.decl.name,
                    self.abi.name()
                ));
            }
            stated.push((offset, f.decl.name.clone(), f.ty.clone()));
            offset = offset
                .checked_add(size)
                .ok_or_else(|| anyhow::anyhow!("line {line}: struct {name} is too large"))?;
            align = align.max(a);
        }
        let size = round_up(offset, align)
            .ok_or_else(|| anyhow::anyhow!("line {line}: struct {name} is too large"))?;
        let built = build_struct(name, Some(size), &stated, &self.known, self.abi.word)
            .map_err(|e| anyhow::anyhow!("line {line}: {e}"))?;
        self.aligns.insert(name.to_owned(), align);
        Ok(built)
    }

    /// Reads a type's base: `struct X`, C keywords, or one name, with
    /// `const` and `volatile` dropped.
    ///
    /// # Errors
    ///
    /// When it is a union, or no type is there.
    fn base(&mut self) -> anyhow::Result<Base> {
        while self.eat_word("const") || self.eat_word("volatile") {}
        let line = self.line();
        if self.eat_word("union") {
            return Err(anyhow::anyhow!(
                "line {line}: unions are not read; state the largest member"
            ));
        }
        if self.eat_word("struct") || self.eat_word("enum") {
            return Ok(Base::Tag(self.ident("a struct or enum name")?));
        }
        let mut words: Vec<String> = Vec::new();
        while let Some(Token {
            tok: Tok::Word(w), ..
        }) = self.peek()
        {
            if KEYWORDS.contains(&w.as_str()) {
                words.push(w.clone());
                self.pos += 1;
            } else if w == "const" || w == "volatile" {
                self.pos += 1;
            } else {
                break;
            }
        }
        if !words.is_empty() {
            return Ok(Base::Words(words.join(" ")));
        }
        Ok(Base::Name(self.ident("a type")?))
    }

    /// Reads one declarator: stars, a name and dimensions, or a function
    /// pointer.
    ///
    /// # Errors
    ///
    /// When a bit-field, a flexible array or something no declarator reads
    /// is there.
    fn declarator(&mut self) -> anyhow::Result<Declarator> {
        let line = self.line();
        let mut stars = 0usize;
        loop {
            if self.eat('*') {
                stars += 1;
            } else if !(self.eat_word("const") || self.eat_word("volatile")) {
                break;
            }
        }
        let (name, function) = if self.eat('(') {
            self.expect('*', "in a function pointer `(*name)(...)`")?;
            let name = self.ident("the function pointer's name")?;
            self.expect(')', "after the function pointer's name")?;
            self.expect('(', "opening the function pointer's parameters")?;
            let mut depth = 1usize;
            while depth > 0 {
                match self.next().map(|t| &t.tok) {
                    Some(Tok::Sym('(')) => depth += 1,
                    Some(Tok::Sym(')')) => depth -= 1,
                    Some(_) => {}
                    None => {
                        return Err(anyhow::anyhow!(
                            "line {line}: the function pointer {name}'s parameters do not end"
                        ));
                    }
                }
            }
            (name, true)
        } else {
            (self.ident("a name")?, false)
        };
        let mut dims: Vec<u64> = Vec::new();
        while self.eat('[') {
            if self.eat(']') {
                return Err(anyhow::anyhow!(
                    "line {line}: {name}[] is a flexible array, which has no size; state its length"
                ));
            }
            let n = self.integer()?;
            let n = u64::try_from(n)
                .ok()
                .filter(|n| (1..=ARRAY_LEN_MAX).contains(n))
                .ok_or_else(|| {
                    anyhow::anyhow!(
                        "line {line}: {name}'s length {n} is not a count from 1 to {ARRAY_LEN_MAX:#x}"
                    )
                })?;
            dims.push(n);
            self.expect(']', "closing the array")?;
        }
        if self.eat(':') {
            return Err(anyhow::anyhow!(
                "line {line}: {name} is a bit-field, which is not read; state the word that holds it"
            ));
        }
        if stars.saturating_add(dims.len()) > utypes::PTR_DEPTH_MAX {
            return Err(anyhow::anyhow!(
                "line {line}: {name} stacks more than {} pointers and arrays",
                utypes::PTR_DEPTH_MAX
            ));
        }
        Ok(Declarator {
            name,
            stars,
            dims,
            function,
            line,
        })
    }

    /// The type a declarator gives its base.
    ///
    /// # Arguments
    ///
    /// * `base` - The base.
    /// * `decl` - The declarator.
    /// * `alias` - It declares a typedef, which may name a struct the text
    ///   defines later, since a typedef resolves by name.
    ///
    /// # Errors
    ///
    /// When the base names no type, or is `void` with no pointer over it.
    fn declared(
        &mut self,
        base: &Base,
        decl: &Declarator,
        alias: bool,
    ) -> anyhow::Result<TypeExpr> {
        let ty = if decl.function {
            TypeExpr::Ptr(Box::new(TypeExpr::U8))
        } else {
            let inner = self.resolve(base, decl.stars > 0 || alias, decl.line)?;
            match inner {
                Some(t) => (0..decl.stars).fold(t, |t, _| TypeExpr::Ptr(Box::new(t))),
                None if decl.stars > 0 => (1..decl.stars)
                    .fold(TypeExpr::Ptr(Box::new(TypeExpr::U8)), |t, _| {
                        TypeExpr::Ptr(Box::new(t))
                    }),
                None => {
                    return Err(anyhow::anyhow!(
                        "line {}: {} is void, which has no size",
                        decl.line,
                        decl.name
                    ));
                }
            }
        };
        Ok(decl
            .dims
            .iter()
            .rev()
            .fold(ty, |t, n| TypeExpr::Array(Box::new(t), *n)))
    }

    /// The type a base names.
    ///
    /// # Arguments
    ///
    /// * `base` - The base.
    /// * `pointed` - A pointer (or a typedef's name) is over it, so `void`,
    ///   a struct the text defines later and one it never defines are
    ///   allowed.
    /// * `line` - Where it is, for the message.
    ///
    /// # Returns
    ///
    /// The type, or `None` for `void`.
    ///
    /// # Errors
    ///
    /// When the base names no type, is `long double`, or names a struct by
    /// value before the text defines it.
    fn resolve(
        &mut self,
        base: &Base,
        pointed: bool,
        line: usize,
    ) -> anyhow::Result<Option<TypeExpr>> {
        let named = |name: &str, this: &Self| -> anyhow::Result<Option<TypeExpr>> {
            if this.later.contains(name) && !pointed {
                return Err(anyhow::anyhow!(
                    "line {line}: {name} is used by value before it is defined"
                ));
            }
            if this.known.contains_key(name) {
                return Ok(Some(TypeExpr::Named(name.to_owned())));
            }
            Err(anyhow::anyhow!("line {line}: {name} is not defined"))
        };
        match base {
            Base::Tag(tag) => {
                if !self.known.contains_key(tag) && pointed {
                    self.out.notes.push(format!(
                        "line {line}: struct {tag} is defined nowhere, so a pointer to it reads as u8 *"
                    ));
                    return Ok(Some(TypeExpr::U8));
                }
                named(tag, self)
            }
            Base::Name(name) if self.known.contains_key(name) || self.later.contains(name) => {
                named(name, self)
            }
            Base::Name(name) | Base::Words(name) => self.word_type(name, line),
        }
    }

    /// The type C keywords, a library type name or a scalar word of the
    /// language (`u8`, which a dropped `typedef unsigned char u8;` leaves
    /// standing) stand for.
    ///
    /// # Arguments
    ///
    /// * `words` - The words, joined by single spaces.
    /// * `line` - Where they are, for the message.
    ///
    /// # Returns
    ///
    /// The type, or `None` for `void`.
    ///
    /// # Errors
    ///
    /// When neither C nor the type library spells the words, or they are
    /// `long double`.
    fn word_type(&self, words: &str, line: usize) -> anyhow::Result<Option<TypeExpr>> {
        if let Ok(own) = utypes::parse_type(words)
            && !matches!(own, TypeExpr::Named(_))
        {
            return Ok(Some(own));
        }
        let char_ptr = || Some(TypeExpr::Ptr(Box::new(TypeExpr::Char)));
        let wide_ptr = || Some(TypeExpr::Ptr(Box::new(TypeExpr::U16)));
        match words {
            "char" | "CHAR" => return Ok(Some(TypeExpr::Char)),
            "wchar_t" => {
                return Ok(Some(if self.abi.windows {
                    TypeExpr::U16
                } else {
                    TypeExpr::I32
                }));
            }
            "LPSTR" | "LPCSTR" | "PSTR" | "PCSTR" | "PCHAR" => return Ok(char_ptr()),
            "LPWSTR" | "LPCWSTR" | "PWSTR" | "PCWSTR" | "PWCHAR" => return Ok(wide_ptr()),
            "long double" => {
                return Err(anyhow::anyhow!(
                    "line {line}: long double is not read; its width differs by compiler"
                ));
            }
            _ => {}
        }
        let bits = u8::try_from(self.abi.word * 8).unwrap_or(64);
        let format = if self.abi.windows {
            BinaryFormat::Pe
        } else {
            BinaryFormat::Elf
        };
        let pass = typelib::pass_of(words, bits, format).or_else(|| {
            let trimmed = words.strip_suffix(" int")?;
            typelib::pass_of(trimmed, bits, format)
        });
        let unknown = || {
            anyhow::anyhow!(
                "line {line}: {} is no type C, the type library or an earlier definition spells",
                crate::text::quoted(words)
            )
        };
        Ok(match pass.ok_or_else(unknown)? {
            Pass::Void => None,
            Pass::Pointer => Some(TypeExpr::Ptr(Box::new(TypeExpr::U8))),
            Pass::Float(32) => Some(TypeExpr::F32),
            Pass::Float(_) => Some(TypeExpr::F64),
            Pass::Int { bits, signed } => Some(match (bits, signed) {
                (8, true) => TypeExpr::I8,
                (8, false) => TypeExpr::U8,
                (16, true) => TypeExpr::I16,
                (16, false) => TypeExpr::U16,
                (32, true) => TypeExpr::I32,
                (32, false) => TypeExpr::U32,
                (_, true) => TypeExpr::I64,
                (_, false) => TypeExpr::U64,
            }),
        })
    }

    /// The alignment a type takes under the ABI, before any packing.
    ///
    /// # Arguments
    ///
    /// * `ty` - The type.
    /// * `depth` - Typedefs and nested structs followed so far.
    fn align_of(&self, ty: &TypeExpr, depth: usize) -> u64 {
        if depth > ALIGN_DEPTH_MAX {
            return 1;
        }
        match ty {
            TypeExpr::U8 | TypeExpr::I8 | TypeExpr::Char => 1,
            TypeExpr::U16 | TypeExpr::I16 => 2,
            TypeExpr::U32 | TypeExpr::I32 | TypeExpr::F32 => 4,
            TypeExpr::U64 | TypeExpr::I64 | TypeExpr::F64 => self.abi.wide_align(),
            TypeExpr::Ptr(_) => self.abi.word,
            TypeExpr::Array(inner, _) => self.align_of(inner, depth + 1),
            TypeExpr::Named(n) => {
                if let Some(a) = self.aligns.get(n) {
                    return *a;
                }
                match self.known.get(n) {
                    Some(UserType::Struct(s)) => {
                        let natural = s
                            .fields
                            .values()
                            .map(|f| self.align_of(&f.ty, depth + 1))
                            .max()
                            .unwrap_or(1);
                        natural.min(largest_power_dividing(s.size))
                    }
                    Some(UserType::Enum(e)) => {
                        if e.size == 8 {
                            self.abi.wide_align()
                        } else {
                            e.size
                        }
                    }
                    Some(UserType::Alias(inner)) => self.align_of(inner, depth + 1),
                    None => 1,
                }
            }
        }
    }

    /// Reads an enum's `[Tag] [: T] { A, B = 5 }`, `enum` already read.
    ///
    /// # Arguments
    ///
    /// * `fallback` - The name to give an untagged enum.
    ///
    /// # Returns
    ///
    /// The tag (or the fallback) and the enum.
    ///
    /// # Errors
    ///
    /// When a value is no integer literal, the stated width is not 4 or 8,
    /// or the enum does not build.
    fn enum_body(&mut self, fallback: Option<&str>) -> anyhow::Result<(Option<String>, UserType)> {
        let line = self.line();
        let tag = match self.peek().map(|t| &t.tok) {
            Some(Tok::Word(_)) => Some(self.ident("the enum's name")?),
            Some(_) | None => None,
        };
        let mut width: Option<u64> = None;
        if self.eat(':') {
            let base = self.base()?;
            let ty = self.resolve(&base, false, line)?;
            let w = ty.and_then(|t| utypes::width_of(&self.known, &t, self.abi.word));
            width = Some(w.filter(|w| matches!(w, 4 | 8)).ok_or_else(|| {
                anyhow::anyhow!(
                    "line {line}: an enum is read 4 or 8 bytes wide, not as its stated type"
                )
            })?);
        }
        self.expect('{', "opening the enum")?;
        let mut values: Vec<(i128, String)> = Vec::new();
        let mut next: i128 = 0;
        while !self.eat('}') {
            let name = self.ident("an enumerator")?;
            if self.eat('=') {
                next = self.integer().map_err(|_| {
                    anyhow::anyhow!(
                        "line {}: enumerator {name}'s value is not an integer literal; only literals are read",
                        self.line()
                    )
                })?;
            }
            values.push((next, name));
            next += 1;
            if !self.eat(',') {
                self.expect('}', "closing the enum")?;
                break;
            }
        }
        let name = tag
            .clone()
            .or_else(|| fallback.map(str::to_owned))
            .ok_or_else(|| anyhow::anyhow!("line {line}: an untagged enum needs a typedef name"))?;
        let fits32 = values
            .iter()
            .all(|(v, _)| (i128::from(i32::MIN)..=i128::from(u32::MAX)).contains(v));
        let size = width.unwrap_or(if fits32 { 4 } else { 8 });
        let mut stated: Vec<(u64, String)> = Vec::with_capacity(values.len());
        for (v, n) in values {
            let bits = if v < 0 {
                u64::try_from(v + (1i128 << 64)).ok()
            } else {
                u64::try_from(v).ok()
            };
            let bits = bits
                .map(|b| {
                    if size == 4 {
                        b & u64::from(u32::MAX)
                    } else {
                        b
                    }
                })
                .ok_or_else(|| {
                    anyhow::anyhow!("line {line}: enumerator {n} = {v} fits no 8 bytes")
                })?;
            stated.push((bits, n));
        }
        let built =
            build_enum(&name, size, &stated).map_err(|e| anyhow::anyhow!("line {line}: {e}"))?;
        self.aligns.insert(
            name.clone(),
            if size == 8 {
                self.abi.wide_align()
            } else {
                size
            },
        );
        Ok((tag.or(Some(name)), built))
    }

    /// Reads a `typedef`, `typedef` already read.
    ///
    /// # Errors
    ///
    /// When the type or a declarator is refused.
    fn typedef(&mut self) -> anyhow::Result<()> {
        let line = self.line();
        let at_struct = matches!(self.peek().map(|t| &t.tok), Some(Tok::Word(w)) if w == "struct");
        let at_enum = matches!(self.peek().map(|t| &t.tok), Some(Tok::Word(w)) if w == "enum");
        let base = if at_struct && self.body_follows(self.pos + 1) {
            self.pos += 1;
            let packed = self.attribute()?;
            let tag = match self.peek().map(|t| &t.tok) {
                Some(Tok::Word(w)) if w != "__attribute__" => {
                    Some(self.ident("the struct's name")?)
                }
                Some(_) | None => None,
            };
            let name = match &tag {
                Some(t) => t.clone(),
                None => self.plain_name_ahead().ok_or_else(|| {
                    anyhow::anyhow!("line {line}: an untagged struct needs a plain typedef name")
                })?,
            };
            let ty = self.struct_body(&name, packed)?;
            self.define(&name, ty, line)?;
            Base::Tag(name)
        } else if at_enum && self.body_follows(self.pos + 1) {
            self.pos += 1;
            let fallback = self.plain_name_ahead();
            let (name, ty) = self.enum_body(fallback.as_deref())?;
            let name = name.ok_or_else(|| anyhow::anyhow!("line {line}: the enum needs a name"))?;
            self.define(&name, ty, line)?;
            Base::Tag(name)
        } else {
            self.base()?
        };
        loop {
            let decl = self.declarator()?;
            let ty = self.declared(&base, &decl, true)?;
            self.alias(&decl.name, &ty, decl.line)?;
            if !self.eat(',') {
                break;
            }
        }
        self.expect(';', "ending the typedef")
    }

    /// Tells whether a struct or enum body opens after `struct` or `enum`:
    /// past an optional `__attribute__((...))`, an optional tag and, for an
    /// enum, before its `: T`.
    ///
    /// # Arguments
    ///
    /// * `from` - The token after the keyword.
    fn body_follows(&self, from: usize) -> bool {
        let tok = |i: usize| self.toks.get(i).map(|t| &t.tok);
        let skip_attribute = |i: usize| match tok(i) {
            Some(Tok::Word(w)) if w == "__attribute__" => i + 6,
            Some(_) | None => i,
        };
        let mut i = skip_attribute(from);
        if matches!(tok(i), Some(Tok::Word(_))) {
            i = skip_attribute(i + 1);
        }
        matches!(tok(i), Some(Tok::Sym('{' | ':')))
    }

    /// Finds the first plain name a typedef declares after a `{...}` body
    /// ahead, for an untagged struct or enum to take.
    ///
    /// # Returns
    ///
    /// The name, or `None` when the body does not close or no plain name
    /// follows it.
    fn plain_name_ahead(&self) -> Option<String> {
        let mut depth = 0usize;
        let mut i = self.pos;
        loop {
            match &self.toks.get(i)?.tok {
                Tok::Sym('{') => depth += 1,
                Tok::Sym('}') => {
                    depth = depth.checked_sub(1)?;
                    if depth == 0 {
                        break;
                    }
                }
                Tok::Word(_)
                | Tok::Num(_)
                | Tok::Str
                | Tok::Sym(_)
                | Tok::Directive(_)
                | Tok::At(_) => {}
            }
            i += 1;
        }
        let mut stars = false;
        for t in self.toks.get(i + 1..)? {
            match &t.tok {
                Tok::Sym('*') => stars = true,
                Tok::Sym(',') => stars = false,
                Tok::Word(w) if w == "__attribute__" || w == "packed" => {}
                Tok::Word(w) if !stars => return Some(w.clone()),
                Tok::Sym(';') => return None,
                Tok::Word(_)
                | Tok::Num(_)
                | Tok::Str
                | Tok::Sym(_)
                | Tok::Directive(_)
                | Tok::At(_) => {}
            }
        }
        None
    }

    /// Defines a name for a type, as a typedef declares one.
    ///
    /// A typedef naming a type by its own name (`typedef struct S S;`) and
    /// one naming a scalar of the language by its own word
    /// (`typedef unsigned char u8;`) add nothing and are dropped.
    ///
    /// # Arguments
    ///
    /// * `name` - The new name.
    /// * `ty` - The type it stands for.
    /// * `line` - Where it is declared.
    ///
    /// # Errors
    ///
    /// When the alias does not build: a word of the language for another
    /// type, or a chain that loops.
    fn alias(&mut self, name: &str, ty: &TypeExpr, line: usize) -> anyhow::Result<()> {
        if *ty == TypeExpr::Named(name.to_owned())
            || utypes::parse_type(name).is_ok_and(|own| own == *ty)
        {
            return Ok(());
        }
        let built = build_alias(name, ty, &self.known, self.abi.word)
            .map_err(|e| anyhow::anyhow!("line {line}: {e}"))?;
        self.define(name, built, line)
    }

    /// Records a type the text defined.
    ///
    /// # Arguments
    ///
    /// * `name` - Its name.
    /// * `ty` - The type.
    /// * `line` - Where it is defined.
    ///
    /// # Errors
    ///
    /// When the text defines the name twice, or more types than an overlay
    /// holds.
    fn define(&mut self, name: &str, ty: UserType, line: usize) -> anyhow::Result<()> {
        if self.out.types.iter().any(|(n, _, _)| n == name) {
            return Err(anyhow::anyhow!("line {line}: {name} is defined twice"));
        }
        if self.out.types.len() >= utypes::TYPES_MAX {
            return Err(anyhow::anyhow!(
                "line {line}: the text defines more than {} types",
                utypes::TYPES_MAX
            ));
        }
        self.later.remove(name);
        self.known.insert(name.to_owned(), ty.clone());
        let align = self.align_of(&TypeExpr::Named(name.to_owned()), 0);
        self.out.types.push((name.to_owned(), ty, align));
        Ok(())
    }

    /// Reads `static_assert(...)` and checks it, `static_assert` already
    /// read.
    ///
    /// # Arguments
    ///
    /// * `line` - Where it is.
    ///
    /// # Errors
    ///
    /// When it is not an `offsetof` or `sizeof` comparison, names nothing
    /// defined, or does not hold.
    fn static_assert(&mut self, line: usize) -> anyhow::Result<()> {
        self.expect('(', "after static_assert")?;
        let what = self.ident("offsetof or sizeof")?;
        self.expect('(', "after offsetof or sizeof")?;
        self.eat_word("struct");
        let name = self.ident("a struct's name")?;
        let ty = TypeExpr::Named(name.clone());
        let (actual, spelled) = match what.as_str() {
            "offsetof" => {
                self.expect(',', "between the struct and its field")?;
                let field = self.ident("a field's name")?;
                let s = utypes::pointee_struct(&self.known, &ty).ok_or_else(|| {
                    anyhow::anyhow!("line {line}: {name} is no struct defined here")
                })?;
                let off = s
                    .fields
                    .iter()
                    .find(|(_, f)| f.name == field)
                    .map(|(off, _)| *off)
                    .ok_or_else(|| {
                        anyhow::anyhow!("line {line}: struct {name} has no field {field}")
                    })?;
                (off, format!("offsetof({name}, {field})"))
            }
            "sizeof" => {
                let size = utypes::width_of(&self.known, &ty, self.abi.word)
                    .filter(|_| !self.later.contains(&name))
                    .ok_or_else(|| anyhow::anyhow!("line {line}: {name} is not defined"))?;
                (size, format!("sizeof({name})"))
            }
            _ => {
                return Err(anyhow::anyhow!(
                    "line {line}: static_assert reads offsetof(S, f) == N and sizeof(S) == N only"
                ));
            }
        };
        self.expect(')', "closing the operand")?;
        self.expect('=', "in ==")?;
        self.expect('=', "in ==")?;
        let want = self.integer()?;
        if self.eat(',') {
            match self.next().map(|t| &t.tok) {
                Some(Tok::Str) => {}
                Some(_) | None => {
                    return Err(anyhow::anyhow!(
                        "line {line}: a static_assert's message is a string"
                    ));
                }
            }
        }
        self.expect(')', "closing static_assert")?;
        self.expect(';', "after static_assert")?;
        if i128::from(actual) != want {
            return Err(anyhow::anyhow!(
                "line {line}: static_assert fails: {spelled} is {actual:#x} under {} layout, not {want:#x}",
                self.abi.name()
            ));
        }
        Ok(())
    }
}

/// Rounds an offset up to an alignment.
///
/// # Arguments
///
/// * `offset` - The offset.
/// * `align` - The alignment, at least one.
///
/// # Returns
///
/// The rounded offset, or `None` when it overflows.
fn round_up(offset: u64, align: u64) -> Option<u64> {
    let align = align.max(1);
    offset.checked_add(align - 1).map(|v| v / align * align)
}

/// The largest power of two dividing a size, at most 16: the most a type
/// of that size can be aligned to and still tile an array.
///
/// # Arguments
///
/// * `size` - The size in bytes.
fn largest_power_dividing(size: u64) -> u64 {
    if size == 0 {
        return 1;
    }
    (1u64 << size.trailing_zeros().min(4)).max(1)
}

/// Reads C declarations into user types, laid out by an ABI.
///
/// The grammar, the layout rules and what is refused are in the module's
/// documentation ([`self`]). Every type the text defines is built against
/// the ones defined before it (in the overlay, then earlier in the text)
/// and checked as `set_type`'s structured form checks them.
///
/// # Arguments
///
/// * `text` - The declarations; at most [`TEXT_MAX`] bytes.
/// * `known` - The types already defined.
/// * `abi` - The layout rules.
///
/// # Returns
///
/// The types in the order the text defines them, with their alignments.
///
/// # Errors
///
/// The first thing refused, with its line: a construct the subset does not
/// read, a type that names nothing, an offset assertion that fails, or a
/// type that does not build.
///
/// # Examples
///
/// ```
/// use borer_engine::analysis::cdecl::{Abi, parse};
/// use std::collections::BTreeMap;
///
/// let abi = Abi { word: 8, windows: true };
/// let got = parse("struct S { char c; int n; char *p; };", &BTreeMap::new(), abi)
///     .expect("it reads");
/// assert_eq!(got.types.len(), 1);
/// ```
pub fn parse(text: &str, known: &BTreeMap<String, UserType>, abi: Abi) -> anyhow::Result<Declared> {
    if text.len() > TEXT_MAX {
        return Err(anyhow::anyhow!(
            "the declarations are {} bytes; {TEXT_MAX} is the most read at once",
            text.len()
        ));
    }
    let toks = lex(text)?;
    let mut later: BTreeSet<String> = BTreeSet::new();
    for pair in toks.windows(3) {
        if let [
            Token {
                tok: Tok::Word(kw), ..
            },
            Token {
                tok: Tok::Word(name),
                ..
            },
            Token {
                tok: Tok::Sym('{' | ';'),
                ..
            },
        ] = pair
            && kw == "struct"
        {
            later.insert(name.clone());
        }
    }
    let mut placeholders = known.clone();
    for name in &later {
        placeholders.entry(name.clone()).or_insert_with(|| {
            UserType::Struct(UserStruct {
                size: 0,
                fields: BTreeMap::new(),
            })
        });
    }
    let mut reader = Reader {
        toks: &toks,
        pos: 0,
        abi,
        known: placeholders,
        aligns: BTreeMap::new(),
        later,
        pack: None,
        saved: Vec::new(),
        out: Declared {
            types: Vec::new(),
            notes: Vec::new(),
        },
    };
    reader.statements()?;
    if reader.out.types.is_empty() {
        return Err(anyhow::anyhow!(
            "the text defines no type; write `struct S {{ int a; }};`"
        ));
    }
    if let Some(name) = reader.later.iter().find(|n| !known.contains_key(*n)) {
        return Err(anyhow::anyhow!(
            "struct {name} is declared but never defined; define it, or point at it as void *"
        ));
    }
    Ok(reader.out)
}

/// Describes what a text declared, one line per type: a struct with its
/// size, alignment and `offset name type` per field, an enum with its
/// width and values, a typedef with its target.
///
/// # Arguments
///
/// * `declared` - What [`parse`] read.
#[must_use]
pub fn describe(declared: &Declared) -> Vec<String> {
    let mut out: Vec<String> = declared
        .types
        .iter()
        .map(|(name, ty, align)| match ty {
            UserType::Struct(s) => {
                let fields = s
                    .fields
                    .iter()
                    .map(|(off, f)| format!("{off:#x} {} {}", f.name, f.ty.spell()))
                    .collect::<Vec<_>>()
                    .join(", ");
                format!(
                    "struct {name} ({:#x} bytes, align {align}): {fields}",
                    s.size
                )
            }
            UserType::Enum(e) => {
                let values = e
                    .values
                    .iter()
                    .map(|(v, n)| format!("{n} = {v:#x}"))
                    .collect::<Vec<_>>()
                    .join(", ");
                format!("enum {name} ({} bytes): {values}", e.size)
            }
            UserType::Alias(inner) => format!("typedef {name}: {}", inner.spell()),
        })
        .collect();
    out.extend(declared.notes.iter().cloned());
    out
}

#[cfg(test)]
#[expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]
mod tests {
    use super::{Abi, Declared, parse};
    use crate::analysis::utypes::{TypeExpr, UserType};
    use std::collections::BTreeMap;

    /// Windows x64.
    const X64: Abi = Abi {
        word: 8,
        windows: true,
    };
    /// Windows x86.
    const X86: Abi = Abi {
        word: 4,
        windows: true,
    };
    /// x86 System V.
    const I386: Abi = Abi {
        word: 4,
        windows: false,
    };

    /// The offsets, size and alignment of the struct `name` a text defines.
    ///
    /// # Arguments
    ///
    /// * `got` - What the text declared.
    /// * `name` - The struct.
    fn layout(got: &Declared, name: &str) -> (Vec<u64>, u64, u64) {
        let (_, ty, align) = got
            .types
            .iter()
            .find(|(n, _, _)| n == name)
            .unwrap_or_else(|| panic!("{name} missing"));
        let UserType::Struct(s) = ty else {
            panic!("{name} is no struct");
        };
        (s.fields.keys().copied().collect(), s.size, *align)
    }

    /// `char, int, char *` lays out to 0, 4, 8: 16 bytes on x64, 12 on
    /// x86; a packed struct to 0, 1, 5; an 8-byte scalar after a byte sits
    /// at 8 on Windows x86 and at 4 on System V.
    #[test]
    fn structs_lay_out_by_the_abi() {
        let text = "struct S { char c; int n; char *p; };";
        let x64 = parse(text, &BTreeMap::new(), X64).unwrap();
        assert_eq!(layout(&x64, "S"), (vec![0, 4, 8], 16, 8));
        let x86 = parse(text, &BTreeMap::new(), X86).unwrap();
        assert_eq!(layout(&x86, "S"), (vec![0, 4, 8], 12, 4));
        for packed in [
            "#pragma pack(push, 1)\nstruct S { char c; int n; char *p; };\n#pragma pack(pop)",
            "struct __attribute__((packed)) S { char c; int n; char *p; };",
            "struct S { char c; int n; char *p; } __attribute__((packed));",
        ] {
            let got = parse(packed, &BTreeMap::new(), X64).unwrap_or_else(|e| panic!("{e}"));
            assert_eq!(layout(&got, "S"), (vec![0, 1, 5], 13, 1), "{packed}");
        }
        let wide = "struct W { char c; double d; long long q; };";
        let msvc = parse(wide, &BTreeMap::new(), X86).unwrap();
        assert_eq!(layout(&msvc, "W"), (vec![0, 8, 16], 24, 8));
        let sysv = parse(wide, &BTreeMap::new(), I386).unwrap();
        assert_eq!(layout(&sysv, "W"), (vec![0, 4, 12], 20, 4));
        let two = parse(
            "#pragma pack(2)\nstruct P { char c; int n; };\n#pragma pack()\nstruct N { char c; int n; };",
            &BTreeMap::new(),
            X64,
        )
        .unwrap();
        assert_eq!(layout(&two, "P"), (vec![0, 2], 6, 2));
        assert_eq!(layout(&two, "N"), (vec![0, 4], 8, 4));
    }

    /// Nested structs, arrays, enums, typedefs and function pointers read
    /// into the language's types, each named as the text names it.
    #[test]
    fn declarations_read_into_user_types() {
        let text = "
            typedef unsigned char u8;          // a word of the language: dropped
            typedef enum { Idle, Run = 5, Done } State;
            typedef struct Vec { float x, y; } Vec, *PVec;
            struct Rec {
                const char *name;   // @0x0
                DWORD id;           // @0x8
                State state;
                struct Vec pos;     /* @0x10 */
                char tag[2][3];
                void (*cb)(int, char *);
                struct Rec *next;
                struct Later *later;
            };
            struct Later { u8 b; };
            static_assert(offsetof(Rec, next) == 0x28, \"next\");
            _Static_assert(sizeof(struct Rec) == 0x38);
        ";
        let got = parse(text, &BTreeMap::new(), X64).unwrap_or_else(|e| panic!("{e}"));
        let names: Vec<&str> = got.types.iter().map(|(n, _, _)| n.as_str()).collect();
        assert_eq!(names, ["State", "Vec", "PVec", "Rec", "Later"]);
        assert_eq!(
            layout(&got, "Rec"),
            (vec![0, 8, 12, 16, 24, 32, 40, 48], 0x38, 8)
        );
        let Some((_, UserType::Struct(rec), _)) = got.types.iter().find(|(n, _, _)| n == "Rec")
        else {
            panic!("no Rec");
        };
        let spelled: Vec<String> = rec.fields.values().map(|f| f.ty.spell()).collect();
        assert_eq!(
            spelled,
            [
                "char *",
                "u32",
                "State",
                "Vec",
                "char[3][2]",
                "u8 *",
                "Rec *",
                "Later *"
            ]
        );
        let Some((_, UserType::Enum(state), _)) = got.types.iter().find(|(n, _, _)| n == "State")
        else {
            panic!("no State");
        };
        assert_eq!(
            state.values,
            [
                (0, "Idle".to_owned()),
                (5, "Run".to_owned()),
                (6, "Done".to_owned())
            ]
        );
        assert!(matches!(
            got.types.iter().find(|(n, _, _)| n == "PVec"),
            Some((_, UserType::Alias(TypeExpr::Ptr(_)), _))
        ));
    }

    /// An offset assertion that does not hold refuses the text, naming the
    /// field and both offsets; so does a failing `static_assert`.
    #[test]
    fn a_failing_offset_assertion_is_refused() {
        let err = parse(
            "struct S {\n char c;\n int n; // @0x2\n};",
            &BTreeMap::new(),
            X64,
        )
        .unwrap_err()
        .to_string();
        assert!(
            err.contains("line 3: field n of struct S is at 0x4 under x64 Windows layout, not 0x2"),
            "{err}"
        );
        let err = parse(
            "struct S { char c; int n; };\nstatic_assert(sizeof(S) == 5);",
            &BTreeMap::new(),
            X64,
        )
        .unwrap_err()
        .to_string();
        assert!(
            err.contains("sizeof(S) is 0x8 under x64 Windows layout, not 0x5"),
            "{err}"
        );
        let err = parse(
            "struct S { int a; };\nstatic_assert(offsetof(S, b) == 0);",
            &BTreeMap::new(),
            X64,
        )
        .unwrap_err()
        .to_string();
        assert!(err.contains("has no field b"), "{err}");
    }

    /// What the subset does not read is refused with what it is; hostile
    /// texts (deep nesting, huge arrays, loops) answer an error, not a hang.
    #[test]
    fn what_the_subset_does_not_read_is_refused() {
        for (text, says) in [
            ("union U { int a; float b; };", "unions are not read"),
            ("struct S { int a : 3; };", "bit-field"),
            (
                "struct S { struct T { int a; } t; };",
                "defined inside struct S",
            ),
            ("#include <x.h>\nstruct S { int a; };", "only #pragma pack"),
            ("struct S { int a[0xffffffffffff]; };", "is not a count"),
            ("struct S { int a[]; };", "flexible array"),
            ("struct S { long double d; };", "long double"),
            ("struct S { int a; } s;", "declares a variable"),
            (
                "struct S { struct T t; };\nstruct T { int a; };",
                "used by value before",
            ),
            ("struct S { Mystery m; };", "is no type"),
            ("enum E { A = B };", "not an integer literal"),
            ("struct S;\nstruct T { struct S *s; };", "never defined"),
            (
                "typedef int A;\ntypedef A B;\ntypedef B A;",
                "resolves to no size",
            ),
            ("typedef int A;\ntypedef long A;", "defined twice"),
            ("struct S { int a; }; // @0x4", "follows no field"),
            ("", "defines no type"),
        ] {
            let err = parse(text, &BTreeMap::new(), X64)
                .expect_err(text)
                .to_string();
            assert!(err.contains(says), "{text}: {err}");
        }
        let deep = format!("struct S {{ void (*f){}; }};", "(".repeat(10_000));
        assert!(parse(&deep, &BTreeMap::new(), X64).is_err());
        let long = "struct S { int a; };".repeat(4000);
        assert!(
            parse(&long, &BTreeMap::new(), X64).is_err(),
            "past the text cap"
        );
    }

    /// A struct defined before the text, by the structured form, aligns as
    /// its fields do when the text embeds it; a pointer to a struct the
    /// text never defines reads as `u8 *` and says so.
    #[test]
    fn earlier_types_embed_and_unknown_pointers_read_as_bytes() {
        let mut known = BTreeMap::new();
        known.insert(
            "Pair".to_owned(),
            crate::analysis::utypes::build_struct(
                "Pair",
                None,
                &[
                    (0, "a".to_owned(), TypeExpr::U32),
                    (8, "b".to_owned(), TypeExpr::U64),
                ],
                &BTreeMap::new(),
                8,
            )
            .unwrap(),
        );
        let got = parse(
            "struct H { char c; Pair p; struct _IO_FILE *f; };",
            &known,
            X64,
        )
        .unwrap();
        assert_eq!(layout(&got, "H"), (vec![0, 8, 24], 32, 8));
        assert!(
            got.notes
                .iter()
                .any(|n| n.contains("_IO_FILE is defined nowhere")),
            "{got:?}"
        );
        let lines = super::describe(&got);
        assert!(
            lines[0]
                .starts_with("struct H (0x20 bytes, align 8): 0x0 c char, 0x8 p Pair, 0x18 f u8 *"),
            "{lines:?}"
        );
    }
}
