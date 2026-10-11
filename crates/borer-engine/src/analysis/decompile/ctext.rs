//! The decompiler's printed text read back as C: its tokens, its types and
//! its expressions.
//!
//! What [`super::interp`] runs. The text is borer's own output, so the
//! grammar is the part of C it prints: integer, floating, character and
//! string literals, names (a `Class::method` read as one name), the
//! operators at C's precedence, casts to the scalar types and pointers to
//! them, calls, indexing and `->field`. Whatever else a line holds fails to
//! parse with a message naming it, so the caller can say which line it
//! could not read instead of guessing what it meant.

use crate::num::lo32;

/// The scalar a C type is built on.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum Base {
    /// An integer of this many bits, and whether it is signed.
    Int(u8, bool),
    /// An IEEE-754 value of this many bits, 32 or 64.
    Float(u8),
    /// `void`: no value of its own, and a byte behind a pointer, as GNU C
    /// steps a `void *`.
    Void,
    /// A type the text names that this reader does not know (a class, a
    /// struct, an SDK typedef): it has no size, so a pointer to it cannot be
    /// stepped, and as a value it is a machine word.
    Opaque,
    /// A 128-bit vector value, which nothing here computes with.
    Wide,
}

/// A C type: a scalar and the pointers built on it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) struct CTy {
    /// The scalar.
    pub(super) base: Base,
    /// How many pointers deep: zero for the scalar itself.
    pub(super) ptr: u8,
}

impl CTy {
    /// An integer type.
    ///
    /// # Arguments
    ///
    /// * `bits` - Its width: 8, 16, 32 or 64.
    /// * `signed` - Whether it is signed.
    pub(super) const fn int(bits: u8, signed: bool) -> Self {
        Self {
            base: Base::Int(bits, signed),
            ptr: 0,
        }
    }

    /// A scalar type with no pointer on it.
    ///
    /// # Arguments
    ///
    /// * `base` - The scalar.
    pub(super) const fn of(base: Base) -> Self {
        Self { base, ptr: 0 }
    }

    /// The pointer to this type.
    pub(super) fn to(self) -> Self {
        Self {
            base: self.base,
            ptr: self.ptr.saturating_add(1),
        }
    }

    /// The type a pointer of this type points at, `None` for a scalar.
    pub(super) fn pointee(self) -> Option<Self> {
        Some(Self {
            base: self.base,
            ptr: self.ptr.checked_sub(1)?,
        })
    }

    /// Tells whether the type is a pointer.
    pub(super) fn is_ptr(self) -> bool {
        self.ptr > 0
    }

    /// The width of a floating type, `None` for anything else.
    pub(super) fn float(self) -> Option<u8> {
        match (self.ptr, self.base) {
            (0, Base::Float(bits)) => Some(bits),
            _ => None,
        }
    }

    /// Tells whether a value of the type is a signed integer.
    pub(super) fn signed(self) -> bool {
        self.ptr == 0 && matches!(self.base, Base::Int(_, true))
    }

    /// The bits a value of the type holds.
    ///
    /// # Arguments
    ///
    /// * `word` - The machine word in bits, the width of a pointer.
    ///
    /// # Returns
    ///
    /// The width, or `None` for `void` and the vector type, which hold no
    /// value this reader computes with.
    pub(super) fn bits(self, word: u8) -> Option<u8> {
        if self.ptr > 0 {
            return Some(word);
        }
        match self.base {
            Base::Int(bits, _) | Base::Float(bits) => Some(bits),
            Base::Opaque => Some(word),
            Base::Void | Base::Wide => None,
        }
    }

    /// The bytes an object of the type takes: what one step of a pointer to
    /// it moves.
    ///
    /// # Arguments
    ///
    /// * `word` - The machine word in bits.
    ///
    /// # Returns
    ///
    /// The size, or `None` for a type whose size the text does not give.
    pub(super) fn size(self, word: u8) -> Option<u64> {
        if self.ptr > 0 {
            return Some(u64::from(word / 8));
        }
        match self.base {
            Base::Int(bits, _) | Base::Float(bits) => Some(u64::from(bits / 8)),
            Base::Void => Some(1),
            Base::Wide => Some(16),
            Base::Opaque => None,
        }
    }
}

/// The type a type name means, for the names the text and the SDK headers
/// it borrows from use.
///
/// # Arguments
///
/// * `name` - One type name.
/// * `word` - The machine word in bits.
///
/// # Returns
///
/// The type, or `None` for a name this does not know.
pub(super) fn named_type(name: &str, word: u8) -> Option<CTy> {
    let void = CTy::of(Base::Void);
    let wide_char = CTy::int(16, false);
    Some(match name {
        "uint8_t" | "BYTE" | "UCHAR" | "BOOLEAN" | "bool" | "_Bool" => CTy::int(8, false),
        "int8_t" | "CHAR" => CTy::int(8, true),
        "uint16_t" | "WORD" | "USHORT" | "wchar_t" | "WCHAR" => wide_char,
        "int16_t" | "SHORT" => CTy::int(16, true),
        "uint32_t" | "DWORD" | "UINT" | "ULONG" => CTy::int(32, false),
        "int32_t" | "BOOL" | "INT" | "LONG" | "NTSTATUS" | "HRESULT" => CTy::int(32, true),
        "uint64_t" | "QWORD" | "ULONGLONG" | "DWORD64" | "ULONG64" => CTy::int(64, false),
        "int64_t" | "LONGLONG" | "LONG64" => CTy::int(64, true),
        "size_t" | "SIZE_T" | "uintptr_t" | "ULONG_PTR" | "DWORD_PTR" | "UINT_PTR" => {
            CTy::int(word, false)
        }
        "intptr_t" | "ptrdiff_t" | "SSIZE_T" | "LONG_PTR" | "INT_PTR" => CTy::int(word, true),
        "float" => CTy::of(Base::Float(32)),
        "double" => CTy::of(Base::Float(64)),
        "void" | "VOID" => void,
        "uint128_t" | "int128_t" => CTy::of(Base::Wide),
        "HANDLE" | "HMODULE" | "HINSTANCE" | "PVOID" | "LPVOID" | "LPCVOID" | "HKEY" => void.to(),
        "LPSTR" | "LPCSTR" | "PSTR" | "PCSTR" => CTy::int(8, true).to(),
        "LPWSTR" | "LPCWSTR" | "PWSTR" | "PCWSTR" => wide_char.to(),
        _ => return None,
    })
}

/// A piece of a line of text.
#[derive(Debug, Clone, PartialEq)]
pub(super) enum Tok {
    /// A name; a `Class::method` or `ns::name` is one.
    Name(String),
    /// An integer or character literal and the type C gives it.
    Int(u64, CTy),
    /// A floating literal and its type.
    Float(f64, CTy),
    /// A string literal's bytes with its terminator, a wide one's as
    /// UTF-16LE.
    Str(Vec<u8>),
    /// An operator or punctuation.
    Punct(&'static str),
}

/// The operators and punctuation, longest first so a lexer takes the
/// longest that matches.
const PUNCTS: [&str; 47] = [
    "<<=", ">>=", "...", "->", "++", "--", "<<", ">>", "<=", ">=", "==", "!=", "&&", "||", "+=",
    "-=", "*=", "/=", "%=", "&=", "|=", "^=", "::", "+", "-", "*", "/", "%", "&", "|", "^", "~",
    "!", "<", ">", "=", "?", ":", "(", ")", "[", "]", "{", "}", ",", ";", ".",
];

/// The integer type C gives a literal.
///
/// The first of `int`, `unsigned int`, `long long`, `unsigned long long`
/// that holds it, a decimal one skipping the unsigned types, as the
/// standard orders them for the 64-bit Windows model where `long` is 32
/// bits; a suffix narrows the choice.
///
/// # Arguments
///
/// * `v` - The value.
/// * `hex` - Whether it was written in hex or octal.
/// * `suffix` - Its suffix letters, lowercased.
fn literal_type(v: u64, hex: bool, suffix: &str) -> CTy {
    let unsigned = suffix.contains('u');
    let long_long = suffix.contains("ll") || suffix.contains("i64");
    let fits_i32 = v <= 0x7fff_ffff;
    let fits_u32 = v <= 0xffff_ffff;
    let fits_i64 = v <= 0x7fff_ffff_ffff_ffff;
    match (unsigned, long_long) {
        (true, true) => CTy::int(64, false),
        (true, false) if fits_u32 => CTy::int(32, false),
        (true, false) => CTy::int(64, false),
        (false, false) if fits_i32 => CTy::int(32, true),
        (false, false) if hex && fits_u32 => CTy::int(32, false),
        (false, _) if fits_i64 => CTy::int(64, true),
        (false, _) => CTy::int(64, false),
    }
}

/// Reads one escape after a backslash in a literal.
///
/// # Arguments
///
/// * `chars` - The characters after the backslash.
///
/// # Returns
///
/// The code unit, or `None` when the escape does not read.
fn escape(chars: &mut std::iter::Peekable<std::str::CharIndices<'_>>) -> Option<u32> {
    let (_, c) = chars.next()?;
    Some(match c {
        'n' => 10,
        'r' => 13,
        't' => 9,
        'a' => 7,
        'b' => 8,
        'f' => 12,
        'v' => 11,
        'x' => {
            let mut v = 0u32;
            let mut any = false;
            while let Some(&(_, h)) = chars.peek() {
                let Some(d) = h.to_digit(16) else { break };
                v = v.checked_mul(16)?.checked_add(d)?;
                any = true;
                chars.next();
            }
            if !any {
                return None;
            }
            v
        }
        '0'..='7' => {
            let mut v = c.to_digit(8)?;
            for _ in 0..2 {
                let Some(d) = chars.peek().and_then(|&(_, o)| o.to_digit(8)) else {
                    break;
                };
                v = v * 8 + d;
                chars.next();
            }
            v
        }
        other => u32::from(other),
    })
}

/// Splits a line into its tokens, leaving out whitespace and comments.
///
/// # Arguments
///
/// * `text` - The line, or a part of one.
///
/// # Errors
///
/// A character no token starts with, a literal that does not end or does
/// not fit 64 bits.
pub(super) fn tokens(text: &str) -> Result<Vec<Tok>, String> {
    let mut out = Vec::new();
    let mut chars = text.char_indices().peekable();
    while let Some(&(at, c)) = chars.peek() {
        let rest = text.get(at..).unwrap_or("");
        if c.is_whitespace() {
            chars.next();
        } else if rest.starts_with("//") {
            break;
        } else if rest.starts_with("/*") {
            let end = rest.find("*/").ok_or("a comment that does not end")?;
            while chars.peek().is_some_and(|&(k, _)| k < at + end + 2) {
                chars.next();
            }
        } else if c == '"' || (c == 'L' && rest.starts_with("L\"")) {
            let wide = c == 'L';
            if wide {
                chars.next();
            }
            chars.next();
            let mut units: Vec<u32> = Vec::new();
            loop {
                let (_, s) = chars.next().ok_or("a string that does not end")?;
                match s {
                    '"' => break,
                    '\\' => units.push(escape(&mut chars).ok_or("a bad escape in a string")?),
                    other => units.push(u32::from(other)),
                }
            }
            units.push(0);
            let mut bytes = Vec::with_capacity(units.len() * 2);
            for u in units {
                if wide {
                    let unit = u16::try_from(u).map_err(|_| "a wide character past 16 bits")?;
                    bytes.extend(unit.to_le_bytes());
                } else {
                    bytes.push(u8::try_from(u).map_err(|_| "a character past 8 bits")?);
                }
            }
            out.push(Tok::Str(bytes));
        } else if c == '\'' {
            chars.next();
            let mut v = 0u64;
            loop {
                let (_, s) = chars
                    .next()
                    .ok_or("a character literal that does not end")?;
                let unit = match s {
                    '\'' => break,
                    '\\' => escape(&mut chars).ok_or("a bad escape in a character")?,
                    other => u32::from(other),
                };
                v = (v << 8) | u64::from(unit & 0xff);
            }
            out.push(Tok::Int(v, CTy::int(32, true)));
        } else if c.is_ascii_digit()
            || (c == '.' && rest[1..].starts_with(|d: char| d.is_ascii_digit()))
        {
            let bytes = rest.as_bytes();
            let hex = rest.starts_with("0x") || rest.starts_with("0X");
            let mut len = 0;
            while let Some(&d) = bytes.get(len) {
                let exponent_sign = !hex
                    && matches!(d, b'+' | b'-')
                    && len > 0
                    && matches!(bytes.get(len - 1), Some(b'e' | b'E'));
                if !(d.is_ascii_alphanumeric() || d == b'.' || d == b'_' || exponent_sign) {
                    break;
                }
                len += 1;
            }
            out.push(number(&rest[..len])?);
            while chars.peek().is_some_and(|&(k, _)| k < at + len) {
                chars.next();
            }
        } else if c.is_alphabetic() || c == '_' {
            let mut end = rest
                .find(|d: char| !(d.is_alphanumeric() || d == '_'))
                .unwrap_or(rest.len());
            while rest[end..].starts_with("::")
                && rest[end + 2..].starts_with(|d: char| d.is_alphabetic() || d == '_' || d == '~')
            {
                let tail = &rest[end + 2..];
                let skip = usize::from(tail.starts_with('~'));
                end += 2
                    + skip
                    + tail[skip..]
                        .find(|d: char| !(d.is_alphanumeric() || d == '_'))
                        .unwrap_or(tail.len() - skip);
            }
            for word in ["new", "delete"] {
                let joined = rest[end..]
                    .strip_prefix(' ')
                    .and_then(|r| r.strip_prefix(word));
                if rest[..end].ends_with("operator")
                    && joined
                        .is_some_and(|r| !r.starts_with(|d: char| d.is_alphanumeric() || d == '_'))
                {
                    end += 1 + word.len();
                }
            }
            out.push(Tok::Name(rest[..end].to_owned()));
            while chars.peek().is_some_and(|&(k, _)| k < at + end) {
                chars.next();
            }
        } else {
            let p = PUNCTS
                .iter()
                .find(|p| rest.starts_with(**p))
                .ok_or_else(|| format!("cannot read `{c}`"))?;
            out.push(Tok::Punct(p));
            for _ in 0..p.len() {
                chars.next();
            }
        }
    }
    Ok(out)
}

/// Reads a numeric literal.
///
/// # Arguments
///
/// * `lit` - The literal as written, suffix included.
///
/// # Errors
///
/// When it does not read or does not fit 64 bits.
fn number(lit: &str) -> Result<Tok, String> {
    let bad = || format!("cannot read the number {lit}");
    let lower = lit.to_ascii_lowercase();
    if let Some(hex) = lower.strip_prefix("0x") {
        let digits = hex.trim_end_matches(['u', 'l']);
        let suffix = &hex[digits.len()..];
        let v = u64::from_str_radix(digits, 16).map_err(|_| bad())?;
        return Ok(Tok::Int(v, literal_type(v, true, suffix)));
    }
    let float = lower.contains(['.', 'e']) || lower.ends_with('f');
    if float {
        let (digits, ty) = match lower.strip_suffix('f') {
            Some(d) => (d, CTy::of(Base::Float(32))),
            None => (lower.as_str(), CTy::of(Base::Float(64))),
        };
        let v: f64 = digits.parse().map_err(|_| bad())?;
        return Ok(Tok::Float(v, ty));
    }
    let digits = lower.trim_end_matches(['u', 'l']);
    let suffix = &lower[digits.len()..];
    let octal = digits.len() > 1 && digits.starts_with('0');
    let v = if octal {
        u64::from_str_radix(&digits[1..], 8).map_err(|_| bad())?
    } else {
        digits.parse::<u64>().map_err(|_| bad())?
    };
    Ok(Tok::Int(v, literal_type(v, octal, suffix)))
}

/// The index of the `)` closing the `(` at `open`.
///
/// # Arguments
///
/// * `toks` - The tokens.
/// * `open` - The index of the `(`.
pub(super) fn closing(toks: &[Tok], open: usize) -> Option<usize> {
    let mut depth = 0usize;
    for (k, t) in toks.iter().enumerate().skip(open) {
        match t {
            Tok::Punct("(") => depth += 1,
            Tok::Punct(")") => {
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

/// Splits tokens at the top-level punctuation `p`.
///
/// # Arguments
///
/// * `toks` - The tokens.
/// * `p` - The separator.
pub(super) fn split_top<'t>(toks: &'t [Tok], p: &str) -> Vec<&'t [Tok]> {
    let mut out = Vec::new();
    let mut depth = 0usize;
    let mut from = 0;
    for (k, t) in toks.iter().enumerate() {
        match t {
            Tok::Punct("(" | "[") => depth += 1,
            Tok::Punct(")" | "]") => depth = depth.saturating_sub(1),
            Tok::Punct(q) if *q == p && depth == 0 => {
                out.push(toks.get(from..k).unwrap_or(&[]));
                from = k + 1;
            }
            _ => {}
        }
    }
    out.push(toks.get(from..).unwrap_or(&[]));
    out
}

/// Reads a type at `at`, moving past it only when one reads.
///
/// Qualifiers are skipped, the integer keywords combine as C combines them
/// (`unsigned long long`), a single name is a known scalar or a type this
/// does not know, and each `*` or `&` adds a pointer.
///
/// # Arguments
///
/// * `toks` - The tokens.
/// * `at` - Where the type starts; left past it.
/// * `word` - The machine word in bits.
///
/// # Returns
///
/// The type, or `None` when the tokens there are no type.
fn read_type(toks: &[Tok], at: &mut usize, word: u8) -> Option<CTy> {
    let start = *at;
    let mut words: Vec<&str> = Vec::new();
    let mut named: Option<&str> = None;
    while let Some(Tok::Name(n)) = toks.get(*at) {
        match n.as_str() {
            "const" | "volatile" | "struct" | "class" | "union" | "enum" => {}
            "unsigned" | "signed" | "long" | "short" | "int" | "char" => words.push(n),
            _ if named.is_none() && words.is_empty() => named = Some(n),
            _ => break,
        }
        *at += 1;
    }
    let base = if let Some(n) = named {
        named_type(n, word).unwrap_or(CTy::of(Base::Opaque))
    } else if words.is_empty() {
        *at = start;
        return None;
    } else {
        let unsigned = words.contains(&"unsigned");
        let longs = words.iter().filter(|w| **w == "long").count();
        let bits = if words.contains(&"char") {
            8
        } else if words.contains(&"short") {
            16
        } else if longs >= 2 {
            64
        } else {
            32
        };
        CTy::int(bits, !unsigned)
    };
    let mut ty = base;
    while let Some(Tok::Punct("*" | "&")) = toks.get(*at) {
        ty = ty.to();
        *at += 1;
        while matches!(toks.get(*at), Some(Tok::Name(n)) if n == "const") {
            *at += 1;
        }
    }
    Some(ty)
}

/// Reads a declaration's type off the front of `toks`.
///
/// # Arguments
///
/// * `toks` - The declaration's tokens.
/// * `word` - The machine word in bits.
///
/// # Returns
///
/// The scalar the declaration is of, and how many tokens it took before its
/// first pointer, which belongs to the name after it; `None` when no type
/// leads.
pub(super) fn leading_type(toks: &[Tok], word: u8) -> Option<(CTy, usize)> {
    let mut at = 0;
    let ty = read_type(toks, &mut at, word)?;
    while at > 0 && matches!(toks.get(at - 1), Some(Tok::Punct("*" | "&"))) {
        at -= 1;
    }
    Some((CTy::of(ty.base), at))
}

/// A unary operator.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum Un {
    /// `-x`.
    Neg,
    /// `+x`.
    Plus,
    /// `~x`.
    Not,
    /// `!x`.
    LogNot,
    /// `*x`.
    Deref,
    /// `&x`.
    Addr,
}

/// A binary operator that evaluates both operands.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum Bin {
    /// `*`.
    Mul,
    /// `/`.
    Div,
    /// `%`.
    Rem,
    /// `+`.
    Add,
    /// `-`.
    Sub,
    /// `<<`.
    Shl,
    /// `>>`.
    Shr,
    /// `<`.
    Lt,
    /// `<=`.
    Le,
    /// `>`.
    Gt,
    /// `>=`.
    Ge,
    /// `==`.
    Eq,
    /// `!=`.
    Ne,
    /// `&`.
    And,
    /// `^`.
    Xor,
    /// `|`.
    Or,
}

impl Bin {
    /// The operator a token spells, with its precedence (higher binds
    /// tighter), for the operators read by precedence climbing.
    ///
    /// # Arguments
    ///
    /// * `p` - The token's text.
    fn of(p: &str) -> Option<(Self, u8)> {
        Some(match p {
            "*" => (Self::Mul, 10),
            "/" => (Self::Div, 10),
            "%" => (Self::Rem, 10),
            "+" => (Self::Add, 9),
            "-" => (Self::Sub, 9),
            "<<" => (Self::Shl, 8),
            ">>" => (Self::Shr, 8),
            "<" => (Self::Lt, 7),
            "<=" => (Self::Le, 7),
            ">" => (Self::Gt, 7),
            ">=" => (Self::Ge, 7),
            "==" => (Self::Eq, 6),
            "!=" => (Self::Ne, 6),
            "&" => (Self::And, 5),
            "^" => (Self::Xor, 4),
            "|" => (Self::Or, 3),
            _ => return None,
        })
    }

    /// The operator a compound assignment applies: `+=` is `+`.
    ///
    /// # Arguments
    ///
    /// * `p` - The assignment token's text.
    fn compound(p: &str) -> Option<Self> {
        Some(match p {
            "+=" => Self::Add,
            "-=" => Self::Sub,
            "*=" => Self::Mul,
            "/=" => Self::Div,
            "%=" => Self::Rem,
            "&=" => Self::And,
            "|=" => Self::Or,
            "^=" => Self::Xor,
            "<<=" => Self::Shl,
            ">>=" => Self::Shr,
            _ => return None,
        })
    }

    /// Tells whether the operator compares, giving an `int` truth value.
    pub(super) fn compares(self) -> bool {
        matches!(
            self,
            Self::Lt | Self::Le | Self::Gt | Self::Ge | Self::Eq | Self::Ne
        )
    }
}

/// An expression of the text.
#[derive(Debug, Clone, PartialEq)]
pub(super) enum Ast {
    /// An integer literal and its type.
    Int(u64, CTy),
    /// A floating literal and its type.
    Float(f64, CTy),
    /// A string literal's bytes, terminator included.
    Str(Vec<u8>),
    /// A name: a variable, a parameter, a function, a global.
    Name(String),
    /// A unary operator applied.
    Un(Un, Box<Ast>),
    /// A cast.
    Cast(CTy, Box<Ast>),
    /// A binary operator applied.
    Bin(Bin, Box<Ast>, Box<Ast>),
    /// `&&` when true, `||` when false, with its operands.
    Logic(bool, Box<Ast>, Box<Ast>),
    /// `c ? a : b`; `c ?: b` leaves the middle out and yields `c` itself.
    Pick(Box<Ast>, Option<Box<Ast>>, Box<Ast>),
    /// A call and its arguments.
    Call(Box<Ast>, Vec<Ast>),
    /// `a[i]`.
    Index(Box<Ast>, Box<Ast>),
    /// `p->field`, or `p->field.member` with the members joined by dots.
    Arrow(Box<Ast>, String),
    /// `=`, or a compound assignment with its operator.
    Assign(Option<Bin>, Box<Ast>, Box<Ast>),
    /// `++` or `--`, before or after its operand: `(prefix, up, operand)`.
    Step(bool, bool, Box<Ast>),
}

/// Deepest nesting an expression is read to, so a hostile line cannot run
/// the reader out of stack.
const DEPTH_MAX: u16 = 200;

/// A reader of one expression's tokens.
struct Parser<'t> {
    /// The tokens.
    toks: &'t [Tok],
    /// The next one to read.
    at: usize,
    /// Tells whether a name is one the text gives a value (a variable, a
    /// parameter, a function), which a parenthesized name is not a cast to.
    is_value: &'t dyn Fn(&str) -> bool,
    /// The machine word in bits.
    word: u8,
    /// How deep the reading is nested.
    depth: u16,
}

impl Parser<'_> {
    /// The next token, unread.
    fn peek(&self) -> Option<&Tok> {
        self.toks.get(self.at)
    }

    /// The token after the next, unread.
    fn peek2(&self) -> Option<&Tok> {
        self.toks.get(self.at + 1)
    }

    /// Reads the next token if it is the punctuation `p`.
    ///
    /// # Arguments
    ///
    /// * `p` - The punctuation.
    fn eat(&mut self, p: &str) -> bool {
        if matches!(self.peek(), Some(Tok::Punct(q)) if *q == p) {
            self.at += 1;
            true
        } else {
            false
        }
    }

    /// Reads the punctuation `p`, or says what stood there instead.
    ///
    /// # Arguments
    ///
    /// * `p` - The punctuation.
    ///
    /// # Errors
    ///
    /// When the next token is something else.
    fn expect(&mut self, p: &str) -> Result<(), String> {
        if self.eat(p) {
            Ok(())
        } else {
            Err(format!("expected `{p}`, read {}", self.shown()))
        }
    }

    /// The next token as a message shows it.
    fn shown(&self) -> String {
        match self.peek() {
            None => "the end".to_owned(),
            Some(Tok::Name(n)) => format!("`{n}`"),
            Some(Tok::Punct(p)) => format!("`{p}`"),
            Some(Tok::Int(v, _)) => format!("`{v:#x}`"),
            Some(Tok::Float(v, _)) => format!("`{v}`"),
            Some(Tok::Str(_)) => "a string".to_owned(),
        }
    }

    /// Enters one level of nesting.
    ///
    /// # Errors
    ///
    /// When the expression nests deeper than [`DEPTH_MAX`].
    fn deeper(&mut self) -> Result<(), String> {
        self.depth += 1;
        if self.depth > DEPTH_MAX {
            return Err("an expression nested too deep".to_owned());
        }
        Ok(())
    }

    /// Reads an assignment expression, the loosest form.
    ///
    /// # Errors
    ///
    /// When the tokens do not read as one.
    fn assign(&mut self) -> Result<Ast, String> {
        self.deeper()?;
        let left = self.pick()?;
        let op = match self.peek() {
            Some(Tok::Punct("=")) => Some(None),
            Some(Tok::Punct(p)) => Bin::compound(p).map(Some),
            _ => None,
        };
        let out = match op {
            Some(op) => {
                self.at += 1;
                let right = self.assign()?;
                Ast::Assign(op, Box::new(left), Box::new(right))
            }
            None => left,
        };
        self.depth -= 1;
        Ok(out)
    }

    /// Reads a conditional expression.
    ///
    /// # Errors
    ///
    /// When the tokens do not read as one.
    fn pick(&mut self) -> Result<Ast, String> {
        let test = self.logic(false)?;
        if !self.eat("?") {
            return Ok(test);
        }
        let middle = if self.eat(":") {
            None
        } else {
            let m = self.assign()?;
            self.expect(":")?;
            Some(Box::new(m))
        };
        self.deeper()?;
        let other = self.pick()?;
        self.depth -= 1;
        Ok(Ast::Pick(Box::new(test), middle, Box::new(other)))
    }

    /// Reads a `||` chain, or with `and` an `&&` chain.
    ///
    /// # Arguments
    ///
    /// * `and` - Read the `&&` level instead of the `||` level.
    ///
    /// # Errors
    ///
    /// When the tokens do not read as one.
    fn logic(&mut self, and: bool) -> Result<Ast, String> {
        let mut left = if and {
            self.binary(0)?
        } else {
            self.logic(true)?
        };
        let op = if and { "&&" } else { "||" };
        while self.eat(op) {
            let right = if and {
                self.binary(0)?
            } else {
                self.logic(true)?
            };
            left = Ast::Logic(and, Box::new(left), Box::new(right));
        }
        Ok(left)
    }

    /// Reads the binary operators binding at least as tight as `min`, by
    /// precedence climbing.
    ///
    /// # Arguments
    ///
    /// * `min` - The loosest precedence read here.
    ///
    /// # Errors
    ///
    /// When the tokens do not read as an expression.
    fn binary(&mut self, min: u8) -> Result<Ast, String> {
        let mut left = self.unary()?;
        while let Some(Tok::Punct(p)) = self.peek() {
            let Some((op, prec)) = Bin::of(p) else { break };
            if prec < min {
                break;
            }
            self.at += 1;
            self.deeper()?;
            let right = self.binary(prec + 1)?;
            self.depth -= 1;
            left = Ast::Bin(op, Box::new(left), Box::new(right));
        }
        Ok(left)
    }

    /// Tells whether a `(` at the next token opens a cast: its first name is
    /// a type keyword or a known type, or a name that holds no value followed
    /// by a pointer, or a name that holds none whose `)` an operand follows.
    fn at_cast(&self) -> bool {
        let Some(Tok::Name(n)) = self.peek2() else {
            return false;
        };
        let keyword = matches!(
            n.as_str(),
            "const" | "unsigned" | "signed" | "long" | "short" | "int" | "char" | "struct"
        );
        if keyword || named_type(n, self.word).is_some() {
            return !(self.is_value)(n);
        }
        if (self.is_value)(n) {
            return false;
        }
        match self.toks.get(self.at + 2) {
            Some(Tok::Punct("*" | "&")) => true,
            Some(Tok::Punct(")")) => matches!(
                self.toks.get(self.at + 3),
                Some(Tok::Name(_) | Tok::Int(..) | Tok::Float(..) | Tok::Str(_) | Tok::Punct("("))
            ),
            _ => false,
        }
    }

    /// Reads a unary expression: prefix operators and casts, then postfix.
    ///
    /// # Errors
    ///
    /// When the tokens do not read as one.
    fn unary(&mut self) -> Result<Ast, String> {
        self.deeper()?;
        let op = match self.peek() {
            Some(Tok::Punct("-")) => Some(Un::Neg),
            Some(Tok::Punct("+")) => Some(Un::Plus),
            Some(Tok::Punct("~")) => Some(Un::Not),
            Some(Tok::Punct("!")) => Some(Un::LogNot),
            Some(Tok::Punct("*")) => Some(Un::Deref),
            Some(Tok::Punct("&")) => Some(Un::Addr),
            _ => None,
        };
        let out = if let Some(op) = op {
            self.at += 1;
            Ast::Un(op, Box::new(self.unary()?))
        } else if let Some(Tok::Punct(p @ ("++" | "--"))) = self.peek() {
            let up = *p == "++";
            self.at += 1;
            Ast::Step(true, up, Box::new(self.unary()?))
        } else if matches!(self.peek(), Some(Tok::Punct("("))) && self.at_cast() {
            self.at += 1;
            let ty = read_type(self.toks, &mut self.at, self.word).ok_or("a cast to no type")?;
            self.expect(")")?;
            Ast::Cast(ty, Box::new(self.unary()?))
        } else {
            self.postfix()?
        };
        self.depth -= 1;
        Ok(out)
    }

    /// Reads a primary expression and the calls, indexes, fields and steps
    /// after it.
    ///
    /// # Errors
    ///
    /// When the tokens do not read as one.
    fn postfix(&mut self) -> Result<Ast, String> {
        let first = self.toks.get(self.at).cloned();
        self.at += 1;
        let mut e = match first {
            Some(Tok::Int(v, ty)) => Ast::Int(v, ty),
            Some(Tok::Float(v, ty)) => Ast::Float(v, ty),
            Some(Tok::Str(s)) => Ast::Str(s),
            Some(Tok::Name(n)) => Ast::Name(n),
            Some(Tok::Punct("(")) => {
                let inner = self.assign()?;
                self.expect(")")?;
                inner
            }
            _ => {
                self.at -= 1;
                return Err(format!("expected a value, read {}", self.shown()));
            }
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
                        self.expect(",")?;
                    }
                }
                e = Ast::Call(Box::new(e), args);
            } else if self.eat("[") {
                let i = self.assign()?;
                self.expect("]")?;
                e = Ast::Index(Box::new(e), Box::new(i));
            } else if self.eat("->") {
                let Some(Tok::Name(field)) = self.peek().cloned() else {
                    return Err(format!("expected a field, read {}", self.shown()));
                };
                self.at += 1;
                e = Ast::Arrow(Box::new(e), field);
            } else if self.eat(".") {
                let (Some(Tok::Name(member)), Ast::Arrow(base, field)) = (self.peek().cloned(), e)
                else {
                    return Err("a member of something that is no field".to_owned());
                };
                self.at += 1;
                e = Ast::Arrow(base, format!("{field}.{member}"));
            } else if let Some(Tok::Punct(p @ ("++" | "--"))) = self.peek() {
                let up = *p == "++";
                self.at += 1;
                e = Ast::Step(false, up, Box::new(e));
            } else {
                break;
            }
        }
        Ok(e)
    }
}

/// Reads an expression that is all of `toks`.
///
/// # Arguments
///
/// * `toks` - The tokens.
/// * `is_value` - Tells whether a name holds a value, which a parenthesized
///   name is then no cast to.
/// * `word` - The machine word in bits.
///
/// # Errors
///
/// When the tokens do not read as one expression.
pub(super) fn expression(
    toks: &[Tok],
    is_value: &dyn Fn(&str) -> bool,
    word: u8,
) -> Result<Ast, String> {
    let mut p = Parser {
        toks,
        at: 0,
        is_value,
        word,
        depth: 0,
    };
    let e = p.assign()?;
    if p.at < toks.len() {
        return Err(format!("expected the end, read {}", p.shown()));
    }
    Ok(e)
}

/// The bits of a floating value as the type stores them.
///
/// # Arguments
///
/// * `v` - The value.
/// * `bits` - 32 or 64.
#[expect(
    clippy::cast_possible_truncation,
    reason = "rounding a double to a single is the conversion a float type makes"
)]
pub(super) fn float_bits(v: f64, bits: u8) -> u64 {
    if bits == 32 {
        u64::from((v as f32).to_bits())
    } else {
        v.to_bits()
    }
}

/// The floating value a type's bits hold.
///
/// # Arguments
///
/// * `v` - The bits.
/// * `bits` - 32 or 64.
pub(super) fn float_of(v: u64, bits: u8) -> f64 {
    if bits == 32 {
        f64::from(f32::from_bits(lo32(v)))
    } else {
        f64::from_bits(v)
    }
}

#[cfg(test)]
mod tests {
    use super::{Ast, Base, Bin, CTy, Tok, Un, expression, leading_type, tokens};

    /// Reads one expression with every name a value.
    ///
    /// # Panics
    ///
    /// When the text does not read.
    fn read(text: &str) -> Ast {
        expression(&tokens(text).unwrap(), &|_| true, 64).unwrap()
    }

    /// Literals take the type C gives them, strings carry their terminator,
    /// and a `Class::method` is one name.
    ///
    /// # Panics
    ///
    /// When a token reads as another.
    #[test]
    fn literals_and_names_read_as_c_reads_them() {
        let toks = tokens("0xffffffff 5 0x1'A' L\"ab\" 1.5f Foo::Bar /* c */ x").unwrap();
        assert_eq!(toks[0], Tok::Int(0xffff_ffff, CTy::int(32, false)));
        assert_eq!(toks[1], Tok::Int(5, CTy::int(32, true)));
        assert_eq!(toks[2], Tok::Int(1, CTy::int(32, true)));
        assert_eq!(toks[3], Tok::Int(0x41, CTy::int(32, true)));
        assert_eq!(toks[4], Tok::Str(vec![b'a', 0, b'b', 0, 0, 0]));
        assert_eq!(toks[5], Tok::Float(1.5, CTy::of(Base::Float(32))));
        assert_eq!(toks[6], Tok::Name("Foo::Bar".to_owned()));
        assert_eq!(toks[7], Tok::Name("x".to_owned()));
        assert_eq!(toks.len(), 8);
        assert_eq!(
            tokens("operator delete(p)").unwrap()[0],
            Tok::Name("operator delete".to_owned())
        );
    }

    /// Precedence, casts and postfix forms read as C reads them.
    ///
    /// # Panics
    ///
    /// When an expression nests otherwise than C nests it.
    #[test]
    fn expressions_read_at_c_precedence() {
        let e = read("a + b * c << 2 == d");
        let Ast::Bin(Bin::Eq, l, _) = e else {
            panic!("{e:?}")
        };
        let Ast::Bin(Bin::Shl, sum, _) = *l else {
            panic!("{l:?}")
        };
        assert!(matches!(*sum, Ast::Bin(Bin::Add, _, _)), "{sum:?}");
        let cast =
            expression(&tokens("*(uint32_t*)(a1 + 4)").unwrap(), &|n| n == "a1", 64).unwrap();
        let Ast::Un(Un::Deref, inner) = cast else {
            panic!("{cast:?}")
        };
        assert!(
            matches!(
                *inner,
                Ast::Cast(
                    CTy {
                        base: Base::Int(32, false),
                        ptr: 1
                    },
                    _
                )
            ),
            "{inner:?}"
        );
        assert!(matches!(read("x ?: y"), Ast::Pick(_, None, _)));
        assert!(matches!(read("a->field_0x8"), Ast::Arrow(_, _)));
        assert!(matches!(read("f()->NtTib.Self"), Ast::Arrow(_, ref m) if m == "NtTib.Self"));
        assert!(matches!(read("f(a, b)[2]"), Ast::Index(_, _)));
        assert!(matches!(read("x = y += 1"), Ast::Assign(None, _, _)));
    }

    /// A declaration's type is read off its front, its pointers left to the
    /// names they belong to.
    ///
    /// # Panics
    ///
    /// When the type or its length reads otherwise.
    #[test]
    fn a_declaration_type_leaves_its_pointers() {
        let toks = tokens("uint8_t *p, q;").unwrap();
        let (ty, used) = leading_type(&toks, 64).unwrap();
        assert_eq!(ty, CTy::int(8, false));
        assert_eq!(toks[used], Tok::Punct("*"));
        assert!(expression(&tokens("a +").unwrap(), &|_| true, 64).is_err());
    }
}
