//! The search spec: one line naming what to find, where, and how the
//! clauses combine.
//!
//! ```text
//! spec   := find (' ' op ' ' clause)*       left to right, no grouping
//! op     := and | or | minus                by hit address
//! clause := find | in=<place>               in= only after and or minus
//! find   := bytes:<masked pattern>          48 8b 4? ?8 ??
//!         | text:<text>                     ASCII case folded, UTF-8 and UTF-16LE
//!         | value:<n>[..<n>][,option]...    data words and instruction constants
//! option := width=1|2|4|8 | order=le|be | signed | align=<2^k> | disp
//! place  := <section> | <lo>..<hi> | <function>   ranges include both ends
//! ```
//!
//! A text can hold no lone `and`, `or` or `minus` word, which would end
//! it; the search tool finds such a text.

use super::{Lane, masked_at, words};

/// Most bytes one spec holds.
pub const SPEC_MAX: usize = 4096;

/// Most clauses one spec combines: each finds over the whole file.
pub const CLAUSES_MAX: usize = 8;

/// Largest alignment a value search takes, in bytes.
const ALIGN_MAX: u64 = 4096;

/// A parsed search spec.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Spec {
    /// The first clause: always a find.
    pub first: Find,
    /// Each later clause with the operation joining it to what came before.
    pub rest: Vec<(Op, Clause)>,
}

impl Spec {
    /// Returns the spec's finds in order, its places left out.
    pub fn finds(&self) -> impl Iterator<Item = &Find> {
        std::iter::once(&self.first).chain(self.rest.iter().filter_map(|(_, c)| match c {
            Clause::Find(f) => Some(f),
            Clause::In(_) => None,
        }))
    }
}

/// How a clause joins the hits before it, by hit address.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Op {
    /// Keeps the hits whose address the clause also names.
    And,
    /// Adds the clause's hits at addresses not yet hit; a hit already
    /// there keeps its match.
    Or,
    /// Drops the hits whose address the clause names.
    Minus,
}

/// One clause after an operation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Clause {
    /// A search of its own.
    Find(Find),
    /// A place, as written: a section's name, `<lo>..<hi>`, or a function.
    In(String),
}

/// One search.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Find {
    /// A masked byte pattern.
    Bytes(Vec<Lane>),
    /// A text, ASCII case folded, as UTF-8 and as UTF-16LE.
    Text(String),
    /// A value or a range of values.
    Value(Value),
}

/// A value search: the numbers sought and how a word spells them.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Value {
    /// The smallest number sought.
    pub lo: i128,
    /// The largest number sought; at least `lo`.
    pub hi: i128,
    /// Bytes of a data word: 1, 2, 4 or 8; both bounds fit it.
    pub width: u8,
    /// The byte order of a data word.
    pub order: Order,
    /// Whether a word or an operand is read as signed.
    pub sign: Sign,
    /// The alignment of a data word's address, a power of two in bytes.
    pub align: u64,
    /// Whether memory displacements are searched beside immediates.
    pub disp: Disp,
}

/// The byte order of a data word.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Order {
    /// Least significant byte first, every loaded instruction set's.
    Le,
    /// Most significant byte first.
    Be,
}

/// How a word or an operand is read as a number.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Sign {
    /// Zero-extended.
    Unsigned,
    /// Two's complement at its width.
    Signed,
}

/// Whether a value search reads memory displacements.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Disp {
    /// Immediates only.
    Skipped,
    /// Immediates and displacements.
    Searched,
}

/// Parses a search spec.
///
/// # Arguments
///
/// * `text` - The spec ([`self`] gives the grammar).
///
/// # Returns
///
/// The spec, every clause read; places are resolved when it runs.
///
/// # Errors
///
/// When the spec is longer than [`SPEC_MAX`], combines more than
/// [`CLAUSES_MAX`] clauses, or a clause does not read, naming the 1-based
/// column and the form expected there.
pub fn parse(text: &str) -> Result<Spec, String> {
    if text.len() > SPEC_MAX {
        return Err(format!(
            "the spec holds {} bytes, more than the {SPEC_MAX} a search spec may",
            text.len()
        ));
    }
    let mut clauses: Vec<(Option<Op>, usize, usize)> = Vec::new();
    let (mut op, mut start, mut end) = (None, None, 0);
    for (at, word) in words(text) {
        let joins = match word {
            "and" => Some(Op::And),
            "or" => Some(Op::Or),
            "minus" => Some(Op::Minus),
            _ => None,
        };
        let Some(joins) = joins else {
            start = start.or(Some(at));
            end = at.saturating_add(word.len());
            continue;
        };
        let Some(from) = start.take() else {
            return Err(format!(
                "column {}: {word} needs a clause before it",
                col(at)
            ));
        };
        clauses.push((op, from, end));
        op = Some(joins);
    }
    match start {
        Some(from) => clauses.push((op, from, end)),
        None if op.is_some() => {
            return Err("the spec ends after an operation: a clause must follow it".to_owned());
        }
        None => return Err(format!("the spec is empty; {FORMS}")),
    }
    if clauses.len() > CLAUSES_MAX {
        return Err(format!(
            "the spec combines {} clauses, more than the {CLAUSES_MAX} a search may",
            clauses.len()
        ));
    }
    let mut read = clauses.into_iter().map(|(op, from, to)| {
        let body = text.get(from..to).unwrap_or_default();
        Ok((op, clause(body, from, op)?))
    });
    let Some(first) = read.next().transpose()? else {
        return Err(format!("the spec is empty; {FORMS}"));
    };
    let (None, Clause::Find(first)) = first else {
        return Err(format!("column 1: in= narrows hits; {FORMS}"));
    };
    let rest = read
        .map(|r| r.and_then(|(op, c)| Ok((op.ok_or("a clause lost its operation")?, c))))
        .collect::<Result<_, String>>()?;
    Ok(Spec { first, rest })
}

/// The forms a clause takes, for a refusal.
const FORMS: &str = "a clause is bytes:<hex bytes>, text:<text> or value:<n>[..<n>], and in=<place> after and or minus";

/// Returns a byte offset as the 1-based column a refusal names.
///
/// # Arguments
///
/// * `at` - The byte offset in the spec.
fn col(at: usize) -> usize {
    at.saturating_add(1)
}

/// Parses one clause.
///
/// # Arguments
///
/// * `body` - The clause's text, trimmed.
/// * `at` - Its byte offset in the spec.
/// * `op` - The operation before it; `None` for the first.
///
/// # Errors
///
/// When the clause does not read, at its column.
fn clause(body: &str, at: usize, op: Option<Op>) -> Result<Clause, String> {
    if let Some(place) = body.strip_prefix("in=") {
        return match op {
            Some(Op::And | Op::Minus) if !place.is_empty() => Ok(Clause::In(place.to_owned())),
            Some(Op::And | Op::Minus) => Err(format!(
                "column {}: in= names no place; write a section, <lo>..<hi> or a function",
                col(at)
            )),
            None | Some(Op::Or) => Err(format!(
                "column {}: in= narrows the hits before it, so it follows and or minus",
                col(at)
            )),
        };
    }
    let (mode, rest) = body.split_once(':').unwrap_or((body, ""));
    let from = at.saturating_add(mode.len()).saturating_add(1);
    match mode {
        "bytes" => Ok(Clause::Find(Find::Bytes(masked_at(rest, from)?))),
        "text" if !rest.is_empty() => Ok(Clause::Find(Find::Text(rest.to_owned()))),
        "text" => Err(format!("column {}: text: names no text", col(from))),
        "value" => Ok(Clause::Find(Find::Value(value(rest, from)?))),
        _ => Err(format!(
            "column {}: {} is no clause; {FORMS}",
            col(at),
            crate::text::quoted(mode)
        )),
    }
}

/// Parses a value clause's body: the number or range, then its options.
///
/// # Arguments
///
/// * `body` - The text after `value:`.
/// * `at` - Its byte offset in the spec.
///
/// # Errors
///
/// When a number, a range or an option does not read, or the numbers do
/// not fit the width, at its column.
fn value(body: &str, at: usize) -> Result<Value, String> {
    let mut pieces = Vec::new();
    let mut from = at;
    for piece in body.split(',') {
        pieces.push((from, piece));
        from = from.saturating_add(piece.len()).saturating_add(1);
    }
    let Some(&(at, range)) = pieces.first() else {
        return Err(format!("column {}: value: names no number", col(at)));
    };
    let (lo, hi) = range.split_once("..").unwrap_or((range, range));
    let hi_at = at.saturating_add(range.len() - hi.len());
    let (lo, hi) = (number(lo, at)?, number(hi, hi_at)?);
    if lo > hi {
        return Err(format!(
            "column {}: the range ends below its start",
            col(at)
        ));
    }
    let mut asked = Value {
        lo,
        hi,
        width: 0,
        order: Order::Le,
        sign: Sign::Unsigned,
        align: 0,
        disp: Disp::Skipped,
    };
    for &(at, option) in pieces.get(1..).unwrap_or_default() {
        set(&mut asked, option, at)?;
    }
    if lo < 0 && asked.sign == Sign::Unsigned {
        return Err(format!("column {}: a negative value needs signed", col(at)));
    }
    let fits = |w: u8| fits(lo, w, asked.sign) && fits(hi, w, asked.sign);
    if asked.width == 0 {
        asked.width = [1, 2, 4, 8]
            .into_iter()
            .find(|&w| fits(w))
            .ok_or_else(|| format!("column {}: the value does not fit 8 bytes", col(at)))?;
    } else if !fits(asked.width) {
        return Err(format!(
            "column {}: the value does not fit width={}",
            col(at),
            asked.width
        ));
    }
    if asked.align == 0 {
        asked.align = u64::from(asked.width);
    }
    Ok(asked)
}

/// Sets one option of a value clause.
///
/// # Arguments
///
/// * `asked` - The clause read so far.
/// * `option` - The option's text.
/// * `at` - Its byte offset in the spec.
///
/// # Errors
///
/// When the option is unknown or its value does not read, at its column.
fn set(asked: &mut Value, option: &str, at: usize) -> Result<(), String> {
    match option.split_once('=').unwrap_or((option, "")) {
        ("width", w) => {
            asked.width = match w {
                "1" => 1,
                "2" => 2,
                "4" => 4,
                "8" => 8,
                _ => return Err(format!("column {}: width is 1, 2, 4 or 8", col(at))),
            };
        }
        ("order", "le") => asked.order = Order::Le,
        ("order", "be") => asked.order = Order::Be,
        ("order", _) => return Err(format!("column {}: order is le or be", col(at))),
        ("signed", "") => asked.sign = Sign::Signed,
        ("disp", "") => asked.disp = Disp::Searched,
        ("align", n) => {
            asked.align = number(n, at.saturating_add(6))
                .ok()
                .and_then(|n| u64::try_from(n).ok())
                .filter(|n| n.is_power_of_two() && *n <= ALIGN_MAX)
                .ok_or_else(|| {
                    format!(
                        "column {}: align is a power of two up to {ALIGN_MAX}",
                        col(at)
                    )
                })?;
        }
        _ => {
            return Err(format!(
                "column {}: {} is no value option; the options are width=1|2|4|8, order=le|be, signed, align=<n> and disp",
                col(at),
                crate::text::quoted(option)
            ));
        }
    }
    Ok(())
}

/// Reads a number: 0x-hex or decimal, with an optional leading `-`.
///
/// # Arguments
///
/// * `text` - The number.
/// * `at` - Its byte offset in the spec.
///
/// # Errors
///
/// When the text is not a number of at most 64 bits, at its column.
fn number(text: &str, at: usize) -> Result<i128, String> {
    let (neg, digits) = text
        .strip_prefix('-')
        .map_or((false, text), |rest| (true, rest));
    let magnitude = match digits
        .strip_prefix("0x")
        .or_else(|| digits.strip_prefix("0X"))
    {
        Some(hex) if hex.bytes().all(|b| b.is_ascii_hexdigit()) => {
            u64::from_str_radix(hex, 16).ok()
        }
        Some(_) => None,
        None if digits.bytes().all(|b| b.is_ascii_digit()) => digits.parse::<u64>().ok(),
        None => None,
    };
    let magnitude = magnitude.ok_or_else(|| {
        format!(
            "column {}: {} is not a number of at most 64 bits; write 0x-hex or decimal, - before a negative one",
            col(at),
            crate::text::quoted(text)
        )
    })?;
    Ok(if neg {
        -i128::from(magnitude)
    } else {
        i128::from(magnitude)
    })
}

/// Whether a number fits a word of `width` bytes read with `sign`.
///
/// # Arguments
///
/// * `n` - The number.
/// * `width` - The word's bytes: 1 to 8.
/// * `sign` - How the word is read.
pub(crate) fn fits(n: i128, width: u8, sign: Sign) -> bool {
    let bits = u32::from(width) * 8;
    match sign {
        Sign::Unsigned => (0..1i128 << bits).contains(&n),
        Sign::Signed => (-(1i128 << (bits - 1))..1i128 << (bits - 1)).contains(&n),
    }
}
