//! The search spec: one line naming what to find, where, and how the
//! clauses combine.
//!
//! ```text
//! spec   := find (' ' step)*                left to right, no grouping
//! step   := and <clause> | or <find> | minus <clause>    by hit address
//! clause := find | in=<place>               a place narrows what came before
//! find   := bytes:<masked pattern>          48 8b 4? ?8 ??
//!         | text:<text> | text:"<text>"     ASCII case folded, UTF-8 and UTF-16LE
//!         | value:<n>[..<n>][,option]...    data words and instruction constants
//! option := width=1|2|4|8 | order=le|be | signed | align=<2^k> | disp
//! place  := <section> | <lo>..<hi> | <function>   ranges include both ends
//! ```
//!
//! An unquoted text ends at a lone `and`, `or` or `minus` word; a quoted
//! one holds them, `""` standing for a quote inside it. A column a refusal
//! names counts characters from 1.

use super::{Pattern, column, masked_at};

/// Most bytes one spec holds.
pub const SPEC_MAX: usize = 4096;

/// Most clauses one spec combines: each finds over the whole file.
pub const CLAUSES_MAX: usize = 8;

/// Largest alignment a value search takes, in bytes.
const ALIGN_MAX: u64 = 4096;

/// A refusal at a byte offset of the spec, turned into its column by
/// [`parse`].
type Fault = (usize, String);

/// A parsed search spec.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Spec {
    /// The first clause: always a find.
    pub(super) first: Find,
    /// Each later clause with how it joins what came before.
    pub(super) steps: Vec<Step>,
}

impl Spec {
    /// Returns a spec of one find and no steps.
    ///
    /// # Arguments
    ///
    /// * `find` - The find.
    #[must_use]
    pub fn of(find: Find) -> Self {
        Spec {
            first: find,
            steps: Vec::new(),
        }
    }

    /// Returns the spec's finds in order, its places left out.
    pub fn finds(&self) -> impl Iterator<Item = &Find> {
        std::iter::once(&self.first).chain(self.steps.iter().filter_map(Step::find))
    }
}

/// One step after the first find, joining a clause to the hits before it
/// by address.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Step {
    /// Keeps the hits whose address the clause also names.
    And(Clause),
    /// Adds the find's hits at addresses not yet hit; a hit already there
    /// keeps its match.
    Or(Find),
    /// Drops the hits whose address the clause names.
    Minus(Clause),
}

impl Step {
    /// Returns the step's find, `None` for a place.
    fn find(&self) -> Option<&Find> {
        match self {
            Step::And(Clause::Find(f)) | Step::Minus(Clause::Find(f)) | Step::Or(f) => Some(f),
            Step::And(Clause::In(_)) | Step::Minus(Clause::In(_)) => None,
        }
    }
}

/// What an `and` or a `minus` joins.
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
    Bytes(Pattern),
    /// A text, ASCII case folded, as UTF-8 and as UTF-16LE.
    Text(Text),
    /// A value or a range of values.
    Value(Value),
}

/// A text a search finds: never empty.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Text(String);

impl Text {
    /// Returns the text to find.
    ///
    /// # Arguments
    ///
    /// * `text` - The text.
    ///
    /// # Returns
    ///
    /// The text, or `None` for an empty one.
    #[must_use]
    pub fn new(text: &str) -> Option<Self> {
        (!text.is_empty()).then(|| Text(text.to_owned()))
    }

    /// Returns the text.
    #[must_use]
    pub fn as_str(&self) -> &str {
        &self.0
    }
}

/// The bytes of a data word.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Width {
    /// One byte.
    One,
    /// Two bytes.
    Two,
    /// Four bytes.
    Four,
    /// Eight bytes.
    Eight,
}

impl Width {
    /// Every width, smallest first.
    const ALL: [Width; 4] = [Width::One, Width::Two, Width::Four, Width::Eight];

    /// Returns the width in bytes.
    #[must_use]
    pub fn bytes(self) -> u8 {
        match self {
            Width::One => 1,
            Width::Two => 2,
            Width::Four => 4,
            Width::Eight => 8,
        }
    }
}

/// A value search: the numbers sought and how a word spells them.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Value {
    /// The smallest number sought.
    pub(super) lo: i128,
    /// The largest number sought; at least `lo`.
    pub(super) hi: i128,
    /// The width of a data word; both bounds fit it.
    pub(super) width: Width,
    /// The byte order of a data word; `None` for the program's.
    pub(super) order: Option<Order>,
    /// Whether a word or an operand is read as signed.
    pub(super) sign: Sign,
    /// The alignment of a data word's address, a power of two in bytes.
    pub(super) align: u64,
    /// Whether memory displacements are searched beside immediates.
    pub(super) disp: Disp,
}

impl Value {
    /// Returns the byte order a data word is read in: the one asked, else
    /// the program's own.
    ///
    /// # Arguments
    ///
    /// * `program` - The program's byte order.
    #[must_use]
    pub fn order(&self, program: Order) -> Order {
        self.order.unwrap_or(program)
    }
}

/// The byte order of a data word.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Order {
    /// Least significant byte first.
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
/// [`CLAUSES_MAX`] clauses, or a clause does not read, naming the column
/// and the form expected there.
pub fn parse(text: &str) -> Result<Spec, String> {
    if text.len() > SPEC_MAX {
        return Err(format!(
            "the spec holds {} bytes, more than the {SPEC_MAX} a search spec may",
            text.len()
        ));
    }
    read(text).map_err(|(at, why)| format!("column {}: {why}", column(text, at)))
}

/// The forms a clause takes, for a refusal.
const FORMS: &str = "a clause is bytes:<hex bytes>, text:<text> or value:<n>[..<n>], and in=<place> after and or minus";

/// Reads a spec no longer than [`SPEC_MAX`].
///
/// # Arguments
///
/// * `text` - The spec.
///
/// # Returns
///
/// The spec.
///
/// # Errors
///
/// When it does not read, at the byte offset of the fault.
fn read(text: &str) -> Result<Spec, Fault> {
    let mut clauses: Vec<(Option<&str>, usize, usize)> = Vec::new();
    let (mut joins, mut start, mut end) = (None, None, 0);
    for (at, word) in spec_words(text)? {
        if !matches!(word, "and" | "or" | "minus") {
            start = start.or(Some(at));
            end = at.saturating_add(word.len());
            continue;
        }
        let Some(from) = start.take() else {
            return Err((at, format!("{word} needs a clause before it")));
        };
        clauses.push((joins, from, end));
        joins = Some(word);
    }
    match start {
        Some(from) => clauses.push((joins, from, end)),
        None if joins.is_some() => {
            return Err((
                text.len(),
                "the spec ends after an operation: a clause must follow it".to_owned(),
            ));
        }
        None => {}
    }
    if clauses.len() > CLAUSES_MAX {
        return Err((
            0,
            format!(
                "the spec combines {} clauses, more than the {CLAUSES_MAX} a search may",
                clauses.len()
            ),
        ));
    }
    let mut first = None;
    let mut steps = Vec::new();
    for (joins, from, to) in clauses {
        let body = text.get(from..to).unwrap_or_default();
        let clause = clause(body, from)?;
        match (joins, clause) {
            (None, Clause::Find(f)) => first = Some(f),
            (None, Clause::In(_)) => {
                return Err((from, format!("in= narrows the hits before it; {FORMS}")));
            }
            (Some("or"), Clause::Find(f)) => steps.push(Step::Or(f)),
            (Some("or"), Clause::In(_)) => {
                return Err((from, "in= follows and or minus, never or".to_owned()));
            }
            (Some("minus"), c) => steps.push(Step::Minus(c)),
            (Some(_), c) => steps.push(Step::And(c)),
        }
    }
    let first = first.ok_or((0, format!("the spec is empty; {FORMS}")))?;
    Ok(Spec { first, steps })
}

/// Splits a spec into words, a quoted text (`text:"..."`) one word with
/// its spaces.
///
/// # Arguments
///
/// * `text` - The spec.
///
/// # Returns
///
/// Each word with its byte offset.
///
/// # Errors
///
/// When a quoted text is not closed, or something follows its closing
/// quote in the same word.
fn spec_words(text: &str) -> Result<Vec<(usize, &str)>, Fault> {
    let mut out = Vec::new();
    let mut at = 0;
    while let Some(rest) = text.get(at..) {
        let Some(skip) = rest.find(|c: char| !c.is_whitespace()) else {
            break;
        };
        let start = at.saturating_add(skip);
        let word = text.get(start..).unwrap_or_default();
        let len = if let Some(quoted) = word.strip_prefix("text:\"") {
            let close = closing_quote(quoted).ok_or((
                start,
                "the quoted text is not closed; write \"\" for a quote inside it".to_owned(),
            ))?;
            let len = "text:\"".len().saturating_add(close).saturating_add(1);
            if word
                .get(len..)
                .and_then(|t| t.chars().next())
                .is_some_and(|c| !c.is_whitespace())
            {
                return Err((
                    start.saturating_add(len),
                    "a quoted text ends its clause; put a space and an operation after it"
                        .to_owned(),
                ));
            }
            len
        } else {
            word.find(char::is_whitespace).unwrap_or(word.len())
        };
        out.push((start, word.get(..len).unwrap_or_default()));
        at = start.saturating_add(len);
    }
    Ok(out)
}

/// Returns where a quoted text's closing quote is: the first quote not
/// doubled.
///
/// # Arguments
///
/// * `quoted` - The text after the opening quote.
///
/// # Returns
///
/// The byte offset of the closing quote, `None` when there is none.
fn closing_quote(quoted: &str) -> Option<usize> {
    let bytes = quoted.as_bytes();
    let mut i = 0;
    while i < bytes.len() {
        if bytes[i] == b'"' {
            if bytes.get(i + 1) != Some(&b'"') {
                return Some(i);
            }
            i += 1;
        }
        i += 1;
    }
    None
}

/// Parses one clause.
///
/// # Arguments
///
/// * `body` - The clause's text, trimmed.
/// * `at` - Its byte offset in the spec.
///
/// # Returns
///
/// The clause.
///
/// # Errors
///
/// When the clause does not read, at its byte offset.
fn clause(body: &str, at: usize) -> Result<Clause, Fault> {
    if let Some(place) = body.strip_prefix("in=") {
        if place.is_empty() {
            return Err((
                at,
                "in= names no place; write a section, <lo>..<hi> or a function".to_owned(),
            ));
        }
        return Ok(Clause::In(place.to_owned()));
    }
    let (mode, rest) = body.split_once(':').unwrap_or((body, ""));
    let from = at.saturating_add(mode.len()).saturating_add(1);
    let text = match rest.strip_prefix('"').and_then(|q| q.strip_suffix('"')) {
        Some(inner) if mode == "text" => inner.replace("\"\"", "\""),
        _ => rest.to_owned(),
    };
    match mode {
        "bytes" => Ok(Clause::Find(Find::Bytes(masked_at(rest, from)?))),
        "text" => Text::new(&text)
            .map(|t| Clause::Find(Find::Text(t)))
            .ok_or((from, "text: names no text".to_owned())),
        "value" => Ok(Clause::Find(Find::Value(value(rest, from)?))),
        _ => Err((
            at,
            format!("{} is no clause; {FORMS}", crate::text::quoted(mode)),
        )),
    }
}

/// The options a value clause has read so far.
#[derive(Debug, Default)]
struct Options {
    /// `width=`, when given.
    width: Option<Width>,
    /// `order=`, when given.
    order: Option<Order>,
    /// Whether `signed` was given.
    signed: bool,
    /// `align=`, when given.
    align: Option<u64>,
    /// Whether `disp` was given.
    disp: bool,
}

/// Parses a value clause's body: the number or range, then its options.
///
/// # Arguments
///
/// * `body` - The text after `value:`.
/// * `at` - Its byte offset in the spec.
///
/// # Returns
///
/// The value.
///
/// # Errors
///
/// When a number, a range or an option does not read, or the numbers do
/// not fit the width, at its byte offset.
fn value(body: &str, at: usize) -> Result<Value, Fault> {
    let mut pieces = body.split(',');
    let range = pieces.next().unwrap_or_default();
    let (lo_text, hi_text) = range.split_once("..").unwrap_or((range, range));
    let hi_at = at.saturating_add(range.len().saturating_sub(hi_text.len()));
    let (lo, hi) = (number(lo_text, at)?, number(hi_text, hi_at)?);
    if lo > hi {
        return Err((at, "the range ends below its start".to_owned()));
    }
    let mut asked = Options::default();
    let mut from = at.saturating_add(range.len()).saturating_add(1);
    for option in pieces {
        set(&mut asked, option, from)?;
        from = from.saturating_add(option.len()).saturating_add(1);
    }
    let sign = if asked.signed {
        Sign::Signed
    } else {
        Sign::Unsigned
    };
    if lo < 0 && sign == Sign::Unsigned {
        return Err((at, "a negative value needs signed".to_owned()));
    }
    let fits = |w: Width| fits(lo, w, sign) && fits(hi, w, sign);
    let width = match asked.width {
        Some(w) if fits(w) => w,
        Some(w) => {
            return Err((at, format!("the value does not fit width={}", w.bytes())));
        }
        None => Width::ALL
            .into_iter()
            .find(|&w| fits(w))
            .ok_or((at, "the value does not fit 8 bytes".to_owned()))?,
    };
    Ok(Value {
        lo,
        hi,
        width,
        order: asked.order,
        sign,
        align: asked.align.unwrap_or_else(|| u64::from(width.bytes())),
        disp: if asked.disp {
            Disp::Searched
        } else {
            Disp::Skipped
        },
    })
}

/// Sets one option of a value clause.
///
/// # Arguments
///
/// * `asked` - The options read so far.
/// * `option` - The option's text.
/// * `at` - Its byte offset in the spec.
///
/// # Errors
///
/// When the option is unknown or its value does not read, at its byte
/// offset.
fn set(asked: &mut Options, option: &str, at: usize) -> Result<(), Fault> {
    match option.split_once('=').unwrap_or((option, "")) {
        ("width", w) => {
            let width = Width::ALL.into_iter().find(|x| x.bytes().to_string() == w);
            asked.width = Some(width.ok_or((at, "width is 1, 2, 4 or 8".to_owned()))?);
        }
        ("order", "le") => asked.order = Some(Order::Le),
        ("order", "be") => asked.order = Some(Order::Be),
        ("order", _) => return Err((at, "order is le or be".to_owned())),
        ("signed", "") => asked.signed = true,
        ("disp", "") => asked.disp = true,
        ("align", n) => {
            let align = number(n, at.saturating_add(6))
                .ok()
                .and_then(|n| u64::try_from(n).ok())
                .filter(|n| n.is_power_of_two() && *n <= ALIGN_MAX);
            asked.align =
                Some(align.ok_or((at, format!("align is a power of two up to {ALIGN_MAX}")))?);
        }
        _ => {
            return Err((
                at,
                format!(
                    "{} is no value option; the options, joined by commas, are width=1|2|4|8, order=le|be, signed, align=<n> and disp",
                    crate::text::quoted(option)
                ),
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
/// # Returns
///
/// The number.
///
/// # Errors
///
/// When the text is not a number of at most 64 bits, at its byte offset.
fn number(text: &str, at: usize) -> Result<i128, Fault> {
    crate::text::number(text).ok_or_else(|| {
        (
            at,
            format!(
                "{} is not a number of at most 64 bits; write 0x-hex or decimal, - before a negative one",
                crate::text::quoted(text)
            ),
        )
    })
}

/// Whether a number fits a word of `width` read with `sign`.
///
/// # Arguments
///
/// * `n` - The number.
/// * `width` - The word's width.
/// * `sign` - How the word is read.
fn fits(n: i128, width: Width, sign: Sign) -> bool {
    let bits = u32::from(width.bytes()) * 8;
    match sign {
        Sign::Unsigned => (0..1i128 << bits).contains(&n),
        Sign::Signed => (-(1i128 << (bits - 1))..1i128 << (bits - 1)).contains(&n),
    }
}
