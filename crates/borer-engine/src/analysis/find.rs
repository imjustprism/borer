//! One search over every name table the engine holds: what a person types
//! into a find box, parsed once at the boundary, matched against each table
//! in one pass and ranked into one list.
//!
//! Each hit says how borer knows it ([`Source`]), from facts the tables
//! already carry. Not searched here: the pseudo-C text, immediate values
//! and expressions.

use std::borrow::Cow;
use std::cmp::Ordering;
use std::fmt::Write as _;

use super::render::{FunctionRow, RowSource, symbol_addr, symbol_module};
use super::{Analysis, Function, Overlay, bare_name, edit::open_question, name_of, resolve};
use crate::fileinfo::Place;
use crate::program::{Program, Symbol, SymbolKind};
use crate::search::demangled_or_raw;
use crate::strings::Encoding;
use crate::strings::walk::{Needle, walks};
use crate::text::one_line;

/// Most characters of a query's needle; the rest is cut before it is
/// lowered, so a pasted megabyte costs no more than a word.
pub const NEEDLE_MAX: usize = 256;

/// Which tables a query searches, from its kind prefix.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Scope {
    /// No prefix: every table, and first the place the text spells as an
    /// address, if it spells one: `0x`-hex, `rva:<n>`, `off:<n>`, or a bare
    /// number of decimal digits alone, where `borer://addr` also reads bare
    /// hex.
    All(Option<Place>),
    /// `@`: the discovered functions.
    Functions,
    /// `"`: the strings.
    Strings,
    /// `t:`: the user and debug types and the recovered classes.
    Types,
    /// `#`: the user's names and comments.
    Notes,
}

/// A find query: the tables it searches and the needle.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Query {
    /// The tables searched.
    pub scope: Scope,
    /// The text sought, at most [`NEEDLE_MAX`] characters, lowered.
    pub needle: Needle,
    /// The text was longer than [`NEEDLE_MAX`] characters and was cut, so
    /// no hit is known to match it whole.
    pub cut: bool,
}

impl Query {
    /// Returns the query `text` spells.
    ///
    /// A kind prefix (`@`, `"`, `t:`, `#`) narrows the tables; any other
    /// text searches them all, and an address form among it ([`Place`];
    /// a bare number only when it is decimal digits, so `add` or `beef` is
    /// a word) is answered first; text cut at [`NEEDLE_MAX`] spells none. A `"` query may close with a `"` too. A prefix the
    /// grammar lacks is plain text.
    ///
    /// # Arguments
    ///
    /// * `text` - The query as typed, of any length.
    #[must_use]
    pub fn parse(text: &str) -> Self {
        let text = text.trim();
        let (scope, rest) = if let Some(rest) = text.strip_prefix('@') {
            (Some(Scope::Functions), rest)
        } else if let Some(rest) = text.strip_prefix('"') {
            (Some(Scope::Strings), rest.strip_suffix('"').unwrap_or(rest))
        } else if let Some(rest) = text.strip_prefix("t:") {
            (Some(Scope::Types), rest)
        } else if let Some(rest) = text.strip_prefix('#') {
            (Some(Scope::Notes), rest)
        } else {
            (None, text)
        };
        let (rest, cut) = head(rest, NEEDLE_MAX);
        let decimal = rest.bytes().all(|b| b.is_ascii_digit());
        let place = Place::parse(rest).filter(|place| {
            !cut && match place {
                Place::Number(_) => decimal,
                Place::Va(_) | Place::Rva(_) | Place::Off(_) => true,
            }
        });
        Self {
            scope: scope.unwrap_or(Scope::All(place)),
            needle: Needle::new(rest),
            cut,
        }
    }
}

/// Returns the first `max` characters of `text` and whether any were left
/// out.
///
/// # Arguments
///
/// * `text` - The text cut.
/// * `max` - Most characters kept.
fn head(text: &str, max: usize) -> (&str, bool) {
    text.char_indices()
        .nth(max)
        .and_then(|(at, _)| text.get(..at))
        .map_or((text, false), |kept| (kept, true))
}

/// Most hits one kind keeps before the kinds are merged, so a table of a
/// hundred thousand matching strings leaves room for the rest.
///
/// The share holds only under a limit above it: with a limit of
/// `KIND_MAX` or fewer, the best-ranked kind can fill the whole list.
pub const KIND_MAX: usize = 50;

/// Most characters of a hit's text; a longer string or comment is cut and
/// ends in `...`.
pub const TEXT_MAX: usize = 200;

/// What a hit is, in the order hits of one rank are listed.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum HitKind {
    /// The place the query spelled as an address.
    Address,
    /// A discovered function, by the name in force.
    Function,
    /// An imported symbol.
    Import,
    /// An exported symbol, a forward among them.
    Export,
    /// Any other symbol: a local or a named datum.
    Symbol,
    /// A string the walk found.
    String,
    /// A user or debug type.
    Type,
    /// A recovered class.
    Class,
    /// A user's name for an address.
    Name,
    /// A user's comment.
    Comment,
}

impl HitKind {
    /// Returns the kind a symbol's hit is.
    ///
    /// # Arguments
    ///
    /// * `kind` - The symbol's kind.
    #[must_use]
    pub fn of_symbol(kind: SymbolKind) -> HitKind {
        match kind {
            SymbolKind::Import => HitKind::Import,
            SymbolKind::Export | SymbolKind::Forwarder => HitKind::Export,
            SymbolKind::Local | SymbolKind::Data => HitKind::Symbol,
        }
    }
}

/// How well a hit's text matches the needle, best first.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Rank {
    /// The whole text, in any case; never under a needle that was cut.
    Exact,
    /// The start of the text.
    Prefix,
    /// The start of a word in it: after a character that is neither a
    /// letter nor a digit, or at a lowercase-to-uppercase step.
    Word,
    /// Anywhere else, or in what the table matched beside the text shown
    /// (an import's module, a mangled name).
    Substring,
}

/// Where a type comes from.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TypeOrigin {
    /// The user stated it.
    User,
    /// The file's debug information states it.
    Debug,
}

/// How a class was recovered.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ClassOrigin {
    /// From the constructors storing its vtable.
    Vtable,
    /// From its type descriptor alone; no vtable is known.
    Descriptor,
}

/// What a user's comment records.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CommentKind {
    /// A finding.
    Finding,
    /// An open question ([`open_question`]).
    Question,
}

/// How borer knows a hit, which also says what the hit is
/// ([`Source::kind`]).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Source {
    /// The query spelled the address in this form.
    Address(Place),
    /// A function's name: the user's, or the analysis's from its source.
    Function(RowSource),
    /// The symbol table.
    Symbol {
        /// The symbol's kind.
        kind: SymbolKind,
        /// The module an import comes from.
        module: Option<Box<str>>,
    },
    /// The string walk.
    String {
        /// File offset of the first byte.
        off: u64,
        /// The section it loads in; `None` for bytes no section maps.
        section: Option<Box<str>>,
        /// The string's encoding.
        encoding: Encoding,
    },
    /// A type, from where it was stated.
    Type(TypeOrigin),
    /// A class, from how it was recovered.
    Class(ClassOrigin),
    /// The user named the address.
    User,
    /// The user commented the address.
    Comment(CommentKind),
}

impl Source {
    /// Returns what a hit known this way is.
    #[must_use]
    pub fn kind(&self) -> HitKind {
        match self {
            Source::Address(_) => HitKind::Address,
            Source::Function(_) => HitKind::Function,
            Source::Symbol { kind, .. } => HitKind::of_symbol(*kind),
            Source::String { .. } => HitKind::String,
            Source::Type(_) => HitKind::Type,
            Source::Class(_) => HitKind::Class,
            Source::User => HitKind::Name,
            Source::Comment(_) => HitKind::Comment,
        }
    }
}

/// One hit of a find.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Hit {
    /// Where it is; `None` for a type, an unbound import or an unmapped
    /// string.
    pub addr: Option<u64>,
    /// The text matched, at most [`TEXT_MAX`] characters and `...`.
    pub text: Box<str>,
    /// The text was longer than [`TEXT_MAX`] characters and was cut.
    pub cut: bool,
    /// How borer knows it, and so what it is.
    pub source: Source,
    /// How well it matches.
    pub rank: Rank,
}

impl Hit {
    /// Returns what the hit is ([`Source::kind`]).
    #[must_use]
    pub fn kind(&self) -> HitKind {
        self.source.kind()
    }
}

/// The hits of a find, best first, with every kind's true count.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Found {
    /// The hits: by rank, then kind, then those with an address before
    /// those without, then address, then text.
    pub hits: Vec<Hit>,
    /// Each kind that matched with how many matched, in kind order; a kind
    /// keeps at most [`KIND_MAX`] of them in [`Found::hits`].
    pub counted: Vec<(HitKind, usize)>,
    /// The needle was cut to [`NEEDLE_MAX`] characters ([`Query::cut`]).
    pub cut: bool,
    /// The place the query spelled that no section maps, so no address
    /// hit heads the list.
    pub unmapped: Option<Place>,
}

/// A hit before it is kept: its rank, address and whole text, its place
/// in its table, and what its source is built from.
struct Candidate<'t, T> {
    /// How well it matches.
    rank: Rank,
    /// Where it is.
    addr: Option<u64>,
    /// Its whole text.
    text: Cow<'t, str>,
    /// Its place in the table's walk, the last tie-break.
    seq: usize,
    /// What its source is built from.
    from: T,
}

impl<T> Candidate<'_, T> {
    /// Orders candidates of one kind: by rank, then those with an address
    /// first, then address, text and place in the table.
    ///
    /// # Arguments
    ///
    /// * `other` - The candidate compared with.
    fn order(&self, other: &Self) -> Ordering {
        (
            self.rank,
            self.addr.is_none(),
            self.addr,
            &self.text,
            self.seq,
        )
            .cmp(&(
                other.rank,
                other.addr.is_none(),
                other.addr,
                &other.text,
                other.seq,
            ))
    }
}

/// One kind's best [`KIND_MAX`] candidates so far and how many there were,
/// in memory bounded by the cap whatever the table holds.
struct Best<'t, T> {
    /// What the candidates are.
    kind: HitKind,
    /// At most twice [`KIND_MAX`] candidates, the best among them.
    kept: Vec<Candidate<'t, T>>,
    /// Every candidate offered.
    count: usize,
}

impl<'t, T> Best<'t, T> {
    /// Returns an empty selection of `kind`.
    ///
    /// # Arguments
    ///
    /// * `kind` - What the candidates are.
    fn new(kind: HitKind) -> Self {
        Self {
            kind,
            kept: Vec::with_capacity(2 * KIND_MAX),
            count: 0,
        }
    }

    /// Offers one match, dropping the worse half once twice the cap is held.
    ///
    /// # Arguments
    ///
    /// * `rank` - How well it matches.
    /// * `addr` - Where it is.
    /// * `text` - Its whole text.
    /// * `from` - What its source is built from.
    fn offer(&mut self, rank: Rank, addr: Option<u64>, text: Cow<'t, str>, from: T) {
        self.kept.push(Candidate {
            rank,
            addr,
            text,
            seq: self.count,
            from,
        });
        self.count += 1;
        if self.kept.len() >= 2 * KIND_MAX {
            self.kept
                .select_nth_unstable_by(KIND_MAX - 1, Candidate::order);
            self.kept.truncate(KIND_MAX);
        }
    }

    /// Counts the kind and keeps its best [`KIND_MAX`] in `found`.
    ///
    /// # Arguments
    ///
    /// * `found` - Receives the count and the hits.
    /// * `source` - Builds a kept hit's source.
    fn keep(mut self, found: &mut Found, source: impl Fn(T) -> Source) {
        if self.count == 0 {
            return;
        }
        found.counted.push((self.kind, self.count));
        self.kept.sort_by(Candidate::order);
        self.kept.truncate(KIND_MAX);
        found.hits.extend(self.kept.into_iter().map(|c| {
            let (text, cut) = head(&c.text, TEXT_MAX);
            Hit {
                addr: c.addr,
                text: if cut {
                    format!("{text}...").into()
                } else {
                    text.into()
                },
                cut,
                source: source(c.from),
                rank: c.rank,
            }
        }));
    }
}

/// Searches every table a query names and ranks the hits into one list.
///
/// Under [`Scope::All`] an address form is answered first, a bare number
/// through [`resolve`] so a name that spells it wins, as an
/// [`HitKind::Address`] hit that ranks exact. Every table is matched in one
/// pass by one case-folded search, linear in the text ([`Matcher`]), each
/// kind keeps at most [`KIND_MAX`] hits in memory bounded by that cap, and
/// the merge is stable over the kinds' own order, so the list is the same
/// at any thread count. Thunks and funclets are functions like any other.
/// An empty needle finds nothing.
///
/// # Arguments
///
/// * `p` - The loaded program.
/// * `a` - Its analysis, whose memo keeps the string walk and the lowered
///   symbol names.
/// * `o` - User names, comments and types.
/// * `q` - The query ([`Query::parse`]).
/// * `limit` - Most hits listed.
///
/// # Returns
///
/// The best `limit` hits with every kind's true count.
#[must_use]
pub fn everywhere(p: &Program, a: &Analysis, o: &Overlay, q: &Query, limit: usize) -> Found {
    let mut found = Found {
        cut: q.cut,
        ..Found::default()
    };
    let m = Matcher::new(q);
    if !m.needle.is_empty() {
        match q.scope {
            Scope::All(place) => {
                if let Some(place) = place {
                    address(p, a, o, &q.needle, place, &mut found);
                }
                functions(a, o, &m, &mut found);
                symbols(p, a, &m, &mut found);
                strings(p, a, &m, &mut found);
                types(p, a, o, &m, &mut found);
                notes(a, o, &m, false, &mut found);
            }
            Scope::Functions => functions(a, o, &m, &mut found),
            Scope::Strings => strings(p, a, &m, &mut found),
            Scope::Types => types(p, a, o, &m, &mut found),
            Scope::Notes => notes(a, o, &m, true, &mut found),
        }
    }
    found.hits.sort_by_key(|h| (h.rank, h.kind()));
    found.hits.truncate(limit);
    found
}

/// Adds the place an address form names.
///
/// That is the function holding it and the offset into it, else its
/// section; for a place no section maps, nothing but [`Found::unmapped`]. A
/// bare number that [`resolve`] reads as a name adds nothing: the name is
/// its own hit.
///
/// # Arguments
///
/// * `p` - The loaded program.
/// * `a` - Its analysis.
/// * `o` - User names.
/// * `n` - The needle, which spells the address.
/// * `place` - The form it spells.
/// * `found` - Receives the hit.
fn address(p: &Program, a: &Analysis, o: &Overlay, n: &Needle, place: Place, found: &mut Found) {
    let va = match place {
        Place::Va(va) => Some(va),
        Place::Number(number) => match resolve(p, a, o, n.as_str()) {
            Ok(va) if va == number => Some(va),
            Ok(_) | Err(_) => return,
        },
        Place::Rva(rva) => p.image_base.checked_add(rva),
        Place::Off(off) => p.offset_to_va(off),
    };
    let text = va.and_then(|va| match a.function_at(va) {
        Some(f) => Some(format!("{}{}", name_of(a, o, f.entry), f.offset_of(va))),
        None => p.section_at(va).map(|s| s.name.clone()),
    });
    let mut best = Best::new(HitKind::Address);
    match text {
        Some(text) => best.offer(Rank::Exact, va, Cow::Owned(text), place),
        None => found.unmapped = Some(place),
    }
    best.keep(found, Source::Address);
}

/// Adds the functions, thunks and funclets among them, whose name in force
/// holds the needle.
///
/// # Arguments
///
/// * `a` - The analysis.
/// * `o` - User names, which win over the analysis's.
/// * `m` - The needle's matcher.
/// * `found` - Receives the hits.
fn functions(a: &Analysis, o: &Overlay, m: &Matcher<'_>, found: &mut Found) {
    let mut best = Best::new(HitKind::Function);
    let mut spelled = String::new();
    for f in &a.functions {
        let ranked = match f.name_in_force(o) {
            Some(name) => m.rank(name).map(|rank| (rank, Cow::Borrowed(name))),
            None => {
                spelled.clear();
                let _ = write!(spelled, "sub_{:x}", f.entry);
                m.rank(&spelled)
                    .map(|rank| (rank, Cow::Owned(spelled.clone())))
            }
        };
        if let Some((rank, text)) = ranked {
            best.offer(rank, Some(f.entry), text, f);
        }
    }
    best.keep(found, |f: &Function| {
        Source::Function(FunctionRow::of(a, o, f).src)
    });
}

/// One symbol's texts as a find tests them, lowered once per analysis.
#[derive(Debug)]
struct SymbolText {
    /// The name shown: demangled, without its module.
    shown: String,
    /// The whole name, module included, lowered.
    lowered: String,
    /// The name shown, lowered.
    shown_lowered: String,
}

/// Adds the symbols whose whole name, module included, or demangled name
/// holds the needle, as imports, exports and the rest, each ranked by the
/// better of the two.
///
/// # Arguments
///
/// * `p` - The loaded program.
/// * `a` - Its analysis, whose memo keeps the lowered names.
/// * `m` - The needle's matcher.
/// * `found` - Receives the hits.
fn symbols(p: &Program, a: &Analysis, m: &Matcher<'_>, found: &mut Found) {
    let texts = a.derived.get_or_build("find_symbols", (), || {
        p.symbols
            .iter()
            .map(|s| {
                let shown = demangled_or_raw(bare_name(&s.name));
                SymbolText {
                    lowered: s.name.to_lowercase(),
                    shown_lowered: shown.to_lowercase(),
                    shown,
                }
            })
            .collect::<Vec<_>>()
    });
    let mut best = [HitKind::Import, HitKind::Export, HitKind::Symbol].map(Best::new);
    let needle = m.text();
    for (s, t) in p.symbols.iter().zip(texts.iter()) {
        if !t.lowered.contains(needle) && !t.shown_lowered.contains(needle) {
            continue;
        }
        let slot = match HitKind::of_symbol(s.kind) {
            HitKind::Import => 0,
            HitKind::Export => 1,
            HitKind::Symbol => 2,
            HitKind::Address
            | HitKind::Function
            | HitKind::String
            | HitKind::Type
            | HitKind::Class
            | HitKind::Name
            | HitKind::Comment => continue,
        };
        let rank = [m.rank(&s.name), m.rank(&t.shown)]
            .into_iter()
            .flatten()
            .min()
            .unwrap_or(Rank::Substring);
        if let Some(b) = best.get_mut(slot) {
            b.offer(rank, symbol_addr(s), Cow::Borrowed(t.shown.as_str()), s);
        }
    }
    for b in best {
        b.keep(found, |s: &Symbol| Source::Symbol {
            kind: s.kind,
            module: symbol_module(&s.name).map(Into::into),
        });
    }
}

/// Adds the walked strings that hold the needle.
///
/// # Arguments
///
/// * `p` - The loaded program.
/// * `a` - Its analysis, whose memo keeps the walk.
/// * `m` - The needle's matcher.
/// * `found` - Receives the hits.
fn strings(p: &Program, a: &Analysis, m: &Matcher<'_>, found: &mut Found) {
    let walked = walks(p, a);
    let mut best = Best::new(HitKind::String);
    let mut wide = String::new();
    for s in walked.spans() {
        let ranked = match s.encoding {
            Encoding::Ascii => {
                let text = s.whole_text(&p.bytes);
                m.rank(&text).map(|rank| (rank, text))
            }
            Encoding::Utf16 | Encoding::DotnetUs => {
                wide.clear();
                s.push_text(&p.bytes, &mut wide);
                m.rank(&wide).map(|rank| (rank, Cow::Owned(wide.clone())))
            }
        };
        if let Some((rank, text)) = ranked {
            best.offer(rank, p.offset_to_va(s.off), text, (s.off, s.encoding));
        }
    }
    for h in walked.user() {
        let text = h.full_text(&p.bytes);
        if let Some(rank) = m.rank(&text) {
            best.offer(rank, p.offset_to_va(h.off), text, (h.off, h.encoding));
        }
    }
    best.keep(found, |(off, encoding)| Source::String {
        off,
        section: p
            .offset_to_va(off)
            .and_then(|va| p.section_at(va))
            .map(|s| s.name.as_str().into()),
        encoding,
    });
}

/// Adds the user and debug types and the recovered classes whose name
/// holds the needle.
///
/// # Arguments
///
/// * `p` - The loaded program, for its debug types.
/// * `a` - Its analysis, for its classes.
/// * `o` - The user's types.
/// * `m` - The needle's matcher.
/// * `found` - Receives the hits.
fn types(p: &Program, a: &Analysis, o: &Overlay, m: &Matcher<'_>, found: &mut Found) {
    let mut best = Best::new(HitKind::Type);
    let user = o.types.keys().map(|t| (t, TypeOrigin::User));
    let debug = p.debug_types.keys().chain(p.debug_typedefs.keys());
    for (t, origin) in user.chain(debug.map(|t| (t, TypeOrigin::Debug))) {
        if let Some(rank) = m.rank(t) {
            best.offer(rank, None, Cow::Borrowed(t.as_str()), origin);
        }
    }
    best.keep(found, Source::Type);
    let mut best = Best::new(HitKind::Class);
    for (name, c) in &a.classes.by_name {
        if let Some(rank) = m.rank(name) {
            let origin = match c.vtable {
                Some(_) => ClassOrigin::Vtable,
                None => ClassOrigin::Descriptor,
            };
            best.offer(rank, c.vtable, Cow::Borrowed(name.as_str()), origin);
        }
    }
    best.keep(found, Source::Class);
}

/// Adds the user's names and comments that hold the needle.
///
/// # Arguments
///
/// * `a` - The analysis, for the function entries.
/// * `o` - The user's names and comments.
/// * `m` - The needle's matcher.
/// * `entries` - Whether a name at a function's entry is listed too; a
///   search of every table lists it as the function's hit instead.
/// * `found` - Receives the hits.
fn notes(a: &Analysis, o: &Overlay, m: &Matcher<'_>, entries: bool, found: &mut Found) {
    let mut best = Best::new(HitKind::Name);
    for (va, name) in &o.names {
        if (entries || a.function(*va).is_none())
            && let Some(rank) = m.rank(name)
        {
            best.offer(rank, Some(*va), Cow::Borrowed(name.as_str()), ());
        }
    }
    best.keep(found, |()| Source::User);
    let mut best = Best::new(HitKind::Comment);
    for (va, c) in &o.comments {
        if let Some(rank) = m.rank(c) {
            let kind = match open_question(c) {
                Some(_) => CommentKind::Question,
                None => CommentKind::Finding,
            };
            best.offer(rank, Some(*va), Cow::Borrowed(c.as_str()), kind);
        }
    }
    best.keep(found, Source::Comment);
}

/// One query's needle, ready to rank texts: a case-folded Knuth-Morris-Pratt
/// search, linear in the text and the needle.
#[derive(Debug)]
struct Matcher<'q> {
    /// The lowered needle's bytes.
    needle: &'q [u8],
    /// The needle's failure table: for each prefix, the longest proper
    /// prefix of it that is also its suffix.
    fail: Vec<usize>,
    /// The needle was cut, so no text matches it whole.
    cut: bool,
}

impl<'q> Matcher<'q> {
    /// Returns the matcher of a query's needle.
    ///
    /// # Arguments
    ///
    /// * `q` - The query.
    fn new(q: &'q Query) -> Self {
        let needle = q.needle.as_str().as_bytes();
        let mut fail = vec![0; needle.len()];
        let mut k = 0;
        for i in 1..needle.len() {
            while k > 0 && needle.get(i) != needle.get(k) {
                k = fail.get(k - 1).copied().unwrap_or(0);
            }
            if needle.get(i) == needle.get(k) {
                k += 1;
            }
            if let Some(slot) = fail.get_mut(i) {
                *slot = k;
            }
        }
        Self {
            needle,
            fail,
            cut: q.cut,
        }
    }

    /// Returns the lowered needle.
    fn text(&self) -> &str {
        std::str::from_utf8(self.needle).unwrap_or_default()
    }

    /// Returns how well `hay` holds the needle, in any case.
    ///
    /// An ASCII `hay` is folded in place; any other is lowered once,
    /// character by character, and its word starts are read off its
    /// characters before lowering. A needle lowered in context
    /// ([`Needle::new`], a final sigma) may miss such a text; it never
    /// matches a wrong one.
    ///
    /// # Arguments
    ///
    /// * `hay` - The text tested.
    ///
    /// # Returns
    ///
    /// The best place the needle starts at; `None` when it is nowhere, or
    /// empty.
    fn rank(&self, hay: &str) -> Option<Rank> {
        if self.needle.is_empty() {
            return None;
        }
        if hay.is_ascii() {
            let bytes = hay.as_bytes();
            return self.best(bytes, |at| {
                let before = at
                    .checked_sub(1)
                    .and_then(|i| bytes.get(i))
                    .map(|&b| char::from(b));
                let here = bytes.get(at).map(|&b| char::from(b));
                word_start(before, here)
            });
        }
        let mut lowered = String::with_capacity(hay.len());
        let mut starts = Vec::new();
        let mut before = None;
        for c in hay.chars() {
            if word_start(before, Some(c)) {
                starts.push(lowered.len());
            }
            lowered.extend(c.to_lowercase());
            before = Some(c);
        }
        self.best(lowered.as_bytes(), |at| starts.binary_search(&at).is_ok())
    }

    /// Returns the best rank of the needle in `hay`, one pass over it.
    ///
    /// # Arguments
    ///
    /// * `hay` - The text's bytes, folded case-insensitively.
    /// * `word` - Whether a match starting at a byte starts a word.
    fn best(&self, hay: &[u8], word: impl Fn(usize) -> bool) -> Option<Rank> {
        let n = self.needle.len();
        let mut k = 0;
        let mut seen = None;
        for (i, b) in hay.iter().enumerate() {
            while k > 0
                && !self
                    .needle
                    .get(k)
                    .is_some_and(|c| c.eq_ignore_ascii_case(b))
            {
                k = self.fail.get(k - 1).copied().unwrap_or(0);
            }
            if self
                .needle
                .get(k)
                .is_some_and(|c| c.eq_ignore_ascii_case(b))
            {
                k += 1;
            }
            if k < n {
                continue;
            }
            let at = i + 1 - n;
            if at == 0 {
                let whole = hay.len() == n && !self.cut;
                return Some(if whole { Rank::Exact } else { Rank::Prefix });
            }
            if word(at) {
                return Some(Rank::Word);
            }
            seen = Some(Rank::Substring);
            k = self.fail.get(k - 1).copied().unwrap_or(0);
        }
        seen
    }
}

/// Returns whether a character starts a word after the one before it: the
/// first character, one after a character that is neither a letter nor a
/// digit, or an uppercase letter after a lowercase one.
///
/// # Arguments
///
/// * `before` - The character before; `None` at the start.
/// * `here` - The character tested; `None` past the end.
fn word_start(before: Option<char>, here: Option<char>) -> bool {
    match (before, here) {
        (_, None) => false,
        (None, Some(_)) => true,
        (Some(b), Some(h)) => !b.is_alphanumeric() || (b.is_lowercase() && h.is_uppercase()),
    }
}

impl Found {
    /// Returns the find as the `borer://find` resource prints it.
    ///
    /// # Returns
    ///
    /// A `# showing N of M hits` line with each kind's kept and matched
    /// counts, then when they hold that the needle was cut, how many texts
    /// were cut and that the address or the file offset is in no mapped
    /// section; a column header;
    /// then one `rank kind addr source text` row per hit: `-` for no
    /// address, the source and the text escaped to one column and one line.
    #[must_use]
    pub fn spell(&self) -> String {
        let total: usize = self.counted.iter().map(|c| c.1).sum();
        let mut out = format!("# showing {} of {total} hits", self.hits.len());
        for (i, &(kind, count)) in self.counted.iter().enumerate() {
            let kept = self.hits.iter().filter(|h| h.kind() == kind).count();
            let sep = if i == 0 { ": " } else { ", " };
            let _ = write!(out, "{sep}{} {kept} of {count}", kind.word());
        }
        if self.cut {
            let _ = write!(out, "; needle cut to {NEEDLE_MAX} characters");
        }
        let cut = self.hits.iter().filter(|h| h.cut).count();
        if cut > 0 {
            let texts = if cut == 1 { "text" } else { "texts" };
            let _ = write!(out, "; {cut} {texts} cut to {TEXT_MAX} characters");
        }
        match self.unmapped {
            Some(Place::Off(_)) => out.push_str("; the file offset is in no mapped section"),
            Some(Place::Va(_) | Place::Number(_) | Place::Rva(_)) => {
                out.push_str("; the address is in no mapped section");
            }
            None => {}
        }
        out.push_str("\n# rank kind addr source text\n");
        for h in &self.hits {
            let addr = h.addr.map_or_else(|| "-".to_owned(), |a| format!("{a:#x}"));
            let _ = writeln!(
                out,
                "{} {} {addr} {} {}",
                h.rank.word(),
                h.kind().word(),
                h.source.code(),
                one_line(&h.text)
            );
        }
        out
    }
}

impl HitKind {
    /// Returns the word a row spells the kind with: `address`, `function`,
    /// `import`, `export`, `symbol`, `string`, `type`, `class`, `name` or
    /// `comment`.
    #[must_use]
    pub fn word(self) -> &'static str {
        match self {
            HitKind::Address => "address",
            HitKind::Function => "function",
            HitKind::Import => "import",
            HitKind::Export => "export",
            HitKind::Symbol => "symbol",
            HitKind::String => "string",
            HitKind::Type => "type",
            HitKind::Class => "class",
            HitKind::Name => "name",
            HitKind::Comment => "comment",
        }
    }
}

impl Rank {
    /// Returns the word a row spells the rank with: `exact`, `prefix`,
    /// `word` or `substring`.
    #[must_use]
    pub fn word(self) -> &'static str {
        match self {
            Rank::Exact => "exact",
            Rank::Prefix => "prefix",
            Rank::Word => "word",
            Rank::Substring => "substring",
        }
    }
}

impl Source {
    /// Returns the token a row spells the source with, one column: a blank
    /// in a module's or a section's name is written `\x20`.
    ///
    /// # Returns
    ///
    /// `va`, `number`, `rva` or `off` for the address form; a function's
    /// [`RowSource::code`]; a symbol's kind, then `:` and its module when it
    /// has one; a string's section (`off=<n>` for bytes no section maps),
    /// `:` and its encoding; `usr` or `debug` for a type; `vtable` or
    /// `descriptor` for a class; `usr` for a name; `finding` or `question`
    /// for a comment.
    #[must_use]
    pub fn code(&self) -> String {
        let column = |text: &str| one_line(text).replace(' ', "\\x20");
        match self {
            Source::Address(Place::Va(_)) => "va".to_owned(),
            Source::Address(Place::Number(_)) => "number".to_owned(),
            Source::Address(Place::Rva(_)) => "rva".to_owned(),
            Source::Address(Place::Off(_)) => "off".to_owned(),
            Source::Function(src) => src.code().to_owned(),
            Source::Symbol { kind, module } => match module {
                Some(m) => format!("{}:{}", kind.name(), column(m)),
                None => kind.name().to_owned(),
            },
            Source::String {
                off,
                section,
                encoding,
            } => match section {
                Some(s) => format!("{}:{}", column(s), encoding.name()),
                None => format!("off={off:#x}:{}", encoding.name()),
            },
            Source::Type(TypeOrigin::User) | Source::User => "usr".to_owned(),
            Source::Type(TypeOrigin::Debug) => "debug".to_owned(),
            Source::Class(ClassOrigin::Vtable) => "vtable".to_owned(),
            Source::Class(ClassOrigin::Descriptor) => "descriptor".to_owned(),
            Source::Comment(CommentKind::Finding) => "finding".to_owned(),
            Source::Comment(CommentKind::Question) => "question".to_owned(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Returns how `hay` ranks under the query `text`.
    ///
    /// # Arguments
    ///
    /// * `text` - The query as typed.
    /// * `hay` - The text ranked.
    fn rank(text: &str, hay: &str) -> Option<Rank> {
        let q = Query::parse(text);
        Matcher::new(&q).rank(hay)
    }

    /// A match is ranked by where it starts, in any case, and a word starts
    /// where the characters before lowering say.
    ///
    /// # Panics
    ///
    /// When a rank differs.
    #[test]
    fn a_match_is_ranked_by_where_it_starts() {
        assert_eq!(rank("crypt", "CRYPT"), Some(Rank::Exact));
        assert_eq!(rank("crypt", "crypt_init"), Some(Rank::Prefix));
        assert_eq!(rank("crypt", "my_crypt"), Some(Rank::Word));
        assert_eq!(rank("crypt", "CryptEncrypt"), Some(Rank::Prefix));
        assert_eq!(rank("crypt", "doCrypt"), Some(Rank::Word));
        assert_eq!(rank("crypt", "doCrypt\u{e9}"), Some(Rank::Word));
        assert_eq!(rank("crypt", "\u{e9}crypt"), Some(Rank::Substring));
        assert_eq!(rank("crypt", "\u{e9} crypt"), Some(Rank::Word));
        assert_eq!(rank("crypt", "encrypt"), Some(Rank::Substring));
        assert_eq!(rank("aab", "aaab"), Some(Rank::Substring));
        assert_eq!(rank("crypt", "cryp"), None);
        assert_eq!(rank("crypt", ""), None);
        assert_eq!(rank("", "crypt"), None);
    }

    /// A needle cut to its cap matches no text whole.
    ///
    /// # Panics
    ///
    /// When the cut needle ranks exact.
    #[test]
    fn a_cut_needle_is_never_exact() {
        let hay = "a".repeat(NEEDLE_MAX);
        assert_eq!(rank(&hay, &hay), Some(Rank::Exact));
        let long = format!("{hay}{}", "x".repeat(44));
        assert_eq!(rank(&long, &hay), Some(Rank::Prefix));
    }

    /// Each kind prefix narrows the scope and leaves the needle lowered;
    /// a prefix the grammar lacks is plain text.
    ///
    /// # Panics
    ///
    /// When a scope or a needle differs.
    #[test]
    fn a_prefix_picks_the_tables() {
        let parsed = |text: &str| {
            let q = Query::parse(text);
            (q.scope, q.needle.as_str().to_owned())
        };
        assert_eq!(parsed("Crypt"), (Scope::All(None), "crypt".to_owned()));
        assert_eq!(parsed("@Crypt"), (Scope::Functions, "crypt".to_owned()));
        assert_eq!(parsed("\"cry"), (Scope::Strings, "cry".to_owned()));
        assert_eq!(parsed("\"cry\""), (Scope::Strings, "cry".to_owned()));
        assert_eq!(parsed("t:ctx"), (Scope::Types, "ctx".to_owned()));
        assert_eq!(parsed("#key"), (Scope::Notes, "key".to_owned()));
        assert_eq!(parsed("x:key"), (Scope::All(None), "x:key".to_owned()));
    }

    /// The address forms are read only without a prefix, as `borer://addr`
    /// reads them ([`Place::parse`]), and text that is not a number in its
    /// form is no address.
    ///
    /// # Panics
    ///
    /// When a scope differs.
    #[test]
    fn an_address_form_is_a_place() {
        let place = |text: &str| Query::parse(text).scope;
        assert_eq!(place("0x401000"), Scope::All(Some(Place::Va(0x40_1000))));
        assert_eq!(place("4198400"), Scope::All(Some(Place::Number(4_198_400))));
        assert_eq!(place("rva:0x1000"), Scope::All(Some(Place::Rva(0x1000))));
        assert_eq!(place("rva:1a00"), Scope::All(Some(Place::Rva(0x1a00))));
        assert_eq!(place("off:0x400"), Scope::All(Some(Place::Off(0x400))));
        assert_eq!(place("0xzz"), Scope::All(None));
        assert_eq!(place("rva:zz"), Scope::All(None));
        assert_eq!(place("crypt"), Scope::All(None));
        assert_eq!(place("add"), Scope::All(None));
        assert_eq!(place("beef"), Scope::All(None));
        assert_eq!(place("99999999999999999999999"), Scope::All(None));
        assert_eq!(place("@0x401000"), Scope::Functions);
    }

    /// A needle is cut to [`NEEDLE_MAX`] characters before it is lowered,
    /// whatever the text is made of, and says it was; an empty query is an
    /// empty needle.
    ///
    /// # Panics
    ///
    /// When a needle is longer than the cap or its cut is not said.
    #[test]
    fn a_needle_is_capped() {
        let long = "a".repeat(1 << 20);
        let marks = "\u{301}".repeat(1 << 16);
        for text in [long.as_str(), marks.as_str()] {
            let q = Query::parse(text);
            assert!(q.needle.as_str().chars().count() <= NEEDLE_MAX);
            assert!(q.cut);
        }
        for text in ["", "@", "t:", "\"", "crypt"] {
            assert!(!Query::parse(text).cut, "{text}");
        }
        assert_eq!(Query::parse("").needle.as_str(), "");
        let padded = format!("0x{}401000", "0".repeat(NEEDLE_MAX - 6));
        assert_eq!(padded.chars().count(), NEEDLE_MAX + 2);
        assert_eq!(Query::parse(&padded).scope, Scope::All(None));
    }
}
