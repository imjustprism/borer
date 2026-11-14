//! A text as lines of typed tokens, each name linked only to the one thing
//! the engine shows it means.
//!
//! A [`View`] holds its text once and the tokens that tile each line. A
//! token is where it ends in its line, its [`Kind`] and, when the engine
//! can show what it names, a place in the view's table of referents
//! ([`Ref`]). The tokens of a line spell it in order, so a view spells its
//! text byte for byte ([`View::spell`]). The decompile view
//! ([`crate::analysis::decompile::view`]) is read back out of the text a
//! function decompiles to; the function listing view
//! ([`crate::analysis::render::disasm_view`]) is written straight into a
//! [`Sink`] alongside its text.

use std::collections::BTreeMap;
use std::num::NonZeroU32;
use std::ops::Range;
use std::sync::Arc;

/// What a token of a view is.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Kind {
    /// A run of whitespace.
    Space,
    /// A comment: `//` to the end of the line, or `/*` to its `*/`.
    Comment,
    /// A C keyword, a preprocessor directive's name, `nullptr`, `true` or
    /// `false`, or an assembly prefix or operand keyword.
    Keyword,
    /// An instruction's mnemonic.
    Mnemonic,
    /// A machine register.
    Register,
    /// A type's name.
    Type,
    /// A function's name: one of the binary's, an import's, or one the text
    /// declares.
    Function,
    /// A variable a scope of the text declares: a parameter or a local.
    Variable,
    /// A global: an address the text spells, `g<bits>_<hex>`, a data
    /// symbol or an object the text declares `extern`.
    Global,
    /// A member a `->` or `.` names.
    Field,
    /// A block label, `L_<hex>`.
    Label,
    /// A code or target address.
    Address,
    /// A string or character literal.
    String,
    /// A numeric literal.
    Number,
    /// An operator or punctuation.
    Punct,
    /// A name nothing in the text or the engine resolves.
    Text,
}

/// What a token links to: the one thing its spelling names in its scope,
/// borne out by a fact of the engine.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Ref {
    /// A code address: a label's block, a branch's target.
    Address(u64),
    /// A function, by its entry.
    Function(u64),
    /// An import, by its slot.
    Import(u64),
    /// A global, by its address.
    Global(u64),
    /// A string literal in the image, by its address.
    String(u64),
    /// A variable of a function, by the name its text spells it with: a
    /// name `set_name` takes only when it is an `aN`, `local_N`, `home_N` or
    /// `arg_N`, or one the user gave.
    Variable {
        /// The function's entry.
        function: u64,
        /// The variable's name as the text spells it.
        name: Box<str>,
    },
    /// A type the text or the user declares, by its name.
    Type(Box<str>),
}

/// How many names of a view name something yet carry no link.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct Unlinked {
    /// Names exactly one thing spells, which no fact of the engine bears
    /// out.
    pub uncorroborated: usize,
    /// Names more than one thing spells.
    pub ambiguous: usize,
}

/// One token: where it ends in its line, what it is, what it links to.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Token {
    /// One past its last byte, counted from its line's first.
    end: u32,
    /// What it is.
    kind: Kind,
    /// Its referent's place in [`View::refs`] plus one, `None` without one.
    link: Option<NonZeroU32>,
}

/// A view of a large function holds millions of tokens, so each stays
/// within 12 bytes.
const _: () = assert!(size_of::<Token>() <= 12);

/// Where one line starts: in the text, and among the tokens.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
struct Start {
    /// Its first byte in the text.
    at: u32,
    /// Its first token's index.
    first: u32,
}

/// A text as lines of typed tokens.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct View {
    /// The text, once.
    text: Arc<str>,
    /// Where each line starts, and past the last a start one byte beyond
    /// the text: a line runs to the next one's start, its newline left out.
    starts: Box<[Start]>,
    /// The tokens, line after line.
    tokens: Box<[Token]>,
    /// The referents, each once, in order of first use.
    refs: Box<[Ref]>,
    /// The line each referent is defined on, by its place in `refs`.
    defs: Box<[Option<u32>]>,
    /// The names that name something yet carry no link.
    unlinked: Unlinked,
}

/// Widens a 32-bit offset or count of a view to an index.
///
/// # Arguments
///
/// * `n` - The offset or count.
fn wide(n: u32) -> usize {
    usize::try_from(n).unwrap_or(usize::MAX)
}

impl View {
    /// Returns how many lines the view holds: one more than its text's
    /// newlines, so a text ending in one ends with an empty line.
    #[must_use]
    pub fn lines(&self) -> usize {
        self.starts.len().saturating_sub(1)
    }

    /// Returns one line's text, without its newline.
    ///
    /// # Arguments
    ///
    /// * `i` - The line, from 0.
    ///
    /// # Returns
    ///
    /// The line, `None` past the last.
    #[must_use]
    pub fn line(&self, i: usize) -> Option<&str> {
        let (a, b) = (self.starts.get(i)?, self.starts.get(i.checked_add(1)?)?);
        self.text.get(wide(a.at)..wide(b.at).checked_sub(1)?)
    }

    /// Returns one line's tokens in order: the bytes each spans in the
    /// line, its kind and what it links to.
    ///
    /// # Arguments
    ///
    /// * `i` - The line, from 0.
    ///
    /// # Returns
    ///
    /// The tokens, which tile the line; none past the last line.
    pub fn tokens(
        &self,
        i: usize,
    ) -> impl Iterator<Item = (Range<usize>, Kind, Option<&Ref>)> + '_ {
        let span = i
            .checked_add(1)
            .and_then(|next| self.starts.get(i).zip(self.starts.get(next)))
            .map_or(0..0, |(a, b)| wide(a.first)..wide(b.first));
        let mut from = 0;
        self.tokens
            .get(span)
            .unwrap_or_default()
            .iter()
            .map(move |t| {
                let (start, end) = (from, wide(t.end));
                from = end;
                let link = t
                    .link
                    .and_then(|k| self.refs.get(wide(k.get()).checked_sub(1)?));
                (start..end, t.kind, link)
            })
    }

    /// Returns the text the tokens spell, line by line.
    ///
    /// # Returns
    ///
    /// The text the view was built from, byte for byte, when its tokens
    /// tile every line.
    #[must_use]
    pub fn spell(&self) -> String {
        let mut out = String::with_capacity(self.text.len());
        for i in 0..self.lines() {
            if i > 0 {
                out.push('\n');
            }
            let at = self.starts.get(i).map_or(0, |s| wide(s.at));
            for (span, _, _) in self.tokens(i) {
                let piece = at.saturating_add(span.start)..at.saturating_add(span.end);
                out.push_str(self.text.get(piece).unwrap_or_default());
            }
        }
        out
    }

    /// Returns the line a referent is defined on.
    ///
    /// A label is defined on its `L_x:` line, a parameter on the signature
    /// line, a local on its declaration, the function on its signature
    /// line, a function the text defines `static inline` and that body's
    /// parameters on its line, a type on the line that declares it.
    ///
    /// # Arguments
    ///
    /// * `r` - The referent.
    ///
    /// # Returns
    ///
    /// The line, from 0, or `None` when no token links to `r` or no line
    /// of the view defines it.
    #[must_use]
    pub fn definition(&self, r: &Ref) -> Option<usize> {
        let k = self.refs.iter().position(|x| x == r)?;
        self.defs.get(k).copied().flatten().map(wide)
    }

    /// Returns the heap bytes the view holds: its text, lines, tokens and
    /// referents.
    #[must_use]
    pub fn bytes(&self) -> usize {
        let names: usize = self
            .refs
            .iter()
            .map(|r| match r {
                Ref::Variable { name, .. } | Ref::Type(name) => name.len(),
                Ref::Address(_)
                | Ref::Function(_)
                | Ref::Import(_)
                | Ref::Global(_)
                | Ref::String(_) => 0,
            })
            .sum();
        self.text.len()
            + size_of_val(&*self.starts)
            + size_of_val(&*self.tokens)
            + size_of_val(&*self.refs)
            + size_of_val(&*self.defs)
            + names
    }

    /// Returns how many names name something yet carry no link: one thing
    /// spells them that no fact of the engine bears out, or more than one.
    #[must_use]
    pub fn unlinked(&self) -> Unlinked {
        self.unlinked
    }

    /// Returns the text, shared: a build that reads names out of it notes
    /// it as the body it looked them up in, without a copy.
    pub(crate) fn text(&self) -> &Arc<str> {
        &self.text
    }
}

/// Where a renderer that produces both plain text and a [`View`] writes
/// each piece of a line.
pub(crate) trait Sink {
    /// Appends `piece` to the open line with its kind and optional link.
    ///
    /// # Arguments
    ///
    /// * `piece` - The text to append.
    /// * `kind` - What the token is.
    /// * `link` - What the token links to, when known.
    fn put(&mut self, piece: &str, kind: Kind, link: Option<Ref>);

    /// Marks the referent of the last token put as defined on the open
    /// line, when the sink records definitions.
    fn define(&mut self) {}

    /// Ends the open line and starts the next.
    fn end_line(&mut self);
}

impl Sink for String {
    fn put(&mut self, piece: &str, _: Kind, _: Option<Ref>) {
        self.push_str(piece);
    }

    fn end_line(&mut self) {
        self.push('\n');
    }
}

/// Puts a [`View`] together a piece of text at a time, line by line.
#[derive(Debug, Default)]
pub(crate) struct Builder {
    /// The text so far.
    text: String,
    /// The starts of the lines ended so far.
    starts: Vec<Start>,
    /// The start of the open line.
    open: Start,
    /// The tokens so far.
    tokens: Vec<Token>,
    /// Each referent's place in the table, plus one.
    places: BTreeMap<Ref, NonZeroU32>,
    /// The line each referent is defined on, by its place plus one.
    defs: BTreeMap<NonZeroU32, u32>,
    /// The referent and first line of the most recent non-empty [`Builder::put`].
    last_put: Option<(NonZeroU32, u32)>,
    /// Whether the text outgrew the 32-bit offsets, which refuses the view.
    over: bool,
}

impl Sink for Builder {
    fn put(&mut self, piece: &str, kind: Kind, link: Option<Ref>) {
        Builder::put(self, piece, kind, link);
    }

    fn define(&mut self) {
        Builder::define(self);
    }

    fn end_line(&mut self) {
        Builder::end_line(self);
    }
}

impl Builder {
    /// Adds a piece of text to the open line as one token, splitting on
    /// any embedded newline so no line holds one.
    ///
    /// # Arguments
    ///
    /// * `piece` - The text; an empty one adds nothing.
    /// * `kind` - What it is.
    /// * `link` - What it links to.
    pub(crate) fn put(&mut self, piece: &str, kind: Kind, link: Option<Ref>) {
        self.last_put = None;
        if !piece.contains('\n') {
            self.put_span(piece, kind, link);
            return;
        }
        for (i, part) in piece.split('\n').enumerate() {
            if i > 0 {
                self.finish_line();
            }
            self.put_span(part, kind, link.clone());
        }
    }

    /// Adds a newline-free span to the open line as one token.
    ///
    /// # Arguments
    ///
    /// * `piece` - The span; an empty one adds nothing.
    /// * `kind` - What it is.
    /// * `link` - What it links to.
    fn put_span(&mut self, piece: &str, kind: Kind, link: Option<Ref>) {
        if piece.is_empty() {
            return;
        }
        self.text.push_str(piece);
        let end = self
            .text
            .len()
            .checked_sub(wide(self.open.at))
            .and_then(|n| u32::try_from(n).ok());
        let Some(end) = end else {
            self.over = true;
            return;
        };
        let link = link.and_then(|r| {
            let next = u32::try_from(self.places.len())
                .ok()?
                .checked_add(1)
                .and_then(NonZeroU32::new)?;
            Some(*self.places.entry(r).or_insert(next))
        });
        if self.last_put.is_none()
            && let (Some(k), Ok(line)) = (link, u32::try_from(self.starts.len()))
        {
            self.last_put = Some((k, line));
        }
        self.tokens.push(Token { end, kind, link });
    }

    /// Marks the referent of the token put last as defined on the line it
    /// opened on, unless an earlier line defines it.
    pub(crate) fn define(&mut self) {
        if let Some((k, line)) = self.last_put {
            self.defs.entry(k).or_insert(line);
        }
    }

    /// Ends the open line and opens the next.
    pub(crate) fn end_line(&mut self) {
        self.last_put = None;
        self.finish_line();
    }

    /// Appends a newline and records the open line's start without clearing
    /// [`Builder::last_put`].
    fn finish_line(&mut self) {
        self.text.push('\n');
        self.starts.push(self.open);
        match (
            u32::try_from(self.text.len()),
            u32::try_from(self.tokens.len()),
        ) {
            (Ok(at), Ok(first)) => self.open = Start { at, first },
            _ => self.over = true,
        }
    }

    /// Ends the open line and returns the view.
    ///
    /// # Arguments
    ///
    /// * `unlinked` - What the maker counted of the names it left unlinked.
    ///
    /// # Returns
    ///
    /// The view, or `None` when the text reached 4 GiB, which its 32-bit
    /// offsets cannot hold: it is refused, never wrapped.
    pub(crate) fn finish(mut self, unlinked: Unlinked) -> Option<View> {
        let at = u32::try_from(self.text.len()).ok()?.checked_add(1)?;
        let first = u32::try_from(self.tokens.len()).ok()?;
        if self.over {
            return None;
        }
        self.starts.extend([self.open, Start { at, first }]);
        let mut places: Vec<(NonZeroU32, Ref)> =
            self.places.into_iter().map(|(r, k)| (k, r)).collect();
        places.sort_unstable_by_key(|(k, _)| *k);
        let defs = places
            .iter()
            .map(|(k, _)| self.defs.get(k).copied())
            .collect();
        Some(View {
            text: Arc::from(self.text),
            starts: self.starts.into_boxed_slice(),
            tokens: self.tokens.into_boxed_slice(),
            refs: places.into_iter().map(|(_, r)| r).collect(),
            defs,
            unlinked,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::{Builder, Kind, Ref, Unlinked};

    /// A view spells its text, lines and all, gives each line its tokens
    /// with their bytes, kinds and links, holds each referent once, and
    /// finds where a referent is defined.
    ///
    /// # Panics
    ///
    /// When a line, a token or a definition comes back other than it was
    /// put.
    #[test]
    fn a_view_spells_its_lines_and_finds_what_they_define() {
        let mut b = Builder::default();
        let goto = Ref::Address(0x1010);
        b.put("goto", Kind::Keyword, None);
        b.put(" ", Kind::Space, None);
        b.put("L_1010", Kind::Label, Some(goto.clone()));
        b.put(";", Kind::Punct, None);
        b.end_line();
        b.put("L_1010", Kind::Label, Some(goto.clone()));
        b.define();
        b.put(":", Kind::Punct, None);
        b.end_line();
        let counted = Unlinked {
            uncorroborated: 1,
            ambiguous: 2,
        };
        let v = b.finish(counted).expect("a small view");
        assert_eq!(v.spell(), "goto L_1010;\nL_1010:\n");
        assert_eq!(v.lines(), 3);
        assert_eq!(v.line(1), Some("L_1010:"));
        assert_eq!(v.line(2), Some(""));
        assert_eq!(v.line(3), None);
        let first: Vec<_> = v.tokens(0).collect();
        assert_eq!(first.len(), 4);
        assert_eq!(first[2], (5..11, Kind::Label, Some(&goto)));
        assert_eq!(v.tokens(2).count(), 0);
        assert_eq!(v.tokens(usize::MAX).count(), 0);
        assert_eq!(v.definition(&goto), Some(1));
        assert_eq!(v.definition(&Ref::Function(0x1010)), None);
        assert_eq!(v.unlinked(), counted);
        assert!(v.bytes() >= v.spell().len());
        let empty = Builder::default()
            .finish(Unlinked::default())
            .expect("an empty view");
        assert_eq!((empty.lines(), empty.spell()), (1, String::new()));
    }

    /// Defining a referent after a trailing-newline or empty piece attaches
    /// it only to the line that put the non-empty token.
    ///
    /// # Panics
    ///
    /// When [`Builder::define`] attributes a definition to the wrong line.
    #[test]
    fn define_tracks_the_line_that_put_the_token() {
        let mut b = Builder::default();
        let first = Ref::Address(0x1000);
        let second = Ref::Address(0x1004);
        let unplaced = Ref::Address(0x1008);
        b.put("L_1000\n", Kind::Label, Some(first.clone()));
        b.define();
        b.put("fn_a", Kind::Function, Some(second.clone()));
        b.end_line();
        b.put("", Kind::Label, Some(unplaced.clone()));
        b.define();
        let v = b.finish(Unlinked::default()).expect("a small view");
        assert_eq!(v.definition(&first), Some(0));
        assert_eq!(v.definition(&second), None);
        assert_eq!(v.definition(&unplaced), None);
    }
}
