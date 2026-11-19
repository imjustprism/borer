//! A text as lines of typed tokens, each name linked only to the one thing
//! the engine shows it means.
//!
//! A [`View`] holds its text once and the tokens that tile each line. A
//! token is where it ends in its line, its [`Kind`] and, when the engine
//! can show what it names, a place in the view's table of referents
//! ([`Ref`]), which says who stated its name ([`Said`]) where the maker can
//! tell. The tokens of a line spell it in order, so a view spells its
//! text byte for byte ([`View::spell`]). The decompile view
//! ([`crate::analysis::decompile::view`]) is read back out of the text a
//! function decompiles to; the function listing view
//! ([`crate::analysis::render::disasm_view`]) is written straight into a
//! [`Sink`] alongside its text, and each of its instruction lines answers
//! the address it shows ([`View::address`]). Each line of the decompile
//! view answers the block it stands for ([`View::origin`]), and each line
//! of either view the block it was written from ([`View::block`]).

use std::collections::{BTreeMap, BTreeSet};
use std::num::NonZeroU32;
use std::ops::Range;
use std::sync::Arc;

use crate::analysis::Analysis;
use crate::analysis::decompile::Origins;
use crate::analysis::protos::VarKey;

/// What a token of a view is.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Kind {
    /// A run of whitespace.
    Space,
    /// A comment: `//` to the end of the line, or `/*` to its `*/`.
    Comment,
    /// A comment the overlay holds at one of the function's instructions:
    /// a decompile's line of its own, or a listing's after its instruction.
    Note,
    /// A note opening with `?`: an open question.
    Question,
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
    /// A named constant: a `#define`d value, an enum member or a platform
    /// constant.
    Constant,
    /// An operator or punctuation.
    Punct,
    /// A name nothing in the text or the engine resolves.
    Text,
}

/// What a token links to: the one thing its spelling names in its scope,
/// borne out by a fact of the engine.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Ref {
    /// A code address: a label's block, a branch's target, an instruction
    /// a listing line shows or a header names.
    Address(u64),
    /// A function, by its entry.
    Function(u64),
    /// An import, by its first slot: one id however many slots the loader
    /// lists it at.
    Import(u64),
    /// A global, by its address.
    Global(u64),
    /// A string literal in the image, by its address.
    String(u64),
    /// A struct or class field, by its aggregate type and byte offset.
    Field {
        /// The struct or class type.
        ty: Box<str>,
        /// Byte offset inside the aggregate.
        offset: u64,
    },
    /// A variable of a function, by the name its text spells it with and
    /// the parameter or stack slot that name is.
    Variable {
        /// The function's entry.
        function: u64,
        /// The variable's name as the text spells it.
        name: Box<str>,
        /// The parameter or slot the name is, as an edit of the variable
        /// names it ([`crate::analysis::edit::Edit::Var`] takes its
        /// [`VarKey::spell`]): one the user stated, one the debug
        /// information names, or an `aN`, `local_N`, `home_N` or `arg_N`;
        /// `None` for a name that is none of these.
        key: Option<VarKey>,
    },
    /// A type the text or the user declares, by its name.
    Type(Box<str>),
    /// A comment of the overlay, by the instruction address that holds it.
    Comment(u64),
}

/// Who stated the name a referent goes by, read from the fact the engine
/// spelled it with.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Said {
    /// The overlay's name: a person's or an agent's.
    User,
    /// The file's: its symbol table, an import or export, its debug
    /// information.
    Stated,
    /// The engine's own finding: a helper's shape, a vtable slot, a
    /// signature string, a pack's or a library's match.
    Inferred,
    /// A name the engine spells from an address, a slot or an ordinal
    /// because nothing names the thing: `sub_`, `aN`, `local_N`, `home_N`,
    /// `arg_N`, `g<bits>_`, `L_`, `field_0x`, `<dll>_ord<n>`.
    Placeholder,
}

/// How many referents of a view each [`Said`] names.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct SaidCounts {
    /// Referents named by the overlay.
    pub user: usize,
    /// Referents named by the file.
    pub stated: usize,
    /// Referents named by the engine's findings.
    pub inferred: usize,
    /// Referents nothing names.
    pub placeholder: usize,
    /// Referents that go by a name the view cannot tell of: no name token
    /// spells them, or the fact one was spelled from does not say. String
    /// literals and comments are no names and not counted.
    pub unknown: usize,
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

/// A block a line was written from, with the function it was written as
/// part of: a block two functions share is a block of each.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct LineBlock {
    /// The entry of the function whose listing or text wrote the line.
    pub function: u64,
    /// The block's start address.
    pub start: u64,
}

/// A run of lines written from one block: a block's instruction lines sit
/// together, so a listing holds about one run per block.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct BlockRun {
    /// Its first line.
    from: u32,
    /// One past its last line.
    to: u32,
    /// The block.
    block: LineBlock,
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

/// One token of a line as [`View::tokens_said`] gives it: the bytes it
/// spans in the line, its kind, and its link with who stated its
/// referent's name.
pub type SaidToken<'v> = (Range<usize>, Kind, Option<(&'v Ref, Option<Said>)>);

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
    /// Who stated each referent's name, by its place in `refs`; empty for a
    /// view no maker read it for ([`View::with_said`]).
    said: Box<[Option<Said>]>,
    /// The line each referent is defined on, by its place in `refs`.
    defs: Box<[Option<u32>]>,
    /// The names that name something yet carry no link.
    unlinked: Unlinked,
    /// Each line that shows an instruction, in line order; empty for a view
    /// of no listing.
    instr_lines: Box<[u32]>,
    /// The address of the instruction each of [`View::instr_lines`] shows,
    /// at the same place: two tables, so no entry carries padding.
    instr_vas: Box<[u64]>,
    /// Whether [`View::instr_vas`] runs in address order, which
    /// [`View::line_of`] then searches by.
    ordered: bool,
    /// The runs of lines and the block each was written from, in line
    /// order; empty for a view of no listing.
    blocks: Box<[BlockRun]>,
    /// The function the text is of and the block each line stands for,
    /// read by [`View::origin`]; `None` for a view of no decompiled text.
    origins: Option<(u64, Arc<Origins>)>,
}

/// The most uses of one referent [`View::uses`] returns.
pub const USES_MAX: usize = 4096;

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
        self.tokens_said(i)
            .map(|(span, kind, link)| (span, kind, link.map(|(r, _)| r)))
    }

    /// Returns one line's tokens in order as [`View::tokens`] does, each
    /// link with who stated its referent's name.
    ///
    /// # Arguments
    ///
    /// * `i` - The line, from 0.
    ///
    /// # Returns
    ///
    /// The tokens, which tile the line, each link paired with its
    /// [`Said`], `None` where the maker could not tell; none past the last
    /// line.
    pub fn tokens_said(&self, i: usize) -> impl Iterator<Item = SaidToken<'_>> + '_ {
        let mut from = 0;
        self.line_tokens(i).iter().map(move |t| {
            let (start, end) = (from, wide(t.end));
            from = end;
            (start..end, t.kind, self.link(t))
        })
    }

    /// Returns the token that holds one byte of a line.
    ///
    /// # Arguments
    ///
    /// * `i` - The line, from 0.
    /// * `byte` - The byte, from the line's first.
    ///
    /// # Returns
    ///
    /// The bytes the token spans in the line, its kind and what it links
    /// to, as [`View::tokens`] gives them; `None` past the line's end and
    /// past the last line.
    #[must_use]
    pub fn token_at(&self, i: usize, byte: usize) -> Option<(Range<usize>, Kind, Option<&Ref>)> {
        let line = self.line_tokens(i);
        let k = line.partition_point(|t| wide(t.end) <= byte);
        let t = line.get(k)?;
        let start = k
            .checked_sub(1)
            .and_then(|j| line.get(j))
            .map_or(0, |p| wide(p.end));
        Some((start..wide(t.end), t.kind, self.link(t).map(|(r, _)| r)))
    }

    /// Returns where a referent is spelled: the first [`USES_MAX`] tokens
    /// linked to it, in line order, and how many there are in all.
    ///
    /// # Arguments
    ///
    /// * `r` - The referent.
    ///
    /// # Returns
    ///
    /// Each shown token's line and the bytes it spans there, and the count
    /// of every token linked to `r`, so a caller can say `showing N of M`;
    /// empty and 0 when no token links to `r`.
    #[must_use]
    pub fn uses(&self, r: &Ref) -> (Vec<(usize, Range<usize>)>, usize) {
        let Some(want) = self
            .refs
            .iter()
            .position(|x| x == r)
            .and_then(|k| u32::try_from(k.checked_add(1)?).ok())
            .and_then(NonZeroU32::new)
        else {
            return (Vec::new(), 0);
        };
        let (mut shown, mut total) = (Vec::new(), 0usize);
        for i in 0..self.lines() {
            let mut from = 0;
            for t in self.line_tokens(i) {
                let (start, end) = (from, wide(t.end));
                from = end;
                if t.link == Some(want) {
                    total = total.saturating_add(1);
                    if shown.len() < USES_MAX {
                        shown.push((i, start..end));
                    }
                }
            }
        }
        (shown, total)
    }

    /// Returns one line's tokens as stored, none past the last line.
    ///
    /// # Arguments
    ///
    /// * `i` - The line, from 0.
    fn line_tokens(&self, i: usize) -> &[Token] {
        let span = i
            .checked_add(1)
            .and_then(|next| self.starts.get(i).zip(self.starts.get(next)))
            .map_or(0..0, |(a, b)| wide(a.first)..wide(b.first));
        self.tokens.get(span).unwrap_or_default()
    }

    /// Returns what a token links to, with who stated its name.
    ///
    /// # Arguments
    ///
    /// * `t` - The token.
    fn link(&self, t: &Token) -> Option<(&Ref, Option<Said>)> {
        let k = wide(t.link?.get()).checked_sub(1)?;
        Some((self.refs.get(k)?, self.said.get(k).copied().flatten()))
    }

    /// Returns the view with who stated each referent's name, read off the
    /// tokens that spell it as a name.
    ///
    /// The name tokens (a function, variable, global, field, label or type)
    /// of each referent are asked of `said` once per spelling, and no more
    /// once one says nothing; a referent whose spellings answer apart, or
    /// no name token spells, says nothing.
    ///
    /// # Arguments
    ///
    /// * `said` - Tells who stated a referent's name from the spelling of
    ///   one of its tokens, `None` when the fact it was spelled from does
    ///   not say.
    #[must_use]
    pub(crate) fn with_said(mut self, mut said: impl FnMut(&Ref, &str) -> Option<Said>) -> Self {
        let mut seen: Vec<Option<Option<Said>>> = vec![None; self.refs.len()];
        let mut asked: BTreeSet<(usize, &str)> = BTreeSet::new();
        for i in 0..self.lines() {
            let at = self.starts.get(i).map_or(0, |s| wide(s.at));
            let mut from = at;
            for t in self.line_tokens(i) {
                let span = from..at.saturating_add(wide(t.end));
                from = span.end;
                let named = match t.kind {
                    Kind::Function
                    | Kind::Variable
                    | Kind::Global
                    | Kind::Field
                    | Kind::Label
                    | Kind::Type => true,
                    Kind::Space
                    | Kind::Comment
                    | Kind::Note
                    | Kind::Question
                    | Kind::Keyword
                    | Kind::Mnemonic
                    | Kind::Register
                    | Kind::Address
                    | Kind::String
                    | Kind::Number
                    | Kind::Constant
                    | Kind::Punct
                    | Kind::Text => false,
                };
                let Some(k) = t.link.and_then(|l| wide(l.get()).checked_sub(1)) else {
                    continue;
                };
                let (true, Some(slot), Some(r), Some(spelled)) = (
                    named,
                    seen.get_mut(k),
                    self.refs.get(k),
                    self.text.get(span),
                ) else {
                    continue;
                };
                match *slot {
                    None => {
                        *slot = Some(said(r, spelled));
                        asked.insert((k, spelled));
                    }
                    Some(None) => {}
                    Some(Some(first)) => {
                        if asked.insert((k, spelled)) && said(r, spelled) != Some(first) {
                            *slot = Some(None);
                        }
                    }
                }
            }
        }
        self.said = seen.into_iter().map(Option::flatten).collect();
        self
    }

    /// Returns how many referents of the view each [`Said`] names, and how
    /// many that go by a name it cannot tell of: one count per referent
    /// however many tokens spell it.
    #[must_use]
    pub fn said_counts(&self) -> SaidCounts {
        let mut n = SaidCounts::default();
        for (k, r) in self.refs.iter().enumerate() {
            let named = match r {
                Ref::String(_) | Ref::Comment(_) => false,
                Ref::Address(_)
                | Ref::Function(_)
                | Ref::Import(_)
                | Ref::Global(_)
                | Ref::Field { .. }
                | Ref::Variable { .. }
                | Ref::Type(_) => true,
            };
            let c = match self.said.get(k).copied().flatten() {
                None if !named => continue,
                Some(Said::User) => &mut n.user,
                Some(Said::Stated) => &mut n.stated,
                Some(Said::Inferred) => &mut n.inferred,
                Some(Said::Placeholder) => &mut n.placeholder,
                None => &mut n.unknown,
            };
            *c = c.saturating_add(1);
        }
        n
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
    /// parameters on its line, a type on the line that declares it. In a
    /// listing a block's [`Ref::Address`] is defined on its `L_x:` label
    /// line, the one before the line that shows its first instruction
    /// ([`View::line_of`]): going to a label goes here, going to an
    /// instruction goes there.
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

    /// Returns the address of the instruction a line shows.
    ///
    /// # Arguments
    ///
    /// * `i` - The line, from 0.
    ///
    /// # Returns
    ///
    /// The address, `None` for a line that shows no instruction (a header,
    /// a label, a comment) and for every line of a view of no listing; in
    /// the linear listing ([`crate::analysis::render::linear()`]) every line
    /// answers the address its row shows.
    #[must_use]
    pub fn address(&self, i: usize) -> Option<u64> {
        let i = u32::try_from(i).ok()?;
        let k = self.instr_lines.binary_search(&i).ok()?;
        self.instr_vas.get(k).copied()
    }

    /// Returns the first line that shows the instruction at an address.
    ///
    /// For a block's start that is the line after its `L_x:` label, which
    /// [`View::definition`] gives.
    ///
    /// # Arguments
    ///
    /// * `va` - The instruction's address.
    ///
    /// # Returns
    ///
    /// The line, from 0, or `None` when no line shows an instruction there.
    #[must_use]
    pub fn line_of(&self, va: u64) -> Option<usize> {
        let k = if self.ordered {
            Some(self.instr_vas.partition_point(|&at| at < va))
                .filter(|&k| self.instr_vas.get(k) == Some(&va))
        } else {
            self.instr_vas.iter().position(|&at| at == va)
        };
        self.instr_lines.get(k?).copied().map(wide)
    }

    /// Returns the block a line of a decompiled text stands for.
    ///
    /// # Arguments
    ///
    /// * `i` - The line, from 0.
    ///
    /// # Returns
    ///
    /// The start address of the one block whose lifted code spells the
    /// line; `None` for a line no block is known to stand for (a header, a
    /// declaration, a test or jump the emitter wrote, a line the text
    /// passes wrote that no rule places), past the last line, and for every
    /// line of a view of no decompiled text.
    #[must_use]
    pub fn origin(&self, i: usize) -> Option<u64> {
        self.origins.as_ref().and_then(|(_, o)| o.line(i))
    }

    /// Returns the block a line was written from, with its function.
    ///
    /// A decompiled text's line is written from its origin ([`View::origin`])
    /// as part of the text's function; a listing's instruction line from the
    /// block the listing wrote it under, which for code two functions share
    /// is the listed function's own block, never the other's.
    ///
    /// # Arguments
    ///
    /// * `i` - The line, from 0.
    ///
    /// # Returns
    ///
    /// The block, `None` for a line written from no block: a header, a
    /// label, a comment, a line no rule places, and past the last line.
    #[must_use]
    pub fn block(&self, i: usize) -> Option<LineBlock> {
        if let Some((function, origins)) = &self.origins {
            let start = origins.line(i)?;
            return Some(LineBlock {
                function: *function,
                start,
            });
        }
        let line = u32::try_from(i).ok()?;
        let k = self.blocks.partition_point(|r| r.to <= line);
        self.blocks
            .get(k)
            .filter(|r| r.from <= line)
            .map(|r| r.block)
    }

    /// Returns the first line that stands for the instruction at an
    /// address: the line showing it, else the first line written from a
    /// block holding it, by the bounds of that line's own function's block.
    ///
    /// One pass over the lines; a run of lines from one block asks once,
    /// and each block is found among its function's sorted blocks by
    /// binary search.
    ///
    /// # Arguments
    ///
    /// * `a` - The analysis, for the blocks' bounds.
    /// * `va` - The instruction's address.
    ///
    /// # Returns
    ///
    /// The line, from 0, or `None` when no line stands for it.
    #[must_use]
    pub fn line_for(&self, a: &Analysis, va: u64) -> Option<usize> {
        let holds = |b: LineBlock| {
            let blocks = a
                .function(b.function)
                .map_or(&[][..], |f| f.blocks.as_slice());
            let k = blocks.binary_search_by_key(&b.start, |x| x.start).ok();
            k.and_then(|k| blocks.get(k))
                .is_some_and(|x| x.start <= va && va < x.end)
        };
        self.line_of(va).or_else(|| {
            let mut last: Option<(LineBlock, bool)> = None;
            (0..self.lines()).find(|&i| {
                let Some(b) = self.block(i) else {
                    return false;
                };
                match last {
                    Some((seen, hit)) if seen == b => hit,
                    _ => {
                        let hit = holds(b);
                        last = Some((b, hit));
                        hit
                    }
                }
            })
        })
    }

    /// Returns the view with the block each of its lines stands for.
    ///
    /// # Arguments
    ///
    /// * `function` - The entry of the function the text is of.
    /// * `origins` - One origin per line of the view's text
    ///   ([`crate::analysis::decompile::answer_with_origins`]).
    #[must_use]
    pub(crate) fn with_origins(mut self, function: u64, origins: Arc<Origins>) -> Self {
        self.origins = Some((function, origins));
        self
    }

    /// Returns the heap bytes the view holds: its text, lines, tokens,
    /// referents, instruction addresses and line origins.
    #[must_use]
    pub fn bytes(&self) -> usize {
        let names: usize = self
            .refs
            .iter()
            .map(|r| match r {
                Ref::Variable { name, .. } | Ref::Type(name) | Ref::Field { ty: name, .. } => {
                    name.len()
                }
                Ref::Address(_)
                | Ref::Function(_)
                | Ref::Import(_)
                | Ref::Global(_)
                | Ref::String(_)
                | Ref::Comment(_) => 0,
            })
            .sum();
        self.text.len()
            + size_of_val(&*self.starts)
            + size_of_val(&*self.tokens)
            + size_of_val(&*self.refs)
            + size_of_val(&*self.said)
            + size_of_val(&*self.defs)
            + size_of_val(&*self.instr_lines)
            + size_of_val(&*self.instr_vas)
            + size_of_val(&*self.blocks)
            + self.origins.as_ref().map_or(0, |(_, o)| o.bytes())
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

    /// Marks the open line as showing the instruction at `va`, when the
    /// sink records addresses.
    ///
    /// # Arguments
    ///
    /// * `va` - The instruction's address.
    fn at(&mut self, _va: u64) {}

    /// Marks the open line as written from `block`, when the sink records
    /// blocks.
    ///
    /// # Arguments
    ///
    /// * `block` - The block, with the function whose listing writes it.
    fn block(&mut self, _block: LineBlock) {}

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
    /// The lines marked as showing an instruction, in line order.
    instr_lines: Vec<u32>,
    /// The address of the instruction each of those lines shows.
    instr_vas: Vec<u64>,
    /// The runs of lines marked as written from one block, in line order.
    blocks: Vec<BlockRun>,
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

    fn at(&mut self, va: u64) {
        match u32::try_from(self.starts.len()) {
            Ok(line) if self.instr_lines.last().is_none_or(|&l| l < line) => {
                self.instr_lines.push(line);
                self.instr_vas.push(va);
            }
            Ok(_) => {}
            Err(_) => self.over = true,
        }
    }

    fn block(&mut self, block: LineBlock) {
        let Ok(line) = u32::try_from(self.starts.len()) else {
            self.over = true;
            return;
        };
        let to = line.saturating_add(1);
        match self.blocks.last_mut() {
            Some(r) if r.to > line => {}
            Some(r) if r.to == line && r.block == block => r.to = to,
            _ => self.blocks.push(BlockRun {
                from: line,
                to,
                block,
            }),
        }
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
            said: Box::default(),
            defs,
            unlinked,
            ordered: self.instr_vas.is_sorted(),
            instr_lines: self.instr_lines.into_boxed_slice(),
            instr_vas: self.instr_vas.into_boxed_slice(),
            blocks: self.blocks.into_boxed_slice(),
            origins: None,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::{Builder, Kind, Ref, Sink, Unlinked};

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

    /// Builds a view of `lines` one-token lines, marking the first `marked`
    /// of them as showing an instruction.
    ///
    /// # Arguments
    ///
    /// * `lines` - How many lines.
    /// * `marked` - How many of them show an instruction.
    ///
    /// # Panics
    ///
    /// When the view is refused, which a small one never is.
    fn listing(lines: u64, marked: u64) -> super::View {
        let mut b = Builder::default();
        for va in 0..lines {
            if va < marked {
                Sink::at(&mut b, 0x1000 + va);
            }
            b.put("x", Kind::Text, None);
            b.end_line();
        }
        b.finish(Unlinked::default()).expect("a small view")
    }

    /// Each line that shows an instruction costs the view 12 bytes, its
    /// line and its address with no padding, and a view of no listing
    /// costs nothing for them.
    ///
    /// # Panics
    ///
    /// When the table holds more than 12 bytes per entry.
    #[test]
    fn an_instruction_line_costs_twelve_bytes() {
        let (none, three) = (listing(4, 0), listing(4, 3));
        assert_eq!(three.bytes() - none.bytes(), 3 * 12);
        assert_eq!(three.address(2), Some(0x1002));
        assert_eq!(three.address(3), None);
    }

    /// A listing whose addresses run out of order, as overlapping blocks
    /// can lay them, still finds the first line of each address.
    ///
    /// # Panics
    ///
    /// When [`super::View::line_of`] searches an unordered table as if it
    /// were ordered, or finds a later line.
    #[test]
    fn line_of_finds_the_first_line_when_addresses_run_out_of_order() {
        let mut b = Builder::default();
        for va in [0x10, 0x18, 0x12, 0x18] {
            Sink::at(&mut b, va);
            b.put("x", Kind::Text, None);
            b.end_line();
        }
        let v = b.finish(Unlinked::default()).expect("a small view");
        assert_eq!(v.line_of(0x10), Some(0));
        assert_eq!(v.line_of(0x18), Some(1));
        assert_eq!(v.line_of(0x12), Some(2));
        assert_eq!(v.line_of(0x11), None);
        assert_eq!(v.address(3), Some(0x18));
    }
}
