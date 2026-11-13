//! A function's text read back as lines of typed tokens ([`View`]), each
//! name linked only to the one thing it can name that a fact of the engine,
//! made apart from the text, bears out.
//!
//! The text is the structurer's, rewritten by the text passes, so no token
//! made before them could survive them: the view reads the finished text.
//! Every byte lands in a piece ([`scan`]), and a name is one piece with its
//! scopes and template arguments ([`ctext::name_end`]).
//!
//! Each line has a role ([`Role`]): the header comments, whose
//! `// signature: ` line is C after its prefix; the unit's items
//! (prototypes, function-like `#define`s, one-line `static inline` bodies,
//! struct definitions, tables, typedefs, other `#define`s); the
//! declarations of the locals; the body. A name resolves in its line's
//! scope: the function's own (its signature's parameters and the locals it
//! declares), a prototype's, a macro's or a `static inline` body's own
//! parameters, a struct's members, and the file's (what the unit declares,
//! and the binary's functions, imports and data as the text spells them).
//! A struct tag is a type wherever it stands, and a piece the text cut from
//! a longer name (`Foo::bar` of `Foo::bar.part.0`, `foo` of
//! `foo()::{lambda}`, `close` of `@selector(close)`, `Widget` of
//! `p->~Widget`) is looked up nowhere.
//!
//! A name links only when exactly one thing spells it ([`Named`]) and a
//! fact agrees ([`Facts`]): a function is one the code is, calls,
//! references, or reaches through a resolved virtual call; an import (one
//! library's symbol, at each of its slots and behind each stub that jumps
//! through one) is one the code references or calls a stub of; a label's
//! address starts a block of the function; a `g<bits>_<hex>` global's
//! address is mapped and referenced; a variable is declared in the scope
//! that reads it; a type is declared in the unit or the overlay. A name two
//! things spell, or one no fact bears out, keeps its kind and is counted
//! ([`Unlinked`]).
//!
//! Reading notes no overlay fact beyond its text's and the spellings it
//! looked up ([`reads`]): the whole-program indexes are taken unnoted, the
//! text is noted as the body its names were looked up in, and a name looked
//! up with no `(` after it is noted as if one followed. A view of an answer
//! ([`view`]) reads what the answer read as well, so it is kept across an
//! edit exactly when its answer is.

use std::cell::OnceCell;
use std::collections::{BTreeMap, BTreeSet};
use std::ops::Range;
use std::sync::Arc;

use super::lexer::{Lex, Piece, scan};
use super::line::{header_len, is_global_name, label_address};
use super::{
    Detail, answer, cir, ctext, declarations_end, defs, expr_render, helper, unit, virtual_callees,
};
use crate::analysis::attributes::global_addr;
use crate::analysis::{Analysis, Function, Overlay, name_of, reads};
use crate::cancel::Cancel;
use crate::program::{Program, SymbolKind};
use crate::view::{Builder, Kind, Ref, Unlinked, View};

/// The prefix of the signature line, a comment before the C it holds.
const SIGNATURE: &str = "// signature: ";

/// One piece of a line and the bytes it spans ([`split`]).
type Spanned = (Piece, Range<usize>);

/// What a line of a function's text is, which says how its names read.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Role {
    /// A header comment.
    Header,
    /// The `// signature: ` line: C after its prefix, which defines the
    /// function and its parameters.
    Signature,
    /// An `extern` prototype: its parameters are its own and no function's
    /// variables.
    Prototype,
    /// A function-like `#define`: its parameters are its own.
    Macro,
    /// A one-line `static inline` definition: its parameters and its body
    /// are its function's.
    Inline,
    /// A struct definition: its tag, its members' types and its members.
    Struct,
    /// Another item of the unit: a table, a typedef, a `#define`, an
    /// `extern` object.
    Item,
    /// A declaration of the function's locals.
    Declaration,
    /// A line of the body.
    Body,
}

/// What a spelling names among the things the file's scope holds.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Named<'a> {
    /// Nothing.
    Nothing,
    /// One function, by its entry.
    Function(u64),
    /// One import, by its slots, sorted.
    Import(&'a [u64]),
    /// One global whose address the spelling holds, `g<bits>_<hex>`.
    Address(u64),
    /// One global by its name: a data symbol, or an address the user named.
    Data,
    /// More than one thing.
    Many,
}

/// What the engine shows of one function apart from its text: what a link
/// on its lines must agree with.
#[derive(Debug)]
struct Facts<'a> {
    /// The function.
    function: &'a Function,
    /// The targets of its reference sites.
    refs: BTreeSet<u64>,
    /// The functions its callees' linkage stubs are bound to.
    bound: BTreeSet<u64>,
    /// The import slots its callees that are import stubs jump through.
    stubs: BTreeSet<u64>,
    /// The functions its virtual calls resolve to, sorted: read from its
    /// decompilation the first time a link needs them.
    virtual_callees: OnceCell<Vec<u64>>,
}

impl<'a> Facts<'a> {
    /// Returns the facts of the function whose entry is `entry`.
    ///
    /// # Arguments
    ///
    /// * `analysis` - The analysis it is in.
    /// * `entry` - The function's entry.
    ///
    /// # Returns
    ///
    /// The facts, `None` when no function starts at `entry`.
    fn of(analysis: &'a Analysis, entry: u64) -> Option<Self> {
        let function = analysis.function(entry)?;
        let callees = function
            .callees
            .iter()
            .filter_map(|&c| analysis.function(c));
        Some(Self {
            function,
            refs: analysis
                .refs_from(entry)
                .into_iter()
                .map(|(t, _)| t)
                .collect(),
            bound: callees.clone().filter_map(|g| g.bound).collect(),
            stubs: callees.filter_map(|g| g.thunk).collect(),
            virtual_callees: OnceCell::new(),
        })
    }

    /// Tells whether a block of the function starts at `va`.
    ///
    /// # Arguments
    ///
    /// * `va` - The address.
    fn starts_block(&self, va: u64) -> bool {
        self.function
            .blocks
            .binary_search_by_key(&va, |b| b.start)
            .is_ok()
    }
}

/// What a text's unit items and declarations declare, read before its
/// lines are.
#[derive(Debug, Default)]
struct Declared<'t> {
    /// The function's parameters and the locals it declares.
    vars: BTreeSet<&'t str>,
    /// The functions the unit declares: prototypes, `static inline`
    /// bodies, function-like `#define`s.
    functions: BTreeSet<&'t str>,
    /// The objects the unit declares: `extern` data and tables.
    data: BTreeSet<&'t str>,
    /// The types the unit declares (typedefs, `#define`d aliases, struct
    /// tags), each with the line that declares it.
    types: BTreeMap<&'t str, usize>,
    /// The functions the unit defines `static inline`, each with its line.
    inline: BTreeMap<&'t str, usize>,
}

/// The scope a line's names resolve in.
#[derive(Debug)]
struct Scope<'s> {
    /// The function whose variables its names are, `None` where they are
    /// no function's of the binary (a prototype's, a macro's, a helper's).
    owner: Option<u64>,
    /// The variables it declares, or on a struct line the members.
    vars: &'s BTreeSet<&'s str>,
    /// The facts its links must agree with, `None` for a helper's line.
    facts: Option<&'s Facts<'s>>,
    /// Which of the line's pieces were cut from a non-C name or selector
    /// ([`cut_pieces`]).
    cut: &'s [bool],
}

/// Where a name stands: its line, which piece it is, the scope it reads in.
#[derive(Debug)]
struct At<'p> {
    /// The line's index in the text.
    i: usize,
    /// What the line is.
    role: Role,
    /// The line.
    line: &'p str,
    /// Its pieces ([`split`]).
    pieces: &'p [Spanned],
    /// The name's piece.
    k: usize,
    /// The scope it resolves in.
    scope: &'p Scope<'p>,
}

/// What reading a text counts and looks up as it goes.
#[derive(Debug, Default)]
struct Tally {
    /// The names left unlinked.
    unlinked: Unlinked,
    /// The names looked up where no `(` follows them, which the text's own
    /// body does not note ([`reads::note_body`]).
    looked: BTreeSet<String>,
    /// Each `(function, slots[0])` import lookup already resolved.
    imports: BTreeMap<(u64, u64), Option<u64>>,
}

/// What reading one function's text needs, read once before its lines.
#[derive(Debug)]
struct Reader<'a> {
    /// The loaded image.
    program: &'a Program,
    /// Its analysis.
    analysis: &'a Analysis,
    /// The names in force.
    overlay: &'a Overlay,
    /// The function's entry.
    entry: u64,
    /// The machine word in bits, which some scalar type names take.
    word: u8,
    /// The function's name as its text spells it.
    own: String,
    /// The functions and data by the names the text spells them with,
    /// taken unnoted ([`unit::index`]).
    index: Arc<unit::Index>,
    /// Each import's spelling, to the imports that go by it ([`imports`]).
    imports: Arc<BTreeMap<String, Vec<Vec<u64>>>>,
    /// Each name the overlay gives an address no function starts at, to
    /// the addresses that go by it ([`renamed`]).
    renamed: Arc<BTreeMap<String, Vec<u64>>>,
    /// What the engine shows of the function.
    facts: Option<Facts<'a>>,
    /// What the text's unit and declarations declare.
    declared: Declared<'a>,
    /// How many header lines the text opens with.
    head: usize,
    /// What each line after the header and up to the body is.
    roles: Vec<Role>,
}

/// Returns a function's text read as lines of typed tokens, each name
/// linked only where exactly one thing spells it and a fact of the engine
/// agrees.
///
/// Any text of the function reads, an answer's or a plain one; every byte
/// lands in a token, so the view spells the text back ([`View::spell`]).
/// The whole-program indexes the names are looked up in are taken unnoted,
/// and the text is noted as the body they were looked up in
/// ([`reads::note_body`]): a build that takes the view reads no overlay
/// fact its text did not, besides the spellings it looked up.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Its analysis.
/// * `overlay` - Names in force.
/// * `entry` - The function's entry.
/// * `text` - The function's text.
///
/// # Returns
///
/// The view, or `None` when the text reaches 4 GiB, which a view's 32-bit
/// offsets cannot hold, or the caller's cancel flag is raised while it
/// reads ([`Cancel`]).
#[must_use]
pub fn view_of(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    entry: u64,
    text: &str,
) -> Option<View> {
    let lines: Vec<&str> = text.split('\n').collect();
    let reader = Reader::new(program, analysis, overlay, entry, &lines, text);
    let (mut b, mut tally, mut pieces) = (Builder::default(), Tally::default(), Vec::new());
    for (i, line) in lines.iter().enumerate() {
        if Cancel::raised() {
            return None;
        }
        if i > 0 {
            b.end_line();
        }
        reader.line(&mut b, &mut tally, i, line, &mut pieces);
    }
    let view = b.finish(tally.unlinked)?;
    reads::note_body(view.text());
    if !tally.looked.is_empty() {
        let called: String = tally.looked.iter().map(|w| format!("{w}(")).collect();
        reads::note_body(&Arc::from(called));
    }
    Some(view)
}

/// Returns the view of the answer `decompile` gives for one function
/// ([`answer()`] at [`Detail::Full`]), read once per function under the names
/// in force through [`Analysis::derived`].
///
/// The view reads what its answer read and the spellings it looked up
/// ([`view_of`]), so an edit carries it to the new names as it is
/// ([`crate::analysis::Derived::moved`]) exactly when it carries its
/// answer. The memo weighs it without its text, which the noted body
/// already holds.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Its analysis, holding the memo.
/// * `overlay` - Names in force.
/// * `entry` - The function's entry.
///
/// # Returns
///
/// The view, or `None` when the function does not decompile ([`answer()`]),
/// its answer reaches 4 GiB, or the caller's cancel flag is raised
/// ([`Cancel`]).
///
/// # Examples
///
/// ```
/// use borer_engine::analysis::decompile::view::view;
/// use borer_engine::analysis::decompile::{Detail, answer};
/// use borer_engine::analysis::{Analysis, Overlay};
/// use borer_engine::program::Program;
///
/// let program = Program::load(&std::env::current_exe()?)?;
/// let analysis = Analysis::compute(&program);
/// let entry = program.entry.expect("an executable has an entry point");
/// let entry = analysis.function_at(entry).expect("the entry is a function").entry;
/// let overlay = Overlay::default();
/// let shown = view(&program, &analysis, &overlay, entry).expect("decompiles");
/// let text = answer(&program, &analysis, &overlay, entry, Detail::Full);
/// assert_eq!(Some(shown.spell()), text);
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
#[must_use]
pub fn view(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    entry: u64,
) -> Option<Arc<View>> {
    analysis
        .derived
        .get_or_build_item(
            "decompile_view",
            overlay.fingerprint(),
            entry,
            || {
                let text = answer(program, analysis, overlay, entry, Detail::Full)?;
                view_of(program, analysis, overlay, entry, &text).map(Arc::new)
            },
            |v| {
                v.as_deref().map_or(0, |v| {
                    size_of::<View>() + v.bytes().saturating_sub(v.text().len())
                })
            },
        )
        .as_ref()
        .clone()
}

/// Returns each import's name as a call through its slot spells it
/// ([`expr_render::import_spelling`]), to the imports that go by it, each
/// as its slots, read once per analysis.
///
/// An import is one library's symbol: the loader lists one at each of its
/// slots (an ELF import at its GOT and its PLT slot, a Mach-O import at its
/// `__got` and `__la_symbol_ptr` slots), and those are one thing, while two
/// Mach-O libraries exporting the same symbol carry distinct ordinals in
/// [`crate::reloc::Relocs::binds`] and stay apart.
///
/// # Arguments
///
/// * `program` - The loaded image, whose symbols and binds name the imports.
/// * `analysis` - Its analysis, holding the memo.
fn imports(program: &Program, analysis: &Analysis) -> Arc<BTreeMap<String, Vec<Vec<u64>>>> {
    analysis.derived.get_or_build("view_imports", (), || {
        let mut slots: BTreeMap<(Option<i64>, &str), Vec<u64>> = BTreeMap::new();
        for s in program
            .symbols
            .iter()
            .filter(|s| s.kind == SymbolKind::Import && s.addr != 0)
        {
            let ordinal = program.relocs.bound_at(s.addr).map(|b| b.ordinal);
            slots
                .entry((ordinal, s.name.as_str()))
                .or_default()
                .push(s.addr);
        }
        let mut by: BTreeMap<String, Vec<Vec<u64>>> = BTreeMap::new();
        for ((_, name), mut at) in slots {
            at.sort_unstable();
            at.dedup();
            by.entry(expr_render::import_spelling(name))
                .or_default()
                .push(at);
        }
        by
    })
}

/// Returns each name the overlay gives an address no function starts at,
/// to the addresses that go by it in address order, built once per names
/// in force.
///
/// The text spells such an address by the name, so a call through it reads
/// like a call of a function. Building it reads every name; a view takes it
/// unnoted and notes the text it looked names up in.
///
/// # Arguments
///
/// * `analysis` - The analysis, holding the memo.
/// * `overlay` - Names in force.
fn renamed(analysis: &Analysis, overlay: &Overlay) -> Arc<BTreeMap<String, Vec<u64>>> {
    analysis
        .derived
        .get_or_build_named("view_renamed", overlay.names_key(), (), || {
            let mut by: BTreeMap<String, Vec<u64>> = BTreeMap::new();
            for (&at, name) in &overlay.names {
                if analysis.function(at).is_none() {
                    by.entry(name.clone()).or_default().push(at);
                }
            }
            by
        })
}

/// Appends the pieces a view reads from byte `from` of `line` on
/// ([`scan`]).
///
/// A name with its scopes and template arguments reads as one piece
/// ([`ctext::name_end`]), including one opening past ASCII.
///
/// # Arguments
///
/// * `line` - The line or slice to scan.
/// * `from` - Where scanning starts, a character boundary.
/// * `out` - Receives the pieces.
fn split_into(line: &str, from: usize, out: &mut Vec<Spanned>) {
    let mut pieces = scan(line, from);
    while let Some((piece, span)) = pieces.next() {
        let rest = line.get(span.start..).unwrap_or_default();
        let opens = piece == Piece::Token(Lex::Name)
            || (piece == Piece::Token(Lex::Punct) && rest.starts_with(char::is_alphabetic));
        if !opens {
            out.push((piece, span));
            continue;
        }
        let end = span
            .start
            .saturating_add(ctext::name_end(rest))
            .max(span.end);
        if end > span.end {
            pieces = scan(line, end);
        }
        out.push((Piece::Token(Lex::Name), span.start..end));
    }
}

/// Splits a line into the pieces a view reads from byte `from` on
/// ([`split_into`]).
///
/// # Arguments
///
/// * `line` - The line.
/// * `from` - Where its C starts, a character boundary.
/// * `out` - Receives the pieces, emptied first.
fn split(line: &str, from: usize, out: &mut Vec<Spanned>) {
    out.clear();
    split_into(line, from, out);
}

/// Splits a [`Role::Signature`] line after [`SIGNATURE`], keeping `own`
/// whole as one [`Lex::Name`] piece before its parameter list.
///
/// # Arguments
///
/// * `line` - The signature line.
/// * `own` - The function's bare name.
/// * `out` - Receives the pieces, emptied first.
fn split_signature(line: &str, own: &str, out: &mut Vec<Spanned>) {
    let from = SIGNATURE.len();
    let found = (!own.is_empty())
        .then(|| line.get(from..))
        .flatten()
        .and_then(|tail| {
            tail.match_indices(own).find_map(|(rel, _)| {
                let at = from.saturating_add(rel);
                let end = at.saturating_add(own.len());
                let before = line.get(from..at)?;
                let after = line.get(end..)?;
                let ok_before = !before.contains('(')
                    && (before.is_empty() || before.ends_with([' ', '\t', '*', '&']));
                (ok_before && after.starts_with('(')).then_some((at, end))
            })
        });
    let Some((at, end)) = found else {
        split(line, from, out);
        return;
    };
    out.clear();
    if let Some(prefix) = line.get(..at) {
        split_into(prefix, from, out);
    }
    out.push((Piece::Token(Lex::Name), at..end));
    split_into(line, end, out);
}

/// Returns the text of piece `k` of a line, empty past the last.
///
/// # Arguments
///
/// * `line` - The line.
/// * `pieces` - Its pieces.
/// * `k` - The piece.
fn word<'t>(line: &'t str, pieces: &[Spanned], k: usize) -> &'t str {
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
fn code_before(pieces: &[Spanned], k: usize) -> Option<usize> {
    (0..k).rev().find(|&j| {
        pieces
            .get(j)
            .is_some_and(|(p, _)| !matches!(p, Piece::Space | Piece::Comment))
    })
}

/// Returns the code pieces of a line, no whitespace and no comment, each
/// with its text.
///
/// # Arguments
///
/// * `line` - The line.
/// * `pieces` - Its pieces.
fn code<'t>(line: &'t str, pieces: &[Spanned]) -> Vec<(Piece, &'t str, Range<usize>)> {
    pieces
        .iter()
        .filter(|(p, _)| !matches!(p, Piece::Space | Piece::Comment))
        .map(|(p, s)| (*p, line.get(s.clone()).unwrap_or_default(), s.clone()))
        .collect()
}

/// Tells whether the `{` at `open` and `}` at `close` enclose C syntax on
/// `role` rather than a demangled `{...}` name piece.
///
/// # Arguments
///
/// * `role` - What the line is.
/// * `line` - The line.
/// * `pieces` - Its pieces.
/// * `open` - The `{` piece.
/// * `close` - Its matching `}` piece.
fn c_braces(role: Role, line: &str, pieces: &[Spanned], open: usize, close: usize) -> bool {
    if role == Role::Struct {
        return true;
    }
    if open
        .checked_sub(1)
        .is_some_and(|j| word(line, pieces, j) == "::")
    {
        return false;
    }
    let (mut depth, mut prev_name, mut prev_paren) = (0usize, false, false);
    let (mut semi, mut non_c) = (false, false);
    for (k, (piece, _)) in pieces.iter().enumerate().take(close).skip(open + 1) {
        if matches!(piece, Piece::Space | Piece::Comment) {
            continue;
        }
        let w = word(line, pieces, k);
        non_c |= prev_paren && w == "{";
        if depth == 0 {
            semi |= w == ";";
            let is_name = *piece == Piece::Token(Lex::Name);
            non_c |= prev_name && is_name;
            prev_name = is_name;
        }
        prev_paren = w == "(";
        depth = match w {
            "(" | "[" | "{" => depth + 1,
            ")" | "]" | "}" => depth.saturating_sub(1),
            _ => depth,
        };
    }
    if semi {
        return true;
    }
    if non_c {
        return false;
    }
    if role == Role::Inline
        && code_before(pieces, open).is_some_and(|j| word(line, pieces, j) == ")")
    {
        return true;
    }
    if matches!(role, Role::Item | Role::Declaration)
        && (0..open).any(|j| {
            pieces
                .get(j)
                .is_some_and(|(p, _)| *p == Piece::Token(Lex::Punct))
                && word(line, pieces, j) == "="
        })
    {
        return true;
    }
    open.checked_sub(1).is_some_and(|j| {
        word(line, pieces, j) == ")"
            && code_before(pieces, j).is_some_and(|p| word(line, pieces, p) != "*")
    })
}

/// Returns a mask over `pieces` marking each piece inside a non-C name or
/// selector span.
///
/// Those spans are a `(...)::` qualifier, `@selector(...)`, an Objective-C
/// `-[...]` or `+[...]` method name, and any non-C `{...}` piece
/// ([`c_braces`]).
///
/// # Arguments
///
/// * `role` - What the line is.
/// * `line` - The line.
/// * `pieces` - Its pieces.
fn cut_pieces(role: Role, line: &str, pieces: &[Spanned]) -> Vec<bool> {
    let len = pieces.len();
    let mut cut = vec![false; len];
    let mut mark = |r: Range<usize>| {
        if let Some(slice) = cut.get_mut(r) {
            slice.fill(true);
        }
    };
    let (mut parens, mut brackets, mut braces) = (Vec::new(), Vec::new(), Vec::new());
    for (k, (piece, _)) in pieces.iter().enumerate() {
        if *piece != Piece::Token(Lex::Punct) {
            continue;
        }
        match word(line, pieces, k) {
            "(" => {
                let selector = code_before(pieces, k).is_some_and(|s| {
                    pieces
                        .get(s)
                        .is_some_and(|(p, _)| *p == Piece::Token(Lex::Name))
                        && word(line, pieces, s) == "selector"
                        && s.checked_sub(1)
                            .is_some_and(|a| word(line, pieces, a) == "@")
                });
                parens.push((k, selector));
            }
            ")" => {
                if let Some((open, selector)) = parens.pop() {
                    if selector {
                        mark(open..k + 1);
                    } else if word(line, pieces, k + 1) == "::" {
                        mark(open.saturating_sub(1)..k + 1);
                    }
                }
            }
            "[" => {
                let objc = k.checked_sub(1).is_some_and(|j| {
                    pieces
                        .get(j)
                        .is_some_and(|(p, _)| *p == Piece::Token(Lex::Punct))
                        && matches!(word(line, pieces, j), "-" | "+")
                });
                brackets.push((k, objc));
            }
            "]" => {
                if let Some((open, true)) = brackets.pop() {
                    mark(open..k + 1);
                }
            }
            "{" => braces.push(k),
            "}" => {
                if let Some(open) = braces.pop()
                    && !c_braces(role, line, pieces, open, k)
                {
                    mark(open..k + 1);
                }
            }
            _ => {}
        }
    }
    for (open, selector) in parens {
        if selector {
            mark(open..len);
        }
    }
    for (open, objc) in brackets {
        if objc {
            mark(open..len);
        }
    }
    for open in braces {
        if open
            .checked_sub(1)
            .is_some_and(|j| word(line, pieces, j) == "::")
        {
            mark(open..len);
        }
    }
    cut
}

/// Returns the names a parameter list declares: the last word of each
/// parameter of two words or more, when it is a name.
///
/// `uint64_t *a8` declares `a8`; `uint64_t`, `FILE *` and `...` declare
/// nothing.
///
/// # Arguments
///
/// * `line` - A prototype, a `static inline` definition or the signature.
/// * `pieces` - Its pieces; the list is the first `(` outside `[...]` and
///   `{...}`.
fn params<'t>(line: &'t str, pieces: &[Spanned]) -> BTreeSet<&'t str> {
    let mut names = BTreeSet::new();
    let mut brackets = 0usize;
    let mut list = code(line, pieces).into_iter().skip_while(|(_, w, _)| {
        let open = *w == "(" && brackets == 0;
        brackets = match *w {
            "[" | "{" => brackets + 1,
            "]" | "}" => brackets.saturating_sub(1),
            _ => brackets,
        };
        !open
    });
    if list.next().is_none() {
        return names;
    }
    let (mut depth, mut words, mut last) = (0usize, 0usize, None);
    for (piece, w, _) in list {
        if depth == 0 && matches!(w, "," | ")") {
            if words > 1 {
                names.extend(last);
            }
            if w == ")" {
                break;
            }
            (words, last) = (0, None);
            continue;
        }
        depth = match w {
            "(" | "[" | "{" => depth + 1,
            ")" | "]" | "}" => depth.saturating_sub(1),
            _ => depth,
        };
        words += 1;
        last = (piece == Piece::Token(Lex::Name)).then_some(w);
    }
    names
}

/// Returns the names a function-like `#define`'s parameter list holds.
///
/// # Arguments
///
/// * `line` - The `#define` line.
/// * `pieces` - Its pieces.
fn macro_params<'t>(line: &'t str, pieces: &[Spanned]) -> BTreeSet<&'t str> {
    code(line, pieces)
        .into_iter()
        .skip_while(|(_, w, _)| *w != "(")
        .skip(1)
        .take_while(|(_, w, _)| *w != ")")
        .filter(|(p, ..)| *p == Piece::Token(Lex::Name))
        .map(|(_, w, _)| w)
        .collect()
}

/// Returns the members a one-line struct definition declares: the
/// declarators between its braces ([`declarators`]).
///
/// # Arguments
///
/// * `code` - The line's code pieces ([`code`]).
fn members<'t>(code: &[(Piece, &'t str, Range<usize>)]) -> BTreeSet<&'t str> {
    let mut out = BTreeSet::new();
    let open = code.iter().position(|(_, w, _)| *w == "{");
    let close = code.iter().rposition(|(_, w, _)| *w == "}");
    if let (Some(open), Some(close)) = (open, close) {
        declarators(
            code.get(open.saturating_add(1)..close).unwrap_or_default(),
            &mut out,
        );
    }
    out
}

/// Adds the names declarations declare: each declarator's last name
/// outside brackets, or the one a function pointer's `(*name)` holds, up
/// to each `,` or `;`.
///
/// # Arguments
///
/// * `code` - The declarations' code pieces ([`code`]).
/// * `out` - Receives the names.
fn declarators<'t>(code: &[(Piece, &'t str, Range<usize>)], out: &mut BTreeSet<&'t str>) {
    let (mut depth, mut name, mut held, mut prev) = (0usize, None, None, "");
    for (piece, w, _) in code {
        match *w {
            "," | ";" if depth == 0 => out.extend(held.take().or(name.take())),
            "(" | "[" => depth += 1,
            ")" | "]" => depth = depth.saturating_sub(1),
            _ if *piece == Piece::Token(Lex::Name) && depth == 0 => name = Some(*w),
            _ if *piece == Piece::Token(Lex::Name) && prev == "*" && held.is_none() => {
                held = Some(*w);
            }
            _ => {}
        }
        prev = *w;
    }
}

/// Returns the name a declaration of one object or type declares: the one
/// before its first `[`, or else the last outside parentheses that no `(`
/// follows, before its `=` or `;`.
///
/// # Arguments
///
/// * `code` - The line's code pieces ([`code`]).
fn declared_name<'t>(code: &[(Piece, &'t str, Range<usize>)]) -> Option<&'t str> {
    let end = code
        .iter()
        .position(|(_, w, _)| matches!(*w, "=" | ";"))
        .unwrap_or(code.len());
    let head = code.get(..end)?;
    if let Some(k) = head.iter().position(|(_, w, _)| *w == "[") {
        let (piece, w, _) = head.get(k.checked_sub(1)?)?;
        return (*piece == Piece::Token(Lex::Name)).then_some(*w);
    }
    let mut depth = 0usize;
    let mut found = None;
    for (k, (piece, w, _)) in head.iter().enumerate() {
        depth = match *w {
            "(" => depth + 1,
            ")" => depth.saturating_sub(1),
            _ => depth,
        };
        let called = head.get(k + 1).is_some_and(|(_, n, _)| *n == "(");
        if depth == 0 && *piece == Piece::Token(Lex::Name) && !called {
            found = Some(*w);
        }
    }
    found
}

impl<'t> Declared<'t> {
    /// Reads what one line among the unit's items and the declarations
    /// declares.
    ///
    /// # Arguments
    ///
    /// * `i` - The line's index in the text.
    /// * `line` - The line.
    /// * `pieces` - Its pieces ([`split`]).
    ///
    /// # Returns
    ///
    /// What the line is.
    fn read(&mut self, i: usize, line: &'t str, pieces: &[Spanned]) -> Role {
        let code = code(line, pieces);
        let named = |k: usize| {
            code.get(k)
                .filter(|(p, ..)| *p == Piece::Token(Lex::Name))
                .map(|(_, w, _)| *w)
        };
        let mut brackets = 0usize;
        let open = code.iter().position(|(_, w, _)| {
            let found = *w == "(" && brackets == 0;
            brackets = match *w {
                "[" | "{" => brackets + 1,
                "]" | "}" => brackets.saturating_sub(1),
                _ => brackets,
            };
            found
        });
        let called = open.and_then(|k| {
            let n = k.checked_sub(1)?;
            let name = named(n)?;
            let glued = n.checked_sub(1).is_some_and(|j| {
                code.get(j).is_some_and(|(_, p, s)| {
                    matches!(*p, ":" | "~") && Some(s.end) == code.get(n).map(|(_, _, ns)| ns.start)
                })
            });
            (!glued).then_some(name)
        });
        if line.starts_with("static inline ") {
            if let Some(name) = called {
                self.functions.insert(name);
                self.inline.insert(name, i);
            }
            return Role::Inline;
        }
        if let Some(name) = named(2).filter(|_| line.starts_with("#define ")) {
            let after = code.get(2).map(|(_, _, s)| s.end);
            if code
                .get(3)
                .is_some_and(|(_, w, s)| *w == "(" && Some(s.start) == after)
            {
                self.functions.insert(name);
                return Role::Macro;
            }
            if named(3).is_some() {
                self.types.insert(name, i);
            }
            return Role::Item;
        }
        if line.starts_with("extern ") {
            if open.is_some() {
                self.functions.extend(called);
                return Role::Prototype;
            }
            self.data.extend(declared_name(&code));
            return Role::Item;
        }
        if line.starts_with("typedef ") {
            if let Some(name) = declared_name(&code) {
                self.types.insert(name, i);
            }
            return Role::Item;
        }
        if defs::defines(line) {
            if let Some(tag) = named(1) {
                self.types.insert(tag, i);
            }
            return Role::Struct;
        }
        if line.starts_with("static ") {
            self.data.extend(declared_name(&code));
            return Role::Item;
        }
        if helper::defines(line) {
            return Role::Item;
        }
        declarators(&code, &mut self.vars);
        Role::Declaration
    }
}

impl<'a> Reader<'a> {
    /// Reads what a text's lines are and what its unit and declarations
    /// declare, and takes the indexes its names are looked up in.
    ///
    /// # Arguments
    ///
    /// * `program` - The loaded image.
    /// * `analysis` - Its analysis.
    /// * `overlay` - Names in force.
    /// * `entry` - The function's entry.
    /// * `lines` - The text's lines.
    /// * `text` - The text.
    fn new(
        program: &'a Program,
        analysis: &'a Analysis,
        overlay: &'a Overlay,
        entry: u64,
        lines: &[&'a str],
        text: &str,
    ) -> Self {
        let (index, imports, renamed) = reads::unnoted(|| {
            (
                unit::index(program, analysis, overlay),
                imports(program, analysis),
                renamed(analysis, overlay),
            )
        });
        let own = expr_render::bare(&name_of(analysis, overlay, entry)).into_owned();
        let head = header_len(lines);
        let decls = declarations_end(text).map_or(head, |end| end.max(head));
        let mut declared = Declared::default();
        let mut pieces = Vec::new();
        if let Some(sig) = lines
            .get(..head)
            .and_then(|h| h.iter().find(|l| l.starts_with(SIGNATURE)).copied())
        {
            split_signature(sig, &own, &mut pieces);
            declared.vars.extend(params(sig, &pieces));
        }
        let mut roles = Vec::with_capacity(decls.saturating_sub(head));
        for (i, line) in lines.iter().copied().enumerate().take(decls).skip(head) {
            split(line, 0, &mut pieces);
            roles.push(declared.read(i, line, &pieces));
        }
        Self {
            program,
            analysis,
            overlay,
            entry,
            word: if program.is_64 { 64 } else { 32 },
            own,
            index,
            imports,
            renamed,
            facts: Facts::of(analysis, entry),
            declared,
            head,
            roles,
        }
    }

    /// Returns what line `i` is.
    ///
    /// # Arguments
    ///
    /// * `i` - The line's index in the text.
    /// * `line` - The line.
    fn role(&self, i: usize, line: &str) -> Role {
        if i < self.head {
            return if line.starts_with(SIGNATURE) {
                Role::Signature
            } else {
                Role::Header
            };
        }
        i.checked_sub(self.head)
            .and_then(|k| self.roles.get(k))
            .copied()
            .unwrap_or(Role::Body)
    }

    /// Puts one line's pieces into the view, each with its kind and its
    /// link.
    ///
    /// # Arguments
    ///
    /// * `b` - The view being built.
    /// * `tally` - What the reading counts.
    /// * `i` - The line's index in the text.
    /// * `line` - The line.
    /// * `pieces` - A buffer for its pieces.
    fn line(
        &self,
        b: &mut Builder,
        tally: &mut Tally,
        i: usize,
        line: &str,
        pieces: &mut Vec<Spanned>,
    ) {
        let role = self.role(i, line);
        if role == Role::Signature {
            b.put(SIGNATURE, Kind::Comment, None);
            split_signature(line, &self.own, pieces);
        } else {
            split(line, 0, pieces);
        }
        let pieces: &[Spanned] = pieces;
        let (line_vars, owner) = match role {
            Role::Inline => (params(line, pieces), self.inline_owner(line, pieces)),
            Role::Prototype => (params(line, pieces), None),
            Role::Macro => (macro_params(line, pieces), None),
            Role::Struct => (members(&code(line, pieces)), None),
            Role::Signature | Role::Declaration | Role::Body => (BTreeSet::new(), Some(self.entry)),
            Role::Header | Role::Item => (BTreeSet::new(), None),
        };
        let inline = owner
            .filter(|_| role == Role::Inline)
            .and_then(|g| Facts::of(self.analysis, g));
        let cut = cut_pieces(role, line, pieces);
        let scope = Scope {
            owner,
            vars: if matches!(role, Role::Signature | Role::Declaration | Role::Body) {
                &self.declared.vars
            } else {
                &line_vars
            },
            facts: if role == Role::Inline {
                inline.as_ref()
            } else {
                self.facts.as_ref()
            },
            cut: &cut,
        };
        for (k, (piece, span)) in pieces.iter().enumerate() {
            let (kind, link, defines) = match piece {
                Piece::Space => (Kind::Space, None, false),
                Piece::Comment => (Kind::Comment, None, false),
                Piece::Token(Lex::Number) => (Kind::Number, None, false),
                Piece::Token(Lex::Literal) => (Kind::String, None, false),
                Piece::Token(Lex::Punct) => (Kind::Punct, None, false),
                Piece::Token(Lex::Name) => {
                    let at = At {
                        i,
                        role,
                        line,
                        pieces,
                        k,
                        scope: &scope,
                    };
                    self.name(&at, tally)
                }
            };
            b.put(line.get(span.clone()).unwrap_or_default(), kind, link);
            if defines {
                b.define();
            }
        }
    }

    /// Returns the function a `static inline` line defines: the one thing
    /// its name spells, when that is a function.
    ///
    /// # Arguments
    ///
    /// * `line` - The line.
    /// * `pieces` - Its pieces.
    ///
    /// # Returns
    ///
    /// The function's entry, `None` for a helper no function of the binary
    /// is.
    fn inline_owner(&self, line: &str, pieces: &[Spanned]) -> Option<u64> {
        let open = pieces
            .iter()
            .position(|(_, s)| line.get(s.clone()) == Some("("))?;
        match self.named(word(line, pieces, code_before(pieces, open)?)) {
            Named::Function(e) => Some(e),
            Named::Nothing | Named::Import(_) | Named::Address(_) | Named::Data | Named::Many => {
                None
            }
        }
    }

    /// Returns a name's kind, its link and whether its line defines what it
    /// links to.
    ///
    /// The kinds go in order: a member after `->` or `.`; a label where a
    /// label stands; a scalar type; a keyword; a struct tag; a variable of
    /// the scope, or a member on a struct line; a type the unit declares,
    /// or any other name on a struct line; then what the name is looked up
    /// as ([`Reader::looked_up`]).
    ///
    /// # Arguments
    ///
    /// * `at` - Where the name stands.
    /// * `tally` - What the reading counts.
    fn name(&self, at: &At<'_>, tally: &mut Tally) -> (Kind, Option<Ref>, bool) {
        let w = word(at.line, at.pieces, at.k);
        let prev = code_before(at.pieces, at.k).map(|j| word(at.line, at.pieces, j));
        let next = word(at.line, at.pieces, at.k.saturating_add(1));
        if matches!(prev, Some("->" | ".")) {
            return (Kind::Field, None, false);
        }
        if let Some(va) = label_address(w)
            && (next == ":" || prev == Some("goto"))
        {
            let link = at.scope.facts.filter(|f| f.starts_block(va));
            return (Kind::Label, link.map(|_| Ref::Address(va)), next == ":");
        }
        if ctext::named_type(w, self.word).is_some() {
            return (Kind::Type, None, false);
        }
        let directive = code_before(at.pieces, at.k).is_some_and(|j| {
            word(at.line, at.pieces, j) == "#" && code_before(at.pieces, j).is_none()
        });
        if directive
            || cir::KEYWORDS.contains(&w)
            || unit::C_WORDS.contains(&w)
            || (at.role == Role::Inline && w == "inline")
        {
            return (Kind::Keyword, None, false);
        }
        if matches!(prev, Some("struct" | "union" | "enum")) {
            return self.typed(w, at.i);
        }
        if at.scope.vars.contains(w) {
            if at.role == Role::Struct {
                return (Kind::Field, None, false);
            }
            let link = at.scope.owner.map(|function| Ref::Variable {
                function,
                name: w.into(),
            });
            let declares = matches!(at.role, Role::Signature | Role::Inline | Role::Declaration);
            return (Kind::Variable, link, declares);
        }
        if at.role == Role::Struct || self.declared.types.contains_key(w) {
            return self.typed(w, at.i);
        }
        self.looked_up(w, at, tally)
    }

    /// Returns a type's name as a [`Kind::Type`] token: linked when the
    /// unit or the overlay declares it, and defined on the line that
    /// declares it.
    ///
    /// # Arguments
    ///
    /// * `w` - The name.
    /// * `i` - Its line's index in the text.
    fn typed(&self, w: &str, i: usize) -> (Kind, Option<Ref>, bool) {
        let here = self.declared.types.get(w).copied();
        let known = here.is_some() || self.overlay.types.contains_key(w);
        (
            Kind::Type,
            known.then(|| Ref::Type(w.into())),
            here == Some(i),
        )
    }

    /// Returns what a name no scope declares is looked up as: a function,
    /// an import or a global, or a type the overlay states, else text.
    ///
    /// A piece cut from a longer name ([`Reader::cut`]) is looked up
    /// nowhere. A name looked up with no `(` after it is noted as if one
    /// followed, so an edit that renames anything to or from it lets the
    /// view go.
    ///
    /// # Arguments
    ///
    /// * `w` - The name.
    /// * `at` - Where it stands.
    /// * `tally` - What the reading counts.
    fn looked_up(&self, w: &str, at: &At<'_>, tally: &mut Tally) -> (Kind, Option<Ref>, bool) {
        if self.cut(at, w) {
            return (Kind::Text, None, false);
        }
        let call = word(at.line, at.pieces, at.k.saturating_add(1)) == "(";
        if !call && !tally.looked.contains(w) {
            tally.looked.insert(w.to_owned());
        }
        let found = if self.declared.functions.contains(w) || w == self.own {
            Kind::Function
        } else if is_global_name(w)
            || self.declared.data.contains(w)
            || self.index.data.contains_key(w)
            || self.renamed.contains_key(w)
        {
            Kind::Global
        } else {
            Kind::Text
        };
        let named = self.named(w);
        if named == Named::Nothing && found == Kind::Text && self.overlay.types.contains_key(w) {
            return (Kind::Type, Some(Ref::Type(w.into())), false);
        }
        let many = if found == Kind::Text && call {
            Kind::Function
        } else {
            found
        };
        let (kind, link) = self.link(named, found, many, at.scope.facts, tally);
        let defines = link.as_ref().is_some_and(|r| {
            (*r == Ref::Function(self.entry) && at.role == Role::Signature)
                || (at.role == Role::Inline && self.declared.inline.get(w) == Some(&at.i))
        });
        (kind, link, defines)
    }

    /// Returns what the file's scope spells as `w`, stopping at the second
    /// thing that goes by it.
    ///
    /// Those things are the binary's functions under the names in force,
    /// its imports as a call through one of their slots spells them (one
    /// import with its stubs: a function that only jumps through the
    /// import's slot is that import), its data symbols, the addresses no
    /// function starts at the user named, and the address a
    /// `g<bits>_<hex>` name holds.
    ///
    /// # Arguments
    ///
    /// * `w` - The spelling.
    fn named(&self, w: &str) -> Named<'_> {
        if self.index.shared.contains(w) {
            return Named::Many;
        }
        let own_import = w
            .strip_prefix("__imp_")
            .filter(|r| *r == self.own)
            .and_then(|r| self.imports.get(r));
        let imports: Vec<&[u64]> = (w != self.own)
            .then(|| self.imports.get(w))
            .flatten()
            .into_iter()
            .chain(own_import)
            .flatten()
            .map(Vec::as_slice)
            .take(2)
            .collect();
        let function = self.index.functions.get(w).copied();
        let stub = function
            .and_then(|e| self.analysis.function(e)?.thunk)
            .is_some_and(|s| imports.iter().any(|g| g.binary_search(&s).is_ok()));
        let data = self.index.data.get(w).copied();
        let renamed = self.renamed.get(w).map_or(&[][..], Vec::as_slice);
        let mut found = function
            .filter(|_| !stub)
            .map(Named::Function)
            .into_iter()
            .chain(imports.iter().copied().map(Named::Import))
            .chain(data.map(|_| Named::Data))
            .chain(
                renamed
                    .iter()
                    .filter(|&&at| Some(at) != data)
                    .map(|_| Named::Data),
            )
            .chain(global_addr(w).map(Named::Address));
        match (found.next(), found.next()) {
            (None, _) => Named::Nothing,
            (Some(one), None) => one,
            (Some(_), Some(_)) => Named::Many,
        }
    }

    /// Returns a looked-up name's kind and link, counting it when something
    /// goes by it and no link is borne out.
    ///
    /// # Arguments
    ///
    /// * `named` - What the name spells ([`Reader::named`]).
    /// * `found` - Its kind when nothing goes by it: [`Kind::Function`] for
    ///   a function the text declares or its own name, [`Kind::Global`] for
    ///   a global's name, else [`Kind::Text`].
    /// * `many` - Its kind when more than one thing does: a call of a name
    ///   nothing declares is [`Kind::Function`].
    /// * `facts` - What the link must agree with, `None` for a helper's line.
    /// * `tally` - What the reading counts.
    fn link(
        &self,
        named: Named<'_>,
        found: Kind,
        many: Kind,
        facts: Option<&Facts<'_>>,
        tally: &mut Tally,
    ) -> (Kind, Option<Ref>) {
        let (kind, link) = match named {
            Named::Nothing => return (found, None),
            Named::Many => {
                tally.unlinked.ambiguous += 1;
                return (many, None);
            }
            Named::Data => (Kind::Global, None),
            Named::Function(e) => {
                let borne = facts.is_some_and(|f| self.reaches(f, e));
                (Kind::Function, borne.then_some(Ref::Function(e)))
            }
            Named::Import(slots) => {
                let kind = if found == Kind::Global {
                    Kind::Global
                } else {
                    Kind::Function
                };
                let slot = facts.and_then(|f| import_slot(f, slots, tally));
                (kind, slot.map(Ref::Import))
            }
            Named::Address(a) => {
                let refers = facts.is_some_and(|f| f.refs.contains(&a));
                let borne = refers && self.program.section_at(a).is_some();
                (Kind::Global, borne.then_some(Ref::Global(a)))
            }
        };
        if link.is_none() {
            tally.unlinked.uncorroborated += 1;
        }
        (kind, link)
    }

    /// Tells whether a function's facts bear out a link to `e`.
    ///
    /// A link holds when `e` is the function, one of its callees or a
    /// callee's bound linkage target, a reference target, or, for the
    /// function the text is of, a resolved virtual callee.
    ///
    /// # Arguments
    ///
    /// * `f` - The facts.
    /// * `e` - The linked function's entry.
    fn reaches(&self, f: &Facts<'_>, e: u64) -> bool {
        e == f.function.entry
            || f.function.callees.binary_search(&e).is_ok()
            || f.refs.contains(&e)
            || f.bound.contains(&e)
            || (f.function.entry == self.entry
                && f.virtual_callees
                    .get_or_init(|| {
                        virtual_callees(self.program, self.analysis, self.overlay, self.entry)
                    })
                    .binary_search(&e)
                    .is_ok())
    }

    /// Tells whether `w` at `at` is a piece the text cut from a longer name
    /// or selector, which is looked up nowhere.
    ///
    /// A piece is cut when it lies inside a non-C span ([`cut_pieces`]),
    /// runs straight into a literal, `:`, `::`, a trailing `.` or `~`, a
    /// preceding `~` after a name, `->` or `.` or for a `~` destructor in
    /// the index, or punctuation outside C (`\`, `$`, `@`, `#`, `?`, `` ` ``
    /// or past ASCII).
    ///
    /// # Arguments
    ///
    /// * `at` - Where the name stands.
    /// * `w` - The name's spelling.
    fn cut(&self, at: &At<'_>, w: &str) -> bool {
        if at.scope.cut.get(at.k).copied().unwrap_or(false) {
            return true;
        }
        let tilde_before = || {
            let member =
                at.k.checked_sub(2)
                    .and_then(|j| at.pieces.get(j))
                    .is_some_and(|(p, s)| {
                        *p == Piece::Token(Lex::Name)
                            || matches!(at.line.get(s.clone()), Some("->" | "."))
                    });
            if member {
                return true;
            }
            let dtor = format!("~{w}");
            self.index.functions.contains_key(&dtor) || self.index.shared.contains(&dtor)
        };
        let joins = |j: Option<usize>, after: bool| {
            j.and_then(|j| at.pieces.get(j))
                .is_some_and(|(piece, span)| {
                    let p = at.line.get(span.clone()).unwrap_or_default();
                    match piece {
                        Piece::Token(Lex::Literal) => true,
                        Piece::Token(Lex::Punct) => {
                            matches!(p, ":" | "::")
                                || (after && matches!(p, "." | "~"))
                                || (!after && p == "~" && tilde_before())
                                || p.starts_with(|c: char| {
                                    !c.is_ascii() || matches!(c, '\\' | '$' | '@' | '#' | '?' | '`')
                                })
                        }
                        Piece::Space | Piece::Comment | Piece::Token(Lex::Name | Lex::Number) => {
                            false
                        }
                    }
                })
        };
        joins(at.k.checked_sub(1), false) || joins(at.k.checked_add(1), true)
    }
}

/// Returns the lowest slot of `slots` that `f` references or calls a stub
/// of, caching the lookup for `f` in `tally`.
///
/// # Arguments
///
/// * `f` - The function's facts.
/// * `slots` - The import's slots, sorted.
/// * `tally` - Holds the per-import cache.
fn import_slot(f: &Facts<'_>, slots: &[u64], tally: &mut Tally) -> Option<u64> {
    let &first = slots.first()?;
    if let Some(&cached) = tally.imports.get(&(f.function.entry, first)) {
        return cached;
    }
    let held = |s: &u64| f.refs.contains(s) || f.stubs.contains(s);
    let slot = if slots.len() <= f.refs.len().saturating_add(f.stubs.len()) {
        slots.iter().copied().find(held)
    } else {
        f.refs
            .iter()
            .chain(&f.stubs)
            .copied()
            .filter(|s| slots.binary_search(s).is_ok())
            .min()
    };
    tally.imports.insert((f.function.entry, first), slot);
    slot
}
