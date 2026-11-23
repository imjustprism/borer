//! What a hover shows of a referent beyond its name ([`peek`]).
//!
//! A function shows its first lines, a global its bytes as the type
//! applied there or as a hexdump row, an import its declaration with how
//! sure the engine is of the name it was looked up by.
//!
//! Every line is capped at [`PEEK_WIDTH`] characters and a peek at
//! [`PEEK_LINES`] lines, with the count of lines the whole text has, so a
//! cut peek can say what it left out.

use super::super::expr_render::import_spelling;
use super::said;
use crate::analysis::render::typed_tsv;
use crate::analysis::{Analysis, Overlay, bare_name, sdk, typelib};
use crate::hexdump::hex_rows;
use crate::program::Program;
use crate::view::{Ref, Said};

/// Most lines of a referent a peek holds.
pub const PEEK_LINES: usize = 12;

/// Most characters of one peek line; a longer one is cut and ends in `…`.
pub const PEEK_WIDTH: usize = 160;

/// Bytes of an untyped global a peek reads: one hexdump row.
pub const PEEK_BYTES: usize = 16;

/// The first lines of a text, each capped, and how many lines the text has.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Head {
    /// The first [`PEEK_LINES`] lines at most, each at most [`PEEK_WIDTH`]
    /// characters and a closing `…`.
    pub lines: Vec<String>,
    /// Lines the whole text has, at least `lines.len()`.
    pub total: usize,
}

impl Head {
    /// Returns the head of a text of `total` lines read off `lines`.
    ///
    /// # Arguments
    ///
    /// * `total` - Lines the whole text has.
    /// * `lines` - Its lines, in order.
    fn of<'a>(total: usize, lines: impl Iterator<Item = &'a str>) -> Self {
        let lines: Vec<_> = lines.take(PEEK_LINES).map(capped).collect();
        let total = total.max(lines.len());
        Self { lines, total }
    }

    /// Returns the head of `text`.
    ///
    /// # Arguments
    ///
    /// * `text` - The engine's text.
    fn of_text(text: &str) -> Self {
        Self::of(text.lines().count(), text.lines())
    }

    /// Returns how many lines of the text the head leaves out, 0 when it
    /// holds them all.
    #[must_use]
    pub const fn more(&self) -> usize {
        self.total.saturating_sub(self.lines.len())
    }
}

/// How a peek read a global's bytes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Read {
    /// As the type the overlay applied at the global ([`typed_tsv`]).
    Typed,
    /// As the hexdump of its first [`PEEK_BYTES`] bytes.
    Bytes,
}

/// How sure the engine is of the name of the import a slot holds.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Certainty {
    /// The file states the name.
    Resolved,
    /// A table of exports lends the name to the import's ordinal.
    Inferred,
    /// No one name is known: the loader made it up, two imports share the
    /// slot, or the import's slots say apart.
    Unresolved,
}

/// What a hover shows of a referent beyond its name.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Peek {
    /// The first lines of a function's decompile view.
    Function(Head),
    /// A global's bytes, read as [`Read`] says.
    Global(Read, Head),
    /// An import: its name as a call spells it and its declaration in the
    /// type library, both `None` where unknown.
    Import {
        /// The name, `None` when no one import symbol holds the slot.
        name: Option<String>,
        /// How sure the engine is of the name.
        certainty: Certainty,
        /// The library's declaration of the name, `None` when the name is
        /// unresolved or the library declares no such name.
        decl: Option<Head>,
    },
    /// Nothing is known of the referent, and the engine's reason why.
    Unknown(String),
}

/// Returns whether a hover peeks at what a token linking to `r` links to:
/// a function, a global or an import ([`peek`]).
///
/// # Arguments
///
/// * `r` - The referent a token links to.
#[must_use]
pub const fn peeks(r: &Ref) -> bool {
    match r {
        Ref::Function(_) | Ref::Global(_) | Ref::Import(_) => true,
        Ref::Address(_)
        | Ref::String(_)
        | Ref::Field { .. }
        | Ref::Variable { .. }
        | Ref::Type(_)
        | Ref::Comment(_) => false,
    }
}

/// Returns what a hover shows of `r` beyond its name.
///
/// A function's view and the type library are memoized or static, so a
/// second peek at the same referent is a lookup.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Its analysis.
/// * `overlay` - Names and types in force.
/// * `r` - The referent a token links to.
///
/// # Returns
///
/// The peek, [`Peek::Unknown`] with the reason when nothing is known of
/// `r`, and `None` only for a referent a peek never shows ([`peeks`]).
#[must_use]
pub fn peek(program: &Program, analysis: &Analysis, overlay: &Overlay, r: &Ref) -> Option<Peek> {
    Some(match r {
        Ref::Function(entry) => function(program, analysis, overlay, *entry),
        Ref::Global(va) => {
            let read = match overlay.applied.get(va) {
                Some(ty) => typed_tsv(program, Some(analysis), overlay, *va, ty)
                    .map(|text| (Read::Typed, text)),
                None => hex_rows(program, *va, PEEK_BYTES)
                    .spell(program)
                    .map(|text| (Read::Bytes, text)),
            };
            read.map_or_else(Peek::Unknown, |(how, text)| {
                Peek::Global(how, Head::of_text(&text))
            })
        }
        Ref::Import(slot) => import(program, analysis, *slot),
        Ref::Address(_)
        | Ref::String(_)
        | Ref::Field { .. }
        | Ref::Variable { .. }
        | Ref::Type(_)
        | Ref::Comment(_) => return None,
    })
}

/// Returns the peek at the function at `entry`: the head of its decompile
/// view, or why there is none.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Its analysis.
/// * `overlay` - Names in force.
/// * `entry` - The function's entry.
fn function(program: &Program, analysis: &Analysis, overlay: &Overlay, entry: u64) -> Peek {
    if analysis.function(entry).is_none() {
        return Peek::Unknown(format!("No function starts at {entry:#x}."));
    }
    super::view(program, analysis, overlay, entry).map_or_else(
        || {
            let why = format!("The engine built no decompile view of the function at {entry:#x}.");
            Peek::Unknown(why)
        },
        |view| {
            Peek::Function(Head::of(
                view.lines(),
                (0..view.lines()).filter_map(|i| view.line(i)),
            ))
        },
    )
}

/// Returns the peek at the import whose first slot is `slot`.
///
/// The name is the one import symbol at the slot, spelled as a call
/// through it spells it ([`import_spelling`]); how sure it is is what a
/// view says of the name ([`said`]); the declaration is the type library's
/// for its bare name, as the lifter looks a callee's up.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Its analysis, holding the import groups.
/// * `slot` - The import's first slot.
fn import(program: &Program, analysis: &Analysis, slot: u64) -> Peek {
    let held = said::import_symbols(program, analysis);
    let raw = match held.get(&slot).map(Vec::as_slice) {
        Some(&[k]) => program.symbols.get(k).map(|s| s.name.as_str()),
        Some(_) | None => None,
    };
    let Some(raw) = raw else {
        return Peek::Import {
            name: None,
            certainty: Certainty::Unresolved,
            decl: None,
        };
    };
    let name = import_spelling(raw);
    let certainty = match said::import(program, analysis, slot, &name) {
        Some(Said::Stated) => Certainty::Resolved,
        Some(Said::Inferred) => Certainty::Inferred,
        Some(Said::User | Said::Placeholder) | None => Certainty::Unresolved,
    };
    let decl = (certainty != Certainty::Unresolved)
        .then(|| typelib::declared(bare_name(raw), program.format))
        .flatten()
        .map(|decl| Head::of_text(&sdk::spell(decl)));
    Peek::Import {
        name: Some(capped(&name)),
        certainty,
        decl,
    }
}

/// Returns `line` cut to [`PEEK_WIDTH`] characters, ending in `…` where cut.
///
/// # Arguments
///
/// * `line` - One line of the engine's text.
fn capped(line: &str) -> String {
    match line.char_indices().nth(PEEK_WIDTH) {
        Some((at, _)) => format!("{}…", line.get(..at).unwrap_or_default()),
        None => line.to_owned(),
    }
}
