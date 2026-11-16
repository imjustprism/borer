//! Which block each line of a function's text stands for, carried through
//! the text passes, for a caller that asks ([`super::answer_with_origins`]).
//!
//! The lifter writes each block's statements, so a traced decompile records
//! which block spells each statement's text, indentation aside
//! ([`Spelled`], filled by [`spell`] as every block is lifted for the
//! emitter, copies and return tails included). An emitted line stands for
//! the one block that spells it; a text two blocks spell, a line the
//! emitter writes itself (a test, a jump, a brace) and a line above the
//! first label stand for none, and a label for the block it starts
//! ([`Origins`], seeded by [`Traced::seeded`]).
//!
//! The passes after the emitter rewrite that text as strings, so every
//! driver that runs one ([`Traced::map`], which [`super::Passes::apply`]
//! runs, and the cleanup rounds through [`Lines`]) carries the origins over
//! the rewrite. The lines both texts begin and end with keep theirs; the
//! lines between are matched by the shortest edit script
//! ([`crate::text::edit_script`]), indentation aside. A line the script
//! keeps keeps its origin. A label the script writes stands for the block
//! it starts. Another line it writes takes the origin of the one line it
//! deleted with the same text (a moved line); one whose text two deleted
//! lines spell takes none; one that replaced exactly one line that is no
//! label, keeping its tokens apart from its identifiers and numbers
//! ([`shape`]), takes that line's (the pass renamed, renumbered or
//! dropped a cast in place); every other written line takes none. A script
//! longer than [`EDITS_MAX`] steps or [`WORK_MAX`] comparisons, a span of changed lines
//! too long for those, and a rewrite after the caller's cancel flag was
//! raised leave the changed lines unknown. A span whose old lines are all
//! unknown is not diffed: its labels stand for their blocks, its other
//! lines for none. Unknown is `None`, never a
//! guess: no rule pairs lines by position alone or merges the origins of
//! several.
//!
//! This diff tracking is the bridge until the passes become transforms of
//! the C tree ([`super::cir`]), whose statements already keep the
//! addresses they came from; the tree's provenance will then feed the same
//! [`Origins`].

use std::collections::BTreeMap;
use std::ops::{Deref, Range};
use std::sync::Arc;

use super::decompile_with;
use super::finish::{finished_traced, named_from};
use super::lift::BlockOut;
use super::line::{label_address, label_name};
use crate::analysis::{Analysis, Overlay, decompiled_kept};
use crate::cancel::Cancel;
use crate::program::Program;
use crate::text::{Op, edit_script};

/// Most steps the edit script of one rewrite may take, as a delta of a
/// server's answer may; past it the lines the rewrite changed are unknown.
const EDITS_MAX: usize = 1_000;

/// Most line comparisons one rewrite's edit script may make, and most a
/// span of changed lines times [`EDITS_MAX`] may come to before the span is
/// unknown without one: a few milliseconds of work.
const WORK_MAX: usize = 4_000_000;

/// Each statement text a traced decompile's blocks spell, indentation
/// aside, to the one block that spells it: `None` when two blocks do.
pub type Spelled = BTreeMap<String, Option<u64>>;

/// What a decompilation keeps beside its text: a set of
/// [`Kept::WITNESS`] and [`Kept::ORIGINS`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct Kept(u8);

impl Kept {
    /// Nothing more.
    pub(crate) const NOTHING: Self = Self(0);
    /// What the lifter knew about each block, for the replay.
    pub(crate) const WITNESS: Self = Self(1);
    /// The block each line stands for ([`Origins`]).
    pub(crate) const ORIGINS: Self = Self(2);
    /// With [`Kept::ORIGINS`], the record the origins are seeded from
    /// ([`Spelled`]), for a sweep's oracle.
    pub(crate) const SPELLED: Self = Self(4);

    /// Returns the set with what `other` keeps too.
    ///
    /// # Arguments
    ///
    /// * `other` - What else to keep.
    #[must_use]
    pub(crate) const fn and(self, other: Self) -> Self {
        Self(self.0 | other.0)
    }

    /// Tells whether the set keeps all `other` keeps.
    ///
    /// # Arguments
    ///
    /// * `other` - What to look for.
    pub(crate) const fn has(self, other: Self) -> bool {
        self.0 & other.0 == other.0
    }
}

/// The C keywords [`shape`] keeps as themselves: a rename never changes
/// one, so a line whose keyword changed is another statement.
const KEYWORDS: [&str; 13] = [
    "goto", "return", "break", "continue", "if", "else", "while", "do", "for", "switch", "case",
    "default", "sizeof",
];

/// Returns what a rename, a renumbering or dropping a cast keeps of a line.
///
/// That is its tokens apart from its identifiers and numbers, each of those
/// as `#` and each keyword as itself ([`KEYWORDS`]), space-separated, and
/// apart from its one-word casts ([`cast_len`]).
///
/// # Arguments
///
/// * `line` - The line.
fn shape(line: &str) -> String {
    let mut out = String::with_capacity(line.len());
    let mut rest = line;
    while let Some(c) = rest.chars().next() {
        let w = |c: char| c.is_ascii_alphanumeric() || c == '_';
        let cast = (c == '(' && !out.ends_with("# "))
            .then(|| cast_len(rest))
            .flatten();
        let len = if let Some(len) = cast {
            len
        } else if w(c) {
            let word = rest.find(|c: char| !w(c)).unwrap_or(rest.len());
            let token = rest.get(..word).unwrap_or_default();
            out.push_str(if KEYWORDS.contains(&token) {
                token
            } else {
                "#"
            });
            out.push(' ');
            word
        } else {
            if !c.is_whitespace() {
                out.push(c);
            }
            c.len_utf8()
        };
        rest = rest.get(len..).unwrap_or_default();
    }
    out
}

/// Returns the length of the cast `rest` starts with: one word that is no
/// keyword in parentheses, followed by an operand (a word or a `(`).
///
/// # Arguments
///
/// * `rest` - The line from a `(` no name precedes.
///
/// # Returns
///
/// The cast's bytes, or `None` when `rest` starts with none.
fn cast_len(rest: &str) -> Option<usize> {
    let w = |c: char| c.is_ascii_alphanumeric() || c == '_';
    let inner = rest.strip_prefix('(')?;
    let close = inner.find(')')?;
    let ty = inner.get(..close)?.trim();
    let after = inner.get(close.checked_add(1)?..)?.trim_start();
    (!ty.is_empty()
        && ty.chars().all(w)
        && !KEYWORDS.contains(&ty)
        && after.starts_with(|c: char| w(c) || c == '('))
    .then(|| close.saturating_add(2))
}

/// Records the statement texts one block's lift spells ([`Spelled`]).
///
/// # Arguments
///
/// * `spelled` - The record so far.
/// * `block` - The block's start address.
/// * `out` - Its lift for the emitter.
pub(super) fn spell(spelled: &mut Spelled, block: u64, out: &BlockOut) {
    let tail = out.branch_tail.iter().flatten();
    for line in out.lines.iter().chain(tail) {
        spelled
            .entry(line.trim().to_owned())
            .and_modify(|b| *b = b.filter(|&k| k == block))
            .or_insert(Some(block));
    }
}

/// The block each line of a function's text stands for, in the order
/// [`str::lines`] reads them: the start address of the one block whose
/// lifted code spells the line, or `None` when unknown.
///
/// A missed origin beats a false one: a line no rule places is unknown,
/// never guessed.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Origins(Vec<Option<u64>>);

impl Origins {
    /// Returns the origins of a text the emitter wrote.
    ///
    /// # Arguments
    ///
    /// * `text` - The emitter's text, a `L_<hex>:` label before each block.
    /// * `spelled` - Which block spells each statement text.
    fn seeded(text: &str, spelled: &Spelled) -> Self {
        let mut started = false;
        Self(
            text.lines()
                .map(|line| {
                    if let Some(name) = label_name(line) {
                        started = true;
                        return label_address(name);
                    }
                    started
                        .then(|| spelled.get(line.trim()).copied().flatten())
                        .flatten()
                })
                .collect(),
        )
    }

    /// Returns the origins of `n` lines, all unknown.
    ///
    /// # Arguments
    ///
    /// * `n` - How many lines.
    fn unknown(n: usize) -> Self {
        Self(vec![None; n])
    }

    /// Returns the block one line stands for.
    ///
    /// # Arguments
    ///
    /// * `i` - The line, from 0.
    ///
    /// # Returns
    ///
    /// The block's start address; `None` when unknown and past the last
    /// line.
    #[must_use]
    pub fn line(&self, i: usize) -> Option<u64> {
        self.0.get(i).copied().flatten()
    }

    /// Returns how many lines the origins are of.
    #[must_use]
    pub fn len(&self) -> usize {
        self.0.len()
    }

    /// Tells whether the origins are of no line.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    /// Tells whether any line's origin is known.
    #[must_use]
    pub fn known(&self) -> bool {
        self.0.iter().any(Option::is_some)
    }

    /// Returns the heap bytes the origins hold.
    #[must_use]
    pub fn bytes(&self) -> usize {
        self.0.capacity() * size_of::<Option<u64>>()
    }

    /// Returns the origins of a text with `n` unknown lines put under its
    /// first line, as [`super::with_header`] puts an answer's header lines.
    ///
    /// # Arguments
    ///
    /// * `n` - How many lines go under the first.
    #[must_use]
    fn under_first(&self, n: usize) -> Self {
        let first = self.0.iter().take(1).copied();
        let rest = self.0.iter().skip(1).copied();
        Self(
            first
                .chain(std::iter::repeat_n(None, n))
                .chain(rest)
                .collect(),
        )
    }

    /// Returns the origins of a text a rewrite made of a different text
    /// these are the origins of: unknown, with no diff, once every origin
    /// is or the caller's cancel flag is raised ([`Cancel`]).
    ///
    /// # Arguments
    ///
    /// * `old` - The text before the rewrite.
    /// * `new` - The text after it.
    fn carried(&self, old: &str, new: &str) -> Self {
        if !self.known() || Cancel::raised() {
            return Self::unknown(new.lines().count());
        }
        let old: Vec<&str> = old.lines().collect();
        let new: Vec<&str> = new.lines().collect();
        self.stepped(&old, &new)
    }

    /// Returns the origins of the lines a rewrite made of the lines these
    /// are the origins of, as the module says it carries them.
    ///
    /// # Arguments
    ///
    /// * `old` - The lines before the rewrite.
    /// * `new` - The lines after it.
    ///
    /// # Returns
    ///
    /// One origin per line of `new`.
    fn stepped<A: AsRef<str>, B: AsRef<str>>(&self, old: &[A], new: &[B]) -> Self {
        let old: Vec<&str> = old.iter().map(|l| l.as_ref().trim()).collect();
        let new: Vec<&str> = new.iter().map(|l| l.as_ref().trim()).collect();
        let head = old.iter().zip(&new).take_while(|(a, b)| a == b).count();
        let tail = old
            .iter()
            .skip(head)
            .rev()
            .zip(new.iter().skip(head).rev())
            .take_while(|(a, b)| a == b)
            .count();
        let (gone, made) = (head..old.len() - tail, head..new.len() - tail);
        let mut out: Vec<Option<u64>> = Vec::with_capacity(new.len());
        out.extend(self.0.iter().take(head).copied());
        out.extend(self.between(&old, &new, gone, made));
        out.extend(self.0.iter().skip(old.len() - tail).copied());
        Self(out)
    }

    /// Returns the origins of the lines a rewrite wrote between the lines
    /// both texts begin and end with, matched by the shortest edit script.
    ///
    /// # Arguments
    ///
    /// * `old` - The trimmed lines before the rewrite.
    /// * `new` - The trimmed lines after it.
    /// * `gone` - The old lines between.
    /// * `made` - The new lines between.
    ///
    /// # Returns
    ///
    /// One origin per line of `made`.
    fn between(
        &self,
        old: &[&str],
        new: &[&str],
        gone: Range<usize>,
        made: Range<usize>,
    ) -> Vec<Option<u64>> {
        let (a, b) = (&old[gone.clone()], &new[made.clone()]);
        let at = |k: usize| self.line(gone.start + k);
        if gone.clone().all(|k| self.line(k).is_none()) {
            return b
                .iter()
                .map(|l| label_name(l).and_then(label_address))
                .collect();
        }
        let work = (a.len() + b.len()).saturating_mul(EDITS_MAX);
        let edits = (work <= WORK_MAX)
            .then(|| edit_script(a, b, EDITS_MAX, WORK_MAX))
            .flatten();
        let Some(edits) = edits else {
            return vec![None; made.len()];
        };
        let mut deleted: BTreeMap<&str, Option<usize>> = BTreeMap::new();
        for e in edits.iter().filter(|e| e.op == Op::Delete) {
            if let Some(&line) = a.get(e.old) {
                deleted
                    .entry(line)
                    .and_modify(|k| *k = None)
                    .or_insert(Some(e.old));
            }
        }
        let mut out: Vec<Option<u64>> = Vec::with_capacity(b.len());
        let (mut x, mut i) = (0, 0);
        loop {
            let (hx, hy) = edits.get(i).map_or((a.len(), b.len()), |e| (e.old, e.new));
            while out.len() < hy {
                out.push(at(x));
                x += 1;
            }
            if i >= edits.len() {
                break;
            }
            let (mut cx, mut cy) = (hx, hy);
            while let Some(e) = edits.get(i).filter(|e| (e.old, e.new) == (cx, cy)) {
                match e.op {
                    Op::Delete => cx += 1,
                    Op::Insert => cy += 1,
                }
                i += 1;
            }
            let was = (cx - hx == 1 && cy - hy == 1)
                .then(|| a.get(hx).copied())
                .flatten()
                .filter(|l| label_name(l).is_none());
            for &line in b.iter().take(cy).skip(hy) {
                out.push(match (label_name(line), deleted.get(line)) {
                    (Some(name), _) => label_address(name),
                    (None, Some(Some(j))) => at(*j),
                    (None, Some(None)) => None,
                    (None, None) => was.filter(|w| shape(w) == shape(line)).and(at(hx)),
                });
            }
            x = cx;
        }
        out
    }
}

/// A text, and the origin of each of its lines when it is traced.
///
/// The text is reached only through a rewrite that carries the origins
/// ([`Traced::map`]), so no pass can change it behind them.
#[derive(Debug, Clone, Default)]
pub(super) struct Traced {
    /// The text.
    text: String,
    /// The origin of each line of [`Traced::text`]; `None` when the text
    /// is not traced, which no rewrite then pays for.
    origins: Option<Origins>,
}

impl Traced {
    /// Returns the text the emitter wrote, traced from the blocks that spell
    /// its lines when a record of them is kept.
    ///
    /// # Arguments
    ///
    /// * `text` - The emitter's text.
    /// * `spelled` - Which block spells each statement text, `None` for a
    ///   decompile not traced.
    pub(super) fn seeded(text: String, spelled: Option<&Spelled>) -> Self {
        let origins = spelled.map(|s| Origins::seeded(&text, s));
        Self { text, origins }
    }

    /// Returns a text with the origins given.
    ///
    /// # Arguments
    ///
    /// * `text` - The text.
    /// * `origins` - Its lines' origins, `None` for a text not traced.
    ///
    /// # Returns
    ///
    /// The traced text; every line is unknown when `origins` are not of as
    /// many lines as `text` has, which is a bug a debug build stops on.
    pub(super) fn new(text: String, origins: Option<Origins>) -> Self {
        let lines = text.lines().count();
        let origins = origins.map(|o| {
            debug_assert_eq!(o.len(), lines, "the origins of another text");
            if o.len() == lines {
                o
            } else {
                Origins::unknown(lines)
            }
        });
        Self { text, origins }
    }

    /// Returns `head` with this text after it, the head's lines unknown.
    ///
    /// # Arguments
    ///
    /// * `head` - The lines that go first, each ending in a newline.
    /// * `body` - The text that follows them.
    pub(super) fn under(head: String, body: Self) -> Self {
        let origins = body.origins.map(|o| {
            let unknown = std::iter::repeat_n(None, head.matches('\n').count());
            Origins(unknown.chain(o.0).collect())
        });
        let mut text = head;
        text.push_str(&body.text);
        Self::new(text, origins)
    }

    /// Returns the text a rewrite makes of this one, the origins carried
    /// over it.
    ///
    /// # Arguments
    ///
    /// * `rewrite` - The rewrite.
    #[must_use]
    pub(super) fn map(self, rewrite: impl FnOnce(&str) -> String) -> Self {
        self.map_with(|text| (rewrite(text), ())).0
    }

    /// Returns [`Traced::map`]'s text when `run` holds, else this text.
    ///
    /// # Arguments
    ///
    /// * `run` - Whether the rewrite runs.
    /// * `rewrite` - The rewrite.
    #[must_use]
    pub(super) fn map_if(self, run: bool, rewrite: impl FnOnce(&str) -> String) -> Self {
        if run { self.map(rewrite) } else { self }
    }

    /// Returns the text a rewrite makes of this one, the origins carried
    /// over it, and what else the rewrite made.
    ///
    /// # Arguments
    ///
    /// * `rewrite` - The rewrite, giving its text and what else it made.
    pub(super) fn map_with<R>(self, rewrite: impl FnOnce(&str) -> (String, R)) -> (Self, R) {
        let (text, made) = rewrite(&self.text);
        (self.to(text), made)
    }

    /// Returns a text a rewrite made of this one, the origins carried over
    /// it: no diff runs once every origin is unknown or the caller's cancel
    /// flag is raised ([`Cancel`]).
    ///
    /// # Arguments
    ///
    /// * `text` - The rewritten text.
    #[must_use]
    pub(super) fn to(self, text: String) -> Self {
        let origins = self.origins.map(|o| {
            if text == self.text {
                o
            } else {
                o.carried(&self.text, &text)
            }
        });
        Self { text, origins }
    }

    /// Returns a text a rewrite made of a text the caller holds, the origins
    /// carried over it, without a copy of the old text.
    ///
    /// # Arguments
    ///
    /// * `old` - The text before the rewrite, and its origins when traced.
    /// * `text` - The rewritten text.
    #[must_use]
    pub(super) fn rewritten(old: (&str, Option<&Origins>), text: String) -> Self {
        let origins = old.1.map(|o| {
            if text == old.0 {
                o.clone()
            } else {
                o.carried(old.0, &text)
            }
        });
        Self { text, origins }
    }

    /// Returns the text, letting the origins go.
    pub(super) fn into_text(self) -> String {
        self.text
    }

    /// Returns the origins, `None` for a text not traced.
    pub(super) fn origins(&self) -> Option<&Origins> {
        self.origins.as_ref()
    }

    /// Returns the text and its origins.
    pub(super) fn into_parts(self) -> (String, Option<Origins>) {
        (self.text, self.origins)
    }

    /// Returns the heap bytes the text and its origins hold.
    pub(super) fn bytes(&self) -> usize {
        self.text.capacity() + self.origins.as_ref().map_or(0, Origins::bytes)
    }
}

impl Deref for Traced {
    type Target = str;

    fn deref(&self) -> &str {
        &self.text
    }
}

/// Returns the text [`super::decompile_named`] answers and the block each
/// of its lines stands for.
///
/// It is memoized per function under the names in force through
/// [`Analysis::derived`] apart from the untraced text, so only a caller
/// asking for origins pays for them. The decompilation is the
/// shared one when a traced build made it ([`decompiled_kept`]), else a
/// traced build of its own.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Discovery results, holding the memo.
/// * `overlay` - User names and comments.
/// * `entry` - The function's entry address.
///
/// # Returns
///
/// The traced text, `None` when the function does not decompile.
pub(super) fn named(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    entry: u64,
) -> Arc<Option<Traced>> {
    analysis.derived.get_or_build_item(
        "traced_text",
        overlay.fingerprint(),
        entry,
        || {
            let key = overlay.fingerprint();
            let shared = decompiled_kept(program, analysis, overlay, key, entry, Kept::ORIGINS);
            let fresh;
            let d = match shared.as_ref() {
                Some(d) if d.origins.is_some() => d,
                _ => {
                    fresh = decompile_with(
                        program,
                        analysis,
                        overlay,
                        entry,
                        true,
                        &[],
                        Kept::ORIGINS,
                    )?;
                    &fresh
                }
            };
            let laid = || {
                Some(finished_traced(
                    d.traced(),
                    program,
                    analysis,
                    overlay,
                    entry,
                ))
            };
            let text = (d.text.as_str(), d.origins.as_ref());
            named_from(program, analysis, overlay, entry, text, laid)?.1
        },
        |t| t.as_ref().map_or(0, Traced::bytes),
    )
}

/// Returns the origins of an answer: a traced text's, with `under` unknown
/// lines under its first.
///
/// # Arguments
///
/// * `text` - The traced text.
/// * `under` - How many header lines the answer puts under its first line.
pub(super) fn under_header(text: &Traced, under: usize) -> Option<Origins> {
    text.origins().map(|o| o.under_first(under))
}

/// Lines a driver rewrites in place, told after each rewrite so their
/// origins can follow it: the plain lines of a text not traced, or the
/// [`Shadowed`] lines of one that is.
pub(super) trait Lines {
    /// Returns the lines to rewrite.
    fn lines(&mut self) -> &mut Vec<String>;

    /// Notes that a rewrite changed the lines.
    fn rewrote(&mut self);
}

impl Lines for Vec<String> {
    fn lines(&mut self) -> &mut Vec<String> {
        self
    }

    fn rewrote(&mut self) {}
}

/// Lines rewritten in place, and the lines as they stood at the last
/// rewrite with the origin of each, which [`Lines::rewrote`] carries over
/// what changed since.
#[derive(Debug)]
pub(super) struct Shadowed {
    /// The lines.
    lines: Vec<String>,
    /// The lines at the last rewrite and their origins.
    kept: Vec<String>,
    /// The origin of each of [`Shadowed::kept`].
    origins: Origins,
}

impl Shadowed {
    /// Returns a traced text's lines, ready to rewrite in place.
    ///
    /// # Arguments
    ///
    /// * `text` - The text.
    /// * `origins` - The origin of each of its lines.
    pub(super) fn new(text: &str, origins: Origins) -> Self {
        let lines: Vec<String> = text.lines().map(str::to_owned).collect();
        Self {
            kept: lines.clone(),
            lines,
            origins,
        }
    }

    /// Returns the lines joined into a text, each ending in a newline, with
    /// their origins: no lines give one empty line, as the untraced cleanup
    /// writes them.
    pub(super) fn into_traced(mut self) -> Traced {
        self.rewrote();
        let mut text = self.lines.join("\n");
        text.push('\n');
        let origins = if self.lines.is_empty() {
            Origins::unknown(1)
        } else {
            self.origins
        };
        Traced::new(text, Some(origins))
    }
}

impl Lines for Shadowed {
    fn lines(&mut self) -> &mut Vec<String> {
        &mut self.lines
    }

    fn rewrote(&mut self) {
        if !self.origins.known() || Cancel::raised() {
            self.origins = Origins::unknown(self.lines.len());
        } else if self.kept != self.lines {
            self.origins = self.origins.stepped(&self.kept, &self.lines);
            self.kept.clone_from(&self.lines);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{Lines, Shadowed, Spelled, Traced};

    /// Returns a text's origins line by line.
    ///
    /// # Arguments
    ///
    /// * `t` - The traced text.
    fn origins(t: &Traced) -> Vec<Option<u64>> {
        let o = t.origins.clone().unwrap_or_default();
        (0..o.len()).map(|i| o.line(i)).collect()
    }

    /// Returns a traced text whose statements each spell their own block:
    /// `x` 0x10, `y` 0x20, `z` 0x30, `f()` both 0x10 and 0x20.
    ///
    /// # Arguments
    ///
    /// * `text` - The emitter's text.
    fn seeded(text: &str) -> Traced {
        let spelled: Spelled = [
            ("x = 1;", Some(0x10)),
            ("y = 2;", Some(0x20)),
            ("z = 3;", Some(0x30)),
            ("f();", None),
        ]
        .into_iter()
        .map(|(t, b)| (t.to_owned(), b))
        .collect();
        Traced::seeded(text.to_owned(), Some(&spelled))
    }

    /// A line stands for the one block that spells it, wherever the emitter
    /// put it; a text two blocks spell, a line the emitter wrote and a line
    /// above every label stand for none, a label for its block.
    ///
    /// # Panics
    ///
    /// When a line stands for another block.
    #[test]
    fn a_line_stands_for_the_one_block_that_spells_it() {
        let t = seeded("x = 1;\nL_10:\n  y = 2;\nf();\nif (c) goto L_30;\nL_30:\nz = 3;\n");
        assert_eq!(
            origins(&t),
            [
                None,
                Some(0x10),
                Some(0x20),
                None,
                None,
                Some(0x30),
                Some(0x30)
            ]
        );
        assert!(Traced::seeded("L_10:\n".into(), None).origins.is_none());
    }

    /// A line a rewrite moves keeps its origin, indentation aside; a line
    /// two deleted lines spell gets none, as does a line a run only
    /// inserts.
    ///
    /// # Panics
    ///
    /// When a moved line loses its origin or an ambiguous one gets one.
    #[test]
    fn a_moved_line_keeps_its_origin_and_an_ambiguous_one_gets_none() {
        let t = seeded("L_10:\nx = 1;\nL_20:\ny = 2;\nL_30:\nz = 3;\n");
        let moved = t.map(|_| "L_10:\nL_20:\ny = 2;\nL_30:\nz = 3;\n  x = 1;\n".into());
        assert_eq!(origins(&moved)[5], Some(0x10));
        let t = seeded("L_10:\nx = 1;\nL_20:\nx = 1;\nL_30:\nz = 3;\n");
        let merged = t.map(|_| "L_10:\nL_20:\nL_30:\nz = 3;\nx = 1;\n".into());
        assert_eq!(
            origins(&merged),
            [Some(0x10), Some(0x20), Some(0x30), Some(0x30), None]
        );
    }

    /// A run that replaced one line with one takes that line's origin; two
    /// deleted lines spelling one inserted line's text, and a run that
    /// replaced several lines, give unknown: nothing pairs by position.
    ///
    /// # Panics
    ///
    /// When a line of a run takes an origin it has no rule for.
    #[test]
    fn only_a_line_rewritten_in_place_keeps_its_origin() {
        let t = seeded("L_10:\nx = 1;\nL_20:\ny = 2;\nreturn;\n");
        let rewritten = t
            .clone()
            .map(|_| "L_10:\nx = 5;\nL_20:\ny = 2;\nreturn;\n".into());
        assert_eq!(origins(&rewritten)[1], Some(0x10));
        let two = t.map(|_| "L_10:\nx = 5;\ny = 6;\nreturn;\n".into());
        assert_eq!(origins(&two)[1..3], [None, None]);
        let t = seeded("L_10:\nx = 1;\nx = 1;\ny = 2;\n");
        let ambiguous = t.map(|_| "L_10:\ny = 2;\nx = 1;\n".into());
        assert_eq!(origins(&ambiguous), [Some(0x10), Some(0x20), None]);
    }

    /// A line rewritten in place keeps its origin only while it keeps its
    /// tokens apart from names and numbers; a label's origin goes to no
    /// other line, and a label a rewrite writes stands for its own block.
    ///
    /// # Panics
    ///
    /// When a reshaped line or a line in a label's place keeps an origin,
    /// or a written label stands for another block.
    #[test]
    fn a_rewrite_in_place_keeps_the_origin_only_of_its_shape() {
        let t = seeded("L_10:\nx = 1;\nL_20:\ny = 2;\n");
        let reshaped = t.clone().map(|_| "L_10:\n*x = 1;\nL_20:\ny = 2;\n".into());
        assert_eq!(origins(&reshaped)[1], None);
        let relabeled = t
            .clone()
            .map(|_| "L_10:\nx = 1;\nz = (3);\ny = 2;\n".into());
        assert_eq!(origins(&relabeled)[2], None);
        let moved = t.map(|_| "L_30:\nx = 1;\nL_20:\ny = 2;\n".into());
        assert_eq!(origins(&moved)[0], Some(0x30));
        assert_eq!(
            super::shape("  rax = *(uint32_t*)(a1 + 0x10);"),
            "# =*(# *)(# +# );"
        );
        assert_eq!(
            super::shape("return (uint32_t)a1 == 0x1337abcd;"),
            super::shape("return a1 == 0x1337abcd;")
        );
        assert_ne!(super::shape("f(a1)(x);"), super::shape("f(x);"));
    }

    /// A jump rewritten in place into a return is another statement: its
    /// keyword changed, so it keeps no origin, bare or after a `case`.
    ///
    /// # Panics
    ///
    /// When the return takes the jump's block.
    #[test]
    fn a_jump_rewritten_into_a_return_keeps_no_origin() {
        let start = Some(super::Origins(vec![Some(5), None, None]));
        let none = Traced::new("L_5:\nx = 1;\ny = 2;\n".into(), start);
        let labeled = none.map(|_| "L_5:\nL_10:\ny = 3;\n".into());
        assert_eq!(origins(&labeled), [Some(5), Some(0x10), None]);
        let known = |n| Some(super::Origins(vec![Some(0x10); n]));
        let jump = Traced::new("L_10:\nx = 1;\ngoto L_20;\n".into(), known(3));
        let ret = jump.map(|_| "L_10:\nx = 1;\nreturn eax;\n".into());
        assert_eq!(origins(&ret), [Some(0x10), Some(0x10), None]);
        let case = Traced::new("L_10:\ncase 3: goto L_20;\n".into(), known(2));
        let ret = case.map(|_| "L_10:\ncase 3: return eax;\n".into());
        assert_eq!(origins(&ret), [Some(0x10), None]);
    }

    /// Lines rewritten in place carry their origins over what changed
    /// since the last rewrite, and once every origin is unknown they stay
    /// unknown without a diff.
    ///
    /// # Panics
    ///
    /// When a kept line loses its origin.
    #[test]
    fn rewritten_lines_carry_their_origins() {
        let t = seeded("L_10:\nx = 1;\nL_20:\ny = 2;\n");
        let (text, o) = t.into_parts();
        let mut lines = Shadowed::new(&text, o.unwrap_or_default());
        lines.lines()[3] = "y = 3;".to_owned();
        lines.rewrote();
        lines.lines().remove(0);
        lines.rewrote();
        let t = lines.into_traced();
        assert_eq!(t.text, "x = 1;\nL_20:\ny = 3;\n");
        assert_eq!(origins(&t), [Some(0x10), Some(0x20), Some(0x20)]);
        let mut none = Shadowed::new("a;\nb;\n", super::Origins::unknown(2));
        none.lines().push("c;".to_owned());
        none.rewrote();
        assert!(none.kept.len() == 2 && !none.origins.known());
        assert_eq!(none.origins.len(), 3);
        let mut gone = Shadowed::new("a;\n", super::Origins(vec![Some(0x10)]));
        gone.lines().clear();
        let empty = gone.into_traced();
        assert_eq!((empty.text.as_str(), origins(&empty).len()), ("\n", 1));
    }
}
