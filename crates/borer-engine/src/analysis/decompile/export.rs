//! Whole-binary export: every function's pseudo-C as one C file.
//!
//! Each function is decompiled as the `decompile` tool shows it
//! ([`super::decompile_named_all`]), its translation-unit closure included, and
//! split at its declarations: the file-scope ones (vector typedefs, helper
//! definitions, prototypes, tables and globals) are hoisted to the top of
//! the file, each once, and what is left becomes a C function definition
//! whose head is the text's `// signature:`. A function the file defines
//! is declared by that signature alone, so the closure's own prototype or
//! `static inline` copy of it is dropped.
//!
//! The functions come leaves first ([`order`]): each after every function
//! it calls, a call cycle in entry order. Library code (a library or pack
//! signature matched it, or it is a runtime helper) is left out unless
//! asked for, and an import thunk or a linkage stub always is, being an
//! import rather than code of the program's own. A function over
//! [`BUDGET_BLOCKS`] is not decompiled: a comment saying it was cut
//! stands in its place, and the rest of the file is written whole.
//!
//! [`export`] renders the functions across the cores ([`in_order`]) and
//! hands each finished definition to a sink in order, so memory holds a
//! bounded window of texts and the hoisted declarations, never the file;
//! the caller writes [`Hoisted::head`] above what the sink received.

use super::{Analysis, BTreeMap, BTreeSet, Function, Overlay, Program, name_of};
use crate::analysis::NameSource;
use std::fmt::Write as _;

/// What the file declares before any declaration a function hoists: the
/// headers the helper definitions and the C library names need, and the
/// 128-bit integer types C does not name.
pub const PRELUDE: &str = "#include <stdint.h>
#include <stddef.h>
#include <stdbool.h>
#include <string.h>
#include <stdlib.h>
#include <math.h>

typedef unsigned __int128 uint128_t;
typedef __int128 int128_t;
";

/// Functions a worker of [`in_order`] may always render past the oldest
/// text not yet taken, per core.
const AHEAD_PER_CORE: usize = 128;

/// Bytes of finished texts [`in_order`] may hold past its window.
///
/// Past [`AHEAD_PER_CORE`] functions a core, a worker goes on only while
/// the texts held come to less: enough to keep every core busy while the
/// taker waits minutes on one function.
const HELD_BYTES: usize = 256 << 20;

/// Functions per core [`in_order`] renders before all others: the ones
/// of the most blocks, which take seconds where most take milliseconds, so
/// none starts so late that the export waits on it at the end.
const HEAVY_PER_CORE: usize = 4;

/// Bytes of definitions gathered before they go to the sink.
const SINK_BYTES: usize = 1 << 20;

/// Most declarations stated two ways the head of the file names.
const CONFLICTS_SHOWN: usize = 8;

/// Most basic blocks a function may hold for the export to decompile it.
///
/// Decompiling costs far more than linearly in a function's blocks (a
/// branchy function of 4000 blocks took 4 s, of 8000 blocks 22 s, of 16000
/// blocks 15 minutes; a straight run of 64000 instructions under half a
/// second), so one huge function could hold up a whole binary's export.
/// The bound counts what discovery already measured, never time, so a
/// binary's file is the same bytes at any thread count. It is about twice
/// the largest function of the corpus (`notepad.exe`'s `NPInit`, 2197
/// blocks); `decompile` still writes a cut function alone.
pub const BUDGET_BLOCKS: usize = 4096;

/// Whether library code goes into the file.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Library {
    /// Leave out functions a library or pack signature named, and runtime
    /// helpers.
    Skip,
    /// Write them like any other function.
    Include,
}

/// Tells whether the export leaves a function out.
///
/// # Arguments
///
/// * `f` - The function.
/// * `library` - Whether library code is written.
///
/// # Returns
///
/// `true` for an import thunk or linkage stub, and, under
/// [`Library::Skip`], for a function named by a library or pack signature
/// or recognized as a runtime helper.
#[must_use]
pub fn left_out(f: &Function, library: Library) -> bool {
    let lib = match f.name_source {
        NameSource::Library | NameSource::Pack | NameSource::Helper => true,
        NameSource::None
        | NameSource::Symbol
        | NameSource::Signature
        | NameSource::Handler
        | NameSource::Slot
        | NameSource::Qt
        | NameSource::Funclet
        | NameSource::ObjC
        | NameSource::Constants => false,
    };
    f.thunk.is_some() || f.bound.is_some() || lib && library == Library::Skip
}

/// Orders the functions the export writes, leaves first.
///
/// A depth-first walk from each function in entry order writes a function
/// after every callee it reaches; a callee already on the walk's path (a
/// cycle) is passed over, so the order is total and the same every run.
///
/// # Arguments
///
/// * `analysis` - The functions and their callees.
/// * `library` - Whether library code is written ([`left_out`]).
///
/// # Returns
///
/// The entries of the written functions, each once.
#[must_use]
pub fn order(analysis: &Analysis, library: Library) -> Vec<u64> {
    let mut seen: BTreeSet<u64> = BTreeSet::new();
    let mut out = Vec::with_capacity(analysis.functions.len());
    for root in &analysis.functions {
        if !seen.insert(root.entry) {
            continue;
        }
        let mut stack: Vec<(u64, usize)> = vec![(root.entry, 0)];
        while let Some((entry, next)) = stack.pop() {
            let callees = analysis.function(entry).map_or(&[][..], |f| &f.callees);
            match callees.get(next) {
                Some(&callee) => {
                    stack.push((entry, next + 1));
                    if analysis.function(callee).is_some_and(|f| f.entry == callee)
                        && seen.insert(callee)
                    {
                        stack.push((callee, 0));
                    }
                }
                None => {
                    if analysis
                        .function(entry)
                        .is_some_and(|f| f.entry == entry && !left_out(f, library))
                    {
                        out.push(entry);
                    }
                }
            }
        }
    }
    out
}

/// One file-scope line a function's text declares, by what it is.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum Kind {
    /// A `typedef`.
    Type,
    /// A helper's `#define` or `#undef`, keyed by the line.
    Macro,
    /// A helper's, import's or runtime function's declaration or
    /// definition, keyed by its name.
    Runtime,
    /// `extern T f(P);`, keyed by the function's name.
    Extern,
    /// `static inline T f(P) { ... }` of a function the binary holds,
    /// keyed by its name.
    Inline,
    /// A table or a global, keyed by its name.
    Data,
}

/// Lines in first-seen order, each key once.
#[derive(Debug, Default)]
struct Ordered {
    /// Each key's index in `lines`.
    keys: BTreeMap<String, usize>,
    /// The lines with their keys, in the order the keys were first seen.
    lines: Vec<(String, String)>,
}

impl Ordered {
    /// Keeps a line unless its key was seen.
    ///
    /// # Arguments
    ///
    /// * `key` - What makes the line a duplicate.
    /// * `line` - The line.
    ///
    /// # Returns
    ///
    /// `false` when the key was seen with another line: a conflict the
    /// first line won.
    fn add(&mut self, key: &str, line: &str) -> bool {
        if let Some(&at) = self.keys.get(key) {
            return self.lines.get(at).is_some_and(|(_, l)| l == line);
        }
        self.keys.insert(key.to_owned(), self.lines.len());
        self.lines.push((key.to_owned(), line.to_owned()));
        true
    }

    /// Tells whether a key was seen.
    ///
    /// # Arguments
    ///
    /// * `key` - The key.
    fn has(&self, key: &str) -> bool {
        self.keys.contains_key(key)
    }
}

/// The declarations the functions hoisted, and the export's counts.
#[derive(Debug, Default)]
pub struct Hoisted {
    /// `typedef` lines.
    types: Ordered,
    /// Helper, import and runtime declarations and definitions.
    helpers: Ordered,
    /// Each written function's prototype, from its signature, by name.
    defined: Ordered,
    /// `extern` prototypes, by name.
    externs: Ordered,
    /// `static inline` definitions of the binary's functions, by name.
    inlines: Ordered,
    /// Tables and globals, by name.
    data: Ordered,
    /// The names of the binary's functions, as a text spells them.
    functions: BTreeSet<String>,
    /// Declarations a later function stated otherwise than the kept one.
    pub conflicts: usize,
    /// The first [`CONFLICTS_SHOWN`] of them, as the later function stated
    /// each.
    conflicting: Vec<String>,
    /// Functions written with a body.
    pub written: usize,
    /// Functions that did not decompile, written as a comment.
    pub failed: usize,
    /// Functions over [`BUDGET_BLOCKS`], written as a comment without
    /// being decompiled.
    pub cut: usize,
    /// Functions left out ([`left_out`]).
    pub left_out: usize,
}

impl Hoisted {
    /// Starts an export of a binary with these functions.
    ///
    /// # Arguments
    ///
    /// * `functions` - The names of its functions, as a text spells them:
    ///   a declaration of one of them is a prototype, of any other name a
    ///   helper's, an import's or the runtime's.
    #[must_use]
    pub fn new(functions: BTreeSet<String>) -> Self {
        Self {
            functions,
            ..Self::default()
        }
    }

    /// Records one declaration line.
    ///
    /// # Arguments
    ///
    /// * `kind` - What it declares.
    /// * `line` - The line.
    fn hoist(&mut self, kind: Kind, line: &str) {
        let (store, key) = match kind {
            Kind::Type => (&mut self.types, line.to_owned()),
            Kind::Macro => (&mut self.helpers, line.to_owned()),
            Kind::Runtime => (&mut self.helpers, declared_name(line)),
            Kind::Extern => (&mut self.externs, declared_name(line)),
            Kind::Inline => (&mut self.inlines, declared_name(line)),
            Kind::Data => (&mut self.data, declared_name(line)),
        };
        let kept = store.add(&key, line);
        self.conflict(kept, line);
    }

    /// Counts a declaration a function stated otherwise than the one kept,
    /// keeping the first [`CONFLICTS_SHOWN`] for the head to show.
    ///
    /// # Arguments
    ///
    /// * `kept` - Whether the declaration agreed with the kept one.
    /// * `line` - The declaration as the later function stated it.
    fn conflict(&mut self, kept: bool, line: &str) {
        if kept {
            return;
        }
        self.conflicts += 1;
        if self.conflicting.len() < CONFLICTS_SHOWN {
            self.conflicting.push(line.to_owned());
        }
    }

    /// Writes the comment that stands for a function over
    /// [`BUDGET_BLOCKS`], which the export does not decompile.
    ///
    /// # Arguments
    ///
    /// * `name` - The function's name.
    /// * `entry` - Its entry.
    /// * `blocks` - Its basic block count.
    /// * `out` - Where the comment goes.
    fn cut(&mut self, name: &str, entry: u64, blocks: usize, out: &mut String) {
        self.cut += 1;
        let _ = writeln!(
            out,
            "// {name} @ {entry:#x}: cut, not decompiled: its {blocks} blocks are over the export's budget of {BUDGET_BLOCKS} blocks a function; `decompile` writes it alone\n"
        );
    }

    /// Splits one function's finished text: hoists its file-scope
    /// declarations and writes the rest as a C definition, one local per
    /// declaration line (`T a;` and `T *b;` for `T a, *b;`), the form
    /// tools that read the file one declaration at a time expect.
    ///
    /// # Arguments
    ///
    /// * `name` - The function's name, for a text with no signature.
    /// * `entry` - Its entry.
    /// * `text` - Its decompilation, `None` when it failed.
    /// * `out` - Where the definition goes.
    pub fn add(&mut self, name: &str, entry: u64, text: Option<&str>, out: &mut String) {
        let Some(text) = text else {
            self.failed += 1;
            let _ = writeln!(out, "// {name} @ {entry:#x}: does not decompile\n");
            return;
        };
        self.written += 1;
        let lines: Vec<&str> = text.lines().collect();
        let comments = lines.iter().take_while(|l| l.starts_with("//")).count();
        let decls_end = super::declarations_end(text).unwrap_or(comments);
        let bare = super::expr_render::bare(name);
        let head = lines
            .iter()
            .take(comments)
            .find_map(|l| l.strip_prefix("// signature: "))
            .map_or_else(|| format!("void {bare}(void)"), |s| s.trim().to_owned());
        let proto = format!("{head};");
        let kept = self.defined.add(&declared_name(&head), &proto);
        self.conflict(kept, &proto);
        if let Some(first) = lines.first().filter(|l| l.starts_with("//")) {
            let _ = writeln!(out, "{first}");
        }
        let _ = writeln!(out, "{head}\n{{");
        let mut locals = false;
        for line in lines.get(comments..decls_end).unwrap_or_default() {
            match classify(line, &self.functions) {
                Some(kind) => self.hoist(kind, line),
                None => {
                    locals = true;
                    match super::vars::declaration(line) {
                        Some((ty, items)) if items.len() > 1 => {
                            for (stars, name) in items {
                                let _ = writeln!(out, "  {ty} {stars}{name};");
                            }
                        }
                        _ => {
                            let _ = writeln!(out, "  {line}");
                        }
                    }
                }
            }
        }
        let body = lines.get(decls_end..).unwrap_or_default();
        let blank = body.iter().take_while(|l| l.is_empty()).count();
        let skip = if locals { 0 } else { blank };
        for line in body.get(skip..).unwrap_or_default() {
            if line.is_empty() {
                out.push('\n');
            } else {
                let _ = writeln!(out, "  {line}");
            }
        }
        out.push_str("}\n\n");
    }

    /// Writes the top of the file: a comment saying what it is, the
    /// [`PRELUDE`], then the hoisted declarations once each: types,
    /// helpers, the binary's `static inline` functions the file does not
    /// define, prototypes (a written function's from its signature, then
    /// the other `extern` ones), then tables and globals.
    ///
    /// # Arguments
    ///
    /// * `binary` - The binary's name, for the comment.
    ///
    /// # Returns
    ///
    /// The text the function definitions follow.
    #[must_use]
    pub fn head(&self, binary: &str) -> String {
        let cut = if self.cut == 0 {
            String::new()
        } else {
            format!(
                ", {} cut over the budget of {BUDGET_BLOCKS} blocks a function",
                self.cut
            )
        };
        let mut out = format!(
            "/* {binary}: {} functions decompiled by borer, leaves first; {} did not decompile{cut}, {} library functions and stubs left out.\n   Rough pseudo-C: it says what the binary does, and is not the source it was built from. */\n",
            self.written, self.failed, self.left_out
        );
        out.push_str(PRELUDE);
        let all = |o: &Ordered| -> Vec<String> { o.lines.iter().map(|(_, l)| l.clone()).collect() };
        let undefined = |o: &Ordered| -> Vec<String> {
            o.lines
                .iter()
                .filter(|(k, _)| !self.defined.has(k))
                .map(|(_, l)| l.clone())
                .collect()
        };
        let mut prototypes = all(&self.defined);
        prototypes.extend(undefined(&self.externs));
        let sections = [
            ("types", all(&self.types)),
            ("helpers, imports and runtime functions", all(&self.helpers)),
            (
                "functions the export does not write",
                undefined(&self.inlines),
            ),
            ("prototypes", prototypes),
            ("data", all(&self.data)),
        ];
        for (title, lines) in sections {
            if lines.is_empty() {
                continue;
            }
            let _ = writeln!(out, "\n/* {title} */");
            for line in lines {
                let _ = writeln!(out, "{line}");
            }
        }
        if !self.conflicting.is_empty() {
            let _ = writeln!(
                out,
                "\n/* {} declarations a later function stated otherwise; the first is kept above. Showing {} of {}: */",
                self.conflicts,
                self.conflicting.len(),
                self.conflicts
            );
            for line in &self.conflicting {
                let _ = writeln!(out, "// {line}");
            }
        }
        out.push('\n');
        out
    }
}

/// Reads what a declaration line hoisted to file scope is, or `None` for a
/// local the function keeps.
///
/// # Arguments
///
/// * `line` - One line of a text's declarations.
/// * `functions` - The names of the binary's functions, as a text spells
///   them.
fn classify(line: &str, functions: &BTreeSet<String>) -> Option<Kind> {
    if line.starts_with("typedef ") {
        Some(Kind::Type)
    } else if line.starts_with("#define ") || line.starts_with("#undef ") {
        Some(Kind::Macro)
    } else if line.starts_with("extern ") || line.starts_with("static inline ") {
        Some(if !functions.contains(&declared_name(line)) {
            Kind::Runtime
        } else if line.starts_with("extern ") {
            Kind::Extern
        } else {
            Kind::Inline
        })
    } else if line.starts_with("static ") || line.contains("; // @ 0x") {
        Some(Kind::Data)
    } else {
        None
    }
}

/// Reads the name a file-scope declaration declares.
///
/// That is the function of a prototype or definition, the pointer of a
/// pointer declarator (a table of function pointers, a global function
/// pointer), else the last identifier before an initializer, a bound or
/// the `;`.
///
/// # Arguments
///
/// * `line` - The declaration.
///
/// # Returns
///
/// The name, or the whole line when none reads out.
fn declared_name(line: &str) -> String {
    let code = line.split(" //").next().unwrap_or(line);
    let code = code.split(" = ").next().unwrap_or(code);
    let ident = |s: &str| {
        let s = s.trim_end();
        let mut depth = 0i32;
        let mut start = 0;
        for (i, c) in s.char_indices().rev() {
            match c {
                '>' | ')' => depth += 1,
                '<' | '(' => depth -= 1,
                ' ' | '*' | '&' if depth <= 0 => {
                    start = i + c.len_utf8();
                    break;
                }
                _ => {}
            }
        }
        s.get(start..).unwrap_or_default().to_owned()
    };
    let mut depth = 0i32;
    let open = code.char_indices().find_map(|(i, c)| {
        match c {
            '<' => depth += 1,
            '>' => depth -= 1,
            '(' if depth <= 0 => return Some(i),
            _ => {}
        }
        None
    });
    let split = open.and_then(|i| Some((code.get(..i)?, code.get(i + 1..)?)));
    let name = match split {
        Some((_, rest)) if rest.starts_with('*') => {
            let rest = rest.trim_start_matches('*').trim_start();
            let rest = rest.strip_prefix("const ").unwrap_or(rest);
            ident(rest.split(['[', ')']).next().unwrap_or(rest))
        }
        Some((head, _)) => ident(head),
        None => ident(code.trim_end_matches(';').split('[').next().unwrap_or(code)),
    };
    if name.is_empty() {
        line.to_owned()
    } else {
        name
    }
}

/// Exports every function the binary holds as one C file.
///
/// The functions are rendered across the cores ([`in_order`]) and their
/// definitions go to `sink` in [`order`], a megabyte or so at a time, so
/// the memory held is the window of texts [`in_order`] keeps and the
/// declarations hoisted so far. The file is [`Hoisted::head`] followed by
/// everything `sink` received.
///
/// # Arguments
///
/// * `program` - The loaded binary.
/// * `analysis` - Its analysis.
/// * `overlay` - Names, types and comments to apply.
/// * `library` - Whether library code is written.
/// * `only` - Entries to write. `None` writes every function [`order`]
///   keeps. An entry that is not one of those is skipped, and the
///   declarations the written functions hoist are unchanged.
/// * `sink` - Takes each run's definitions in order.
///
/// # Returns
///
/// The hoisted declarations and the counts.
///
/// # Errors
///
/// The first error `sink` returns, which stops the export.
pub fn export(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    library: Library,
    only: Option<&BTreeSet<u64>>,
    sink: &mut dyn FnMut(&str) -> anyhow::Result<()>,
) -> anyhow::Result<Hoisted> {
    let mut entries = order(analysis, library);
    let left_out = analysis.functions.len().saturating_sub(entries.len());
    if let Some(only) = only {
        let arm = program.arch == crate::program::Arch::Arm;
        entries.retain(|entry| only.contains(entry) || (arm && only.contains(&(entry | 1))));
    }
    let mut hoisted = Hoisted::new(
        analysis
            .functions
            .iter()
            .map(|f| super::expr_render::bare(&name_of(analysis, overlay, f.entry)).into_owned())
            .collect(),
    );
    hoisted.left_out = left_out;
    let over = |entry: u64| {
        analysis
            .function(entry)
            .map(|f| f.blocks.len())
            .filter(|&n| n > BUDGET_BLOCKS)
    };
    let render = |entry: u64| {
        over(entry)
            .is_none()
            .then(|| named(program, analysis, overlay, entry))
            .flatten()
    };
    let mut out = String::new();
    let cost = |entry: u64| match over(entry) {
        Some(_) => 0,
        None => analysis.function(entry).map_or(0, |f| f.blocks.len()),
    };
    let window = Window::export(entries.len());
    in_order(&entries, window, &cost, &render, &mut |entry, text| {
        let name = name_of(analysis, overlay, entry);
        match over(entry) {
            Some(blocks) => hoisted.cut(&name, entry, blocks, &mut out),
            None => hoisted.add(&name, entry, text.as_deref(), &mut out),
        }
        if out.len() < SINK_BYTES {
            return Ok(());
        }
        sink(&out)?;
        out.clear();
        Ok(())
    })?;
    sink(&out)?;
    Ok(hoisted)
}

/// Renders one function as [`super::decompile_named_afresh`] does, the
/// same text, but reads a small function's plain text through the memo.
///
/// The unit of each caller defines its small callees
/// ([`super::unit::BODY_INSTRUCTIONS_MAX`] instructions at most) from
/// their plain text through the memo ([`crate::analysis::decompiled_cached`]);
/// the export reading such a text through it too decompiles each small
/// function once instead of twice. Any other function's text is built
/// afresh, so the memo does not fill with the whole binary.
///
/// # Arguments
///
/// * `program` - The loaded binary.
/// * `analysis` - Its analysis, holding the memo.
/// * `overlay` - Names, types and comments to apply.
/// * `entry` - The function's entry.
///
/// # Returns
///
/// The text, `None` when the function does not decompile.
fn named(program: &Program, analysis: &Analysis, overlay: &Overlay, entry: u64) -> Option<String> {
    let small = analysis.function(entry)?.instr_count <= super::unit::BODY_INSTRUCTIONS_MAX;
    let text = if small {
        let key = overlay.fingerprint();
        crate::analysis::decompiled_cached(program, analysis, overlay, key, entry)
            .as_ref()
            .as_ref()?
            .text
            .clone()
    } else {
        super::decompile_plain_full(program, analysis, overlay, entry)?.text
    };
    super::name_fields(program, analysis, overlay, entry, &text)
        .map(|out| super::finished(&out, program, analysis, overlay, entry))
}

/// What the functions rendered but not yet taken, and how far the taking
/// has come, shared by the workers of [`in_order`] and its taker.
#[derive(Debug)]
struct Queue {
    /// Each finished text by its position in the entries, until taken.
    done: BTreeMap<usize, Option<String>>,
    /// Bytes of the texts in `done`.
    held: usize,
    /// The position the taker waits for next: every one before it is taken.
    taken: usize,
    /// Whether the taker stopped, so the workers stop too.
    stop: bool,
}

/// How far [`in_order`] renders ahead of the taking, and on how many
/// workers.
#[derive(Debug, Clone, Copy)]
struct Window {
    /// Workers rendering at once.
    threads: usize,
    /// Functions the workers may always render past the oldest text not
    /// yet taken, all workers together.
    ahead: usize,
    /// Bytes of finished texts held past `ahead` before a worker waits.
    held_bytes: usize,
    /// Costliest functions rendered before all others, never waiting.
    heavy: usize,
}

impl Window {
    /// Returns the export's window: one worker a core, at most one an
    /// entry, [`AHEAD_PER_CORE`], [`HELD_BYTES`] and [`HEAVY_PER_CORE`].
    ///
    /// # Arguments
    ///
    /// * `entries` - How many functions are rendered.
    fn export(entries: usize) -> Self {
        let threads = std::thread::available_parallelism()
            .map_or(1, std::num::NonZeroUsize::get)
            .min(entries);
        Self {
            threads,
            ahead: threads.saturating_mul(AHEAD_PER_CORE),
            held_bytes: HELD_BYTES,
            heavy: threads.saturating_mul(HEAVY_PER_CORE),
        }
    }
}

/// Renders `entries` across the cores and hands each text to `take` in
/// the order of `entries`, as soon as it and every one before it is done.
///
/// The workers first take the `window.heavy` costliest entries, then the
/// rest in order from one counter, with no barrier between runs: a
/// function of seconds holds up only the taking, while the other workers
/// go on rendering past the oldest text not taken, as long as the texts
/// held come to under `window.held_bytes`, and `window.ahead` functions in
/// any case, which bounds the texts held. What `take`
/// receives, and so the file, does not depend on the thread count or the
/// costs.
///
/// # Arguments
///
/// * `entries` - Function entries, in the order `take` receives them.
/// * `window` - The workers and how far they render ahead ([`Window`]).
/// * `cost` - What an entry is expected to cost, in any unit.
/// * `render` - Renders one function; `None` when it has no text.
/// * `take` - Takes each entry and its text, in order.
///
/// # Errors
///
/// The first error `take` returns, which stops the rendering.
fn in_order(
    entries: &[u64],
    window: Window,
    cost: &dyn Fn(u64) -> usize,
    render: &(dyn Fn(u64) -> Option<String> + Sync),
    take: &mut dyn FnMut(u64, Option<String>) -> anyhow::Result<()>,
) -> anyhow::Result<()> {
    use std::sync::{Condvar, Mutex, PoisonError};
    let Window {
        threads,
        ahead,
        held_bytes,
        heavy,
    } = window;
    let mut heaviest: Vec<usize> = (0..entries.len()).collect();
    heaviest.sort_by_key(|&i| (std::cmp::Reverse(entries.get(i).map_or(0, |&e| cost(e))), i));
    heaviest.truncate(heavy);
    let firsts: BTreeSet<usize> = heaviest.iter().copied().collect();
    let plan: Vec<(usize, bool)> = heaviest
        .iter()
        .map(|&i| (i, true))
        .chain(
            (0..entries.len())
                .filter(|i| !firsts.contains(i))
                .map(|i| (i, false)),
        )
        .collect();
    let plan = &plan;
    let next = std::sync::atomic::AtomicUsize::new(0);
    let queue = Mutex::new(Queue {
        done: BTreeMap::new(),
        held: 0,
        taken: 0,
        stop: false,
    });
    let (ready, room) = (Condvar::new(), Condvar::new());
    let (next, queue, ready, room) = (&next, &queue, &ready, &room);
    let here = super::super::reads::Handle::here();
    std::thread::scope(|scope| {
        let mut workers = 0;
        for _ in 0..threads {
            let here = here.clone();
            let worker = super::stack::worker(scope, move || {
                here.enter(|| {
                    loop {
                        let k = next.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                        let Some((i, first)) = plan.get(k).copied() else {
                            break;
                        };
                        let Some(&entry) = entries.get(i) else { break };
                        let mut q = queue.lock().unwrap_or_else(PoisonError::into_inner);
                        while !q.stop
                            && !first
                            && i >= q.taken.saturating_add(ahead)
                            && q.held >= held_bytes
                        {
                            q = room.wait(q).unwrap_or_else(PoisonError::into_inner);
                        }
                        if q.stop {
                            break;
                        }
                        drop(q);
                        let text = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                            render(entry)
                        }));
                        let mut q = queue.lock().unwrap_or_else(PoisonError::into_inner);
                        let text = text.ok().flatten();
                        q.held = q.held.saturating_add(text.as_ref().map_or(0, String::len));
                        q.done.insert(i, text);
                        ready.notify_one();
                    }
                });
            });
            workers += usize::from(worker.is_some());
        }
        let result = 'take: {
            for (i, &entry) in entries.iter().enumerate() {
                let text = if workers == 0 {
                    render(entry)
                } else {
                    let mut q = queue.lock().unwrap_or_else(PoisonError::into_inner);
                    let text = loop {
                        if let Some(text) = q.done.remove(&i) {
                            q.held = q.held.saturating_sub(text.as_ref().map_or(0, String::len));
                            break text;
                        }
                        q = ready.wait(q).unwrap_or_else(PoisonError::into_inner);
                    };
                    q.taken = i + 1;
                    room.notify_all();
                    text
                };
                if let Err(e) = take(entry, text) {
                    break 'take Err(e);
                }
            }
            Ok(())
        };
        queue.lock().unwrap_or_else(PoisonError::into_inner).stop = true;
        room.notify_all();
        result
    })
}

#[cfg(test)]
mod tests {
    use super::{
        BTreeSet, BUDGET_BLOCKS, Hoisted, Kind, Library, Window, classify, declared_name, export,
        in_order,
    };
    use crate::analysis::{Analysis, Overlay};
    use crate::program::{Arch, Program, Section};
    use std::sync::atomic::{AtomicUsize, Ordering};
    use std::time::Duration;

    /// A function over the budget is cut to a comment, and the functions
    /// around it, its callees, are still written whole.
    ///
    /// # Panics
    ///
    /// When the large function is decompiled, or a neighbour is not.
    #[test]
    fn a_function_over_the_budget_is_cut_and_its_neighbours_written() {
        let mut code = vec![0xccu8; 0x20];
        code[..6].copy_from_slice(&[0xb8, 0x01, 0x00, 0x00, 0x00, 0xc3]); // ASM: mov eax, 1; ret
        code[0x10..0x16].copy_from_slice(&[0xb8, 0x02, 0x00, 0x00, 0x00, 0xc3]); // ASM: mov eax, 2; ret
        code.extend([0xe8, 0xdb, 0xff, 0xff, 0xff]); // ASM: call 0x1000
        code.extend([0xe8, 0xe6, 0xff, 0xff, 0xff]); // ASM: call 0x1010
        for _ in 0..BUDGET_BLOCKS / 2 + 1 {
            code.extend([0x85, 0xc0, 0x74, 0x02, 0xff, 0xc1, 0xff, 0xc0]); // ASM: test eax, eax; je +2; inc ecx; inc eax
        }
        code.push(0xc3); // ASM: ret
        let len = u64::try_from(code.len()).expect("a small image");
        let text = Section::mapped(".text", 0x1000, 0, len, false, true);
        let p = Program::raw(code, Arch::X86_64, 0, Some(0x1020), vec![text]);
        let a = Analysis::compute(&p);
        let mut c = String::new();
        let h = export(&p, &a, &Overlay::default(), Library::Skip, None, &mut |t| {
            c.push_str(t);
            Ok(())
        })
        .expect("the sink takes everything");
        assert_eq!((h.written, h.cut, h.failed), (2, 1, 0), "{c}");
        let blocks = a.function(0x1020).map_or(0, |f| f.blocks.len());
        assert!(blocks > BUDGET_BLOCKS);
        let note = format!("// sub_1020 @ 0x1020: cut, not decompiled: its {blocks} blocks");
        assert!(c.contains(&note), "{c}");
        assert!(!c.contains("sub_1020()\n{"), "{c}");
        assert!(c.contains(" sub_1000()\n{\n  return 1;\n}"), "{c}");
        assert!(c.contains(" sub_1010()\n{\n  return 2;\n}"), "{c}");
        assert!(h.head("t").contains("1 cut over the budget"), "{c}");
    }

    /// The texts come to the taker in the order of the entries, however the
    /// workers finish, and an error from the taker stops the rendering and
    /// is returned.
    ///
    /// # Panics
    ///
    /// When a text comes out of order, is lost, or the error is not
    /// returned.
    #[test]
    fn texts_are_taken_in_order_and_an_error_stops_them() {
        let entries: Vec<u64> = (0..20_000).rev().collect();
        let render = |e: u64| (!e.is_multiple_of(7)).then(|| format!("{e}"));
        let mut seen = Vec::new();
        in_order(
            &entries,
            Window::export(entries.len()),
            &|e| usize::try_from(e % 97).unwrap_or(0),
            &render,
            &mut |e, text| {
                assert_eq!(text, render(e));
                seen.push(e);
                Ok(())
            },
        )
        .expect("the taker takes everything");
        assert_eq!(seen, entries);
        let mut taken = 0;
        let window = Window::export(entries.len());
        let stopped = in_order(&entries, window, &|_| 0, &render, &mut |_, _| {
            taken += 1;
            if taken == 5_000 {
                anyhow::bail!("full");
            }
            Ok(())
        });
        assert!(stopped.is_err_and(|e| e.to_string() == "full"));
        assert_eq!(taken, 5_000);
    }

    /// Four workers that may render 8 functions past the oldest text not
    /// taken, and hold 1 byte past that: a window the tests fill.
    const NARROW: Window = Window {
        threads: 4,
        ahead: 8,
        held_bytes: 1,
        heavy: 0,
    };

    /// Runs `f` on a thread of its own and returns what it returns, or
    /// fails when it takes over 30 seconds: an [`in_order`] whose workers
    /// are never woken would hang the test instead of failing it.
    ///
    /// # Arguments
    ///
    /// * `f` - The work.
    ///
    /// # Panics
    ///
    /// When `f` does not return in time.
    fn within<T: Send + 'static>(f: impl FnOnce() -> T + Send + 'static) -> T {
        let (tx, rx) = std::sync::mpsc::channel();
        std::thread::spawn(move || tx.send(f()).expect("the test waits for the result"));
        rx.recv_timeout(Duration::from_secs(30))
            .expect("in_order returns in time")
    }

    /// Renders entry 0 only once the other workers have rendered every
    /// function the window lets them past it and stopped, and tells how
    /// many they had rendered then.
    ///
    /// # Arguments
    ///
    /// * `rendered` - Functions other than entry 0 rendered so far.
    /// * `at_release` - Where the count when entry 0 finishes is kept.
    /// * `e` - The entry to render.
    fn slow_first(rendered: &AtomicUsize, at_release: &AtomicUsize, e: u64) -> Option<String> {
        if e == 0 {
            for _ in 0..10_000 {
                if rendered.load(Ordering::SeqCst) >= NARROW.ahead - 1 {
                    break;
                }
                std::thread::sleep(Duration::from_millis(1));
            }
            std::thread::sleep(Duration::from_millis(200));
            at_release.store(rendered.load(Ordering::SeqCst), Ordering::SeqCst);
        } else {
            rendered.fetch_add(1, Ordering::SeqCst);
        }
        Some(format!("{e}"))
    }

    /// While the first text is slow, the workers render only the window
    /// past it and wait; once it is taken they go on, and every text comes
    /// to the taker in order.
    ///
    /// # Panics
    ///
    /// When the workers do not wait, are not woken, or a text comes out of
    /// order.
    #[test]
    fn workers_wait_behind_a_slow_first_text_and_resume_once_it_is_taken() {
        let (seen, at_release) = within(|| {
            let entries: Vec<u64> = (0..200).collect();
            let rendered = AtomicUsize::new(0);
            let at_release = AtomicUsize::new(0);
            let mut seen = Vec::new();
            in_order(
                &entries,
                NARROW,
                &|_| 0,
                &|e| slow_first(&rendered, &at_release, e),
                &mut |e, text| {
                    assert_eq!(text, Some(format!("{e}")));
                    seen.push(e);
                    Ok(())
                },
            )
            .expect("the taker takes everything");
            (seen, at_release.load(Ordering::SeqCst))
        });
        assert_eq!(at_release, NARROW.ahead - 1);
        assert_eq!(seen, (0..200).collect::<Vec<u64>>());
    }

    /// An error from the taker while workers wait for room wakes them all,
    /// and the error comes back.
    ///
    /// # Panics
    ///
    /// When the call hangs, the workers had not filled the window, or the
    /// error is lost.
    #[test]
    fn an_error_while_workers_wait_releases_them_and_is_returned() {
        let (stopped, at_release, taken) = within(|| {
            let entries: Vec<u64> = (0..200).collect();
            let rendered = AtomicUsize::new(0);
            let at_release = AtomicUsize::new(0);
            let mut taken = 0;
            let stopped = in_order(
                &entries,
                NARROW,
                &|_| 0,
                &|e| slow_first(&rendered, &at_release, e),
                &mut |_, _| {
                    taken += 1;
                    anyhow::bail!("full")
                },
            );
            (
                stopped.map_err(|e| e.to_string()),
                at_release.load(Ordering::SeqCst),
                taken,
            )
        });
        assert_eq!(stopped, Err("full".to_owned()));
        assert_eq!(at_release, NARROW.ahead - 1);
        assert_eq!(taken, 1);
    }

    /// Each kind of file-scope line names what it declares.
    ///
    /// # Panics
    ///
    /// When a name reads otherwise.
    #[test]
    fn declarations_name_what_they_declare() {
        assert_eq!(declared_name("extern uint64_t f(uint64_t);"), "f");
        assert_eq!(
            declared_name("static inline uint32_t g(uint32_t a1) { return a1; }"),
            "g"
        );
        assert_eq!(
            declared_name("static uint32_t (*const ops[4])(uint32_t, uint32_t) = {a, b, a, b};"),
            "ops"
        );
        assert_eq!(
            declared_name("static const uint128_t g128_10f0 = 0x1; // @ 0x10f0"),
            "g128_10f0"
        );
        assert_eq!(declared_name("uint8_t g_4010[16]; // @ 0x4010"), "g_4010");
        assert_eq!(
            declared_name("uint32_t Cache::Key::Append(void *a1, uint16_t *a2);"),
            "Cache::Key::Append"
        );
        assert_eq!(
            declared_name("void out_t<ptr<f<void (*)(void *)> > >::~out_t(void *a1);"),
            "out_t<ptr<f<void (*)(void *)> > >::~out_t"
        );
        assert_eq!(
            declared_name("uint64_t (*g64_c888)(uint64_t); // @ 0xc888"),
            "g64_c888"
        );
        assert_eq!(
            declared_name("extern uint64_t apply(uint64_t (*a1)(uint64_t), uint32_t a2);"),
            "apply"
        );
    }

    /// Locals stay in the function and file-scope lines are hoisted.
    ///
    /// # Panics
    ///
    /// When a line is classified otherwise.
    #[test]
    fn locals_stay_and_file_scope_lines_go() {
        let f: BTreeSet<String> = ["f".to_owned()].into();
        assert_eq!(classify("uint64_t var1, var2;", &f), None);
        assert_eq!(
            classify(
                "typedef uint32_t u32x4 __attribute__((vector_size(16)));",
                &f
            ),
            Some(Kind::Type)
        );
        assert_eq!(
            classify("extern uint64_t f(uint64_t);", &f),
            Some(Kind::Extern)
        );
        assert_eq!(
            classify("static inline uint64_t f(uint64_t a1) { return a1; }", &f),
            Some(Kind::Inline)
        );
        assert_eq!(
            classify(
                "static inline uint64_t mulhi64(uint64_t a, uint64_t b) { return a; }",
                &f
            ),
            Some(Kind::Runtime)
        );
        assert_eq!(
            classify("#define bswap(x) bswap64(x)", &f),
            Some(Kind::Macro)
        );
        assert_eq!(
            classify("uint32_t g_4010; // @ 0x4010", &f),
            Some(Kind::Data)
        );
    }

    /// Two functions sharing a prototype declare it once.
    ///
    /// A function the file defines is declared by its own signature, not
    /// the other's extern, and a later function's other prototype for a
    /// name is counted and shown as a conflict.
    ///
    /// # Panics
    ///
    /// When a declaration is repeated, lost or miscounted, or a grouped
    /// local declaration is not written one local per line with its stars.
    #[test]
    fn shared_declarations_are_hoisted_once() {
        let mut h = Hoisted::new(["a", "b", "c"].map(str::to_owned).into());
        let mut body = String::new();
        let a = "// a @ 0x10\n// signature: uint64_t a(uint64_t a1)\nextern uint64_t c(uint64_t);\nuint64_t var1;\n\nreturn c(a1);\n";
        let b = "// b @ 0x20\n// signature: uint32_t b(void)\nextern uint64_t c(uint64_t);\nextern uint64_t a(uint64_t);\n\nreturn a(c(1));\n";
        h.add("a", 0x10, Some(a), &mut body);
        h.add("b", 0x20, Some(b), &mut body);
        h.add("d", 0x30, None, &mut body);
        let other = "// c2 @ 0x40\n// signature: uint32_t c2(void)\nextern uint32_t c(uint64_t);\n\nreturn 0;\n";
        h.add("c2", 0x40, Some(other), &mut body);
        let head = h.head("t.so");
        assert_eq!(
            head.matches("extern uint64_t c(uint64_t);").count(),
            1,
            "{head}"
        );
        assert!(!head.contains("extern uint64_t a("), "{head}");
        assert!(head.contains("uint64_t a(uint64_t a1);"), "{head}");
        assert!(
            body.contains("uint64_t a(uint64_t a1)\n{\n  uint64_t var1;\n\n  return c(a1);\n}\n"),
            "{body}"
        );
        assert!(body.contains("// d @ 0x30: does not decompile"), "{body}");
        assert_eq!((h.written, h.failed, h.conflicts), (3, 1, 1));
        let mut grouped = Hoisted::new(["f"].map(str::to_owned).into());
        let mut out = String::new();
        let f = "// f @ 0x10\n// signature: void f(void)\nuint64_t a, *b, **c;\nuint8_t buf[4];\n\nreturn;\n";
        grouped.add("f", 0x10, Some(f), &mut out);
        assert!(
            out.contains("  uint64_t a;\n  uint64_t *b;\n  uint64_t **c;\n  uint8_t buf[4];\n"),
            "{out}"
        );
        assert!(
            head.contains("\n// extern uint32_t c(uint64_t);\n"),
            "{head}"
        );
    }
}
