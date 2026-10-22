//! Whole-binary export: every function's pseudo-C as one C file.
//!
//! Each function is decompiled as the `decompile` tool shows it
//! ([`decompile_named_all`]), its translation-unit closure included, and
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
//! import rather than code of the program's own.
//!
//! [`export`] renders a bounded run of functions at a time across the
//! cores and hands each finished definition to a sink in order, so memory
//! holds one run of texts and the hoisted declarations, never the file;
//! the caller writes [`Hoisted::head`] above what the sink received.

use super::{
    Analysis, BTreeMap, BTreeSet, Function, Overlay, Program, decompile_named_all, name_of,
};
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

/// Functions rendered at once per core: enough to keep every core busy
/// past a run's few large functions, few enough that a run's texts stay
/// small.
const RUN_PER_CORE: usize = 32;

/// Most declarations stated two ways the head of the file names.
const CONFLICTS_SHOWN: usize = 8;

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
        let mut out = format!(
            "/* {binary}: {} functions decompiled by borer, leaves first; {} did not decompile, {} library functions and stubs left out.\n   Rough pseudo-C: it says what the binary does, and is not the source it was built from. */\n",
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

/// Exports every function the binary holds as one C file, a run of
/// functions at a time.
///
/// Each run is rendered across the cores ([`decompile_named_all`]) and
/// its definitions go to `sink` in [`order`]; the run's texts are dropped
/// before the next is rendered, so the memory held is one run's texts and
/// the declarations hoisted so far. The file is [`Hoisted::head`] followed
/// by everything `sink` received.
///
/// # Arguments
///
/// * `program` - The loaded binary.
/// * `analysis` - Its analysis.
/// * `overlay` - Names, types and comments to apply.
/// * `library` - Whether library code is written.
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
    sink: &mut dyn FnMut(&str) -> anyhow::Result<()>,
) -> anyhow::Result<Hoisted> {
    let entries = order(analysis, library);
    let mut hoisted = Hoisted::new(
        analysis
            .functions
            .iter()
            .map(|f| super::expr_render::bare(&name_of(analysis, overlay, f.entry)).into_owned())
            .collect(),
    );
    hoisted.left_out = analysis.functions.len().saturating_sub(entries.len());
    let run = std::thread::available_parallelism()
        .map_or(1, std::num::NonZeroUsize::get)
        .saturating_mul(RUN_PER_CORE);
    for chunk in entries.chunks(run) {
        let texts = decompile_named_all(program, analysis, overlay, chunk);
        let mut out = String::new();
        for (&entry, text) in chunk.iter().zip(&texts) {
            let name = name_of(analysis, overlay, entry);
            hoisted.add(&name, entry, text.as_deref(), &mut out);
        }
        sink(&out)?;
    }
    Ok(hoisted)
}

#[cfg(test)]
mod tests {
    use super::{BTreeSet, Hoisted, Kind, classify, declared_name};

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
