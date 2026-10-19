//! Translation-unit closure: every name a function's text uses, declared
//! in the text.
//!
//! A decompilation a reader compiles is a translation unit, not a lone
//! function. Its body calls other functions, indexes tables of them and
//! calls runtime helpers, and each of those names needs a declaration
//! before the body for the text to mean what the binary does. The closure
//! adds them after the header comments, each name once, in a fixed order:
//!
//! - a prototype, `extern uint64_t h_is_odd(uint64_t);`, for each function
//!   the binary exports, from its ABI facts alone
//!   ([`prototype`](abi::function::prototype)), so two functions that call
//!   each other declare each other in either order; a runtime helper's
//!   prototype from the runtime table ([`crate::analysis::runtime`]); and the C library's
//!   declaration of a function or import it names, when the type library
//!   states it in C's own types;
//! - the body of each small leaf function the binary does not export, as
//!   a `static inline` definition on one line, within [`BODIES_MAX`]
//!   bodies of [`BODY_MAX`] bytes: nothing outside the unit defines them,
//!   and a body that names nothing but its own parameters and locals
//!   needs nothing more declared;
//! - each table of function addresses the text indexes in read-only data,
//!   an array of function designators initialized from the image.
//!
//! A name a call passes another argument count than its declaration
//! states stays undeclared: the declaration would refuse the text rather
//! than describe it.

use super::*;
use crate::program::SymbolKind;
use helper::Helper;
use std::sync::Arc;

/// Most bytes a function's body may take on its one line to be defined in
/// a unit that calls it.
const BODY_MAX: usize = 240;

/// Most function bodies one unit defines.
const BODIES_MAX: usize = 8;

/// Most instructions a function may have for a unit to try defining it.
const BODY_INSTRUCTIONS_MAX: usize = 32;

/// The C keywords and constants a defined body may use besides its types.
const C_WORDS: [&str; 16] = [
    "if", "else", "while", "for", "do", "switch", "case", "default", "break", "continue", "return",
    "goto", "sizeof", "nullptr", "true", "false",
];

/// Most entries a table of function addresses is written out with.
const TABLE_MAX: usize = 256;

/// The names a unit resolves, read once per program and names in force.
#[derive(Debug, Default)]
struct Index {
    /// Each function's name as the text spells it, to its entry; the
    /// lowest entry of several that share a name.
    functions: BTreeMap<String, u64>,
    /// The addresses the binary exports a symbol at.
    exported: BTreeSet<u64>,
    /// Each data symbol's name as the text spells it, to its address.
    data: BTreeMap<String, u64>,
    /// The imports' names, as the text spells them.
    imports: BTreeSet<String>,
}

/// Returns the [`Index`] of a program under the names in force, built once
/// through [`Analysis::derived`].
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Its functions.
/// * `overlay` - User names.
fn index(program: &Program, analysis: &Analysis, overlay: &Overlay) -> Arc<Index> {
    analysis
        .derived
        .get_or_build_named("unit_index", overlay.fingerprint(), (), || {
            let mut ix = Index::default();
            for f in &analysis.functions {
                let name = expr::bare(&name_of(analysis, overlay, f.entry)).to_owned();
                ix.functions.entry(name).or_insert(f.entry);
            }
            for s in &program.symbols {
                match s.kind {
                    SymbolKind::Import => {
                        ix.imports.insert(expr::bare(&s.name).to_owned());
                    }
                    SymbolKind::Export | SymbolKind::Local | SymbolKind::Data => {
                        if s.kind == SymbolKind::Export {
                            ix.exported.insert(s.addr);
                        }
                        if s.addr != 0 && analysis.function(s.addr).is_none() {
                            ix.data
                                .entry(expr_render::data_name(&s.name))
                                .or_insert(s.addr);
                        }
                    }
                    SymbolKind::Forwarder => {}
                }
            }
            ix
        })
}

/// A function's C type: what a pointer to it is declared with.
#[derive(Debug, Clone, PartialEq, Eq)]
struct FnTy {
    /// The return type.
    ret: String,
    /// The parameter types, in order.
    params: Vec<String>,
    /// Whether it takes `...` past them.
    variadic: bool,
}

/// How the unit declares one function name.
#[derive(Debug, Clone, PartialEq, Eq)]
enum Declared {
    /// A prototype for a definition outside the unit: the line.
    Extern(String),
    /// A definition in the unit: its signature and its body on one line.
    Static {
        /// The signature, `uint32_t op_add(uint64_t a1, uint64_t a2)`.
        sig: String,
        /// The statements, joined by spaces.
        body: String,
    },
}

/// One declared function: how, and its C type.
#[derive(Debug, Clone, PartialEq, Eq)]
struct Decl {
    /// The declaration.
    how: Declared,
    /// The function's type.
    ty: FnTy,
}

/// A table of function addresses the text indexes.
#[derive(Debug, Clone, PartialEq, Eq)]
struct Table {
    /// The text's spelling of its address, `((uint64_t*)0x4050)` or
    /// `&h_dispatch_ops`.
    spelled: String,
    /// What the text spells it as once declared.
    renamed: String,
    /// The array's name.
    name: String,
    /// The functions' names, in table order.
    entries: Vec<String>,
}

/// Declares, after the header comments, every function, runtime helper,
/// import and function table the text uses that no other line declares.
///
/// # Arguments
///
/// * `text` - A finished decompilation, before its helpers are defined
///   ([`helper::declare`]).
/// * `program` - The loaded image.
/// * `analysis` - Its functions.
/// * `overlay` - User names.
/// * `entry` - The decompiled function's entry.
///
/// # Returns
///
/// The text as a translation unit, or unchanged when it uses nothing
/// undeclared.
pub(super) fn close(
    text: &str,
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    entry: u64,
) -> String {
    let ix = index(program, analysis, overlay);
    let own = expr::bare(&name_of(analysis, overlay, entry)).to_owned();
    let mut tables = designators(text, program, analysis, overlay, &ix);
    let mut names = words(text);
    names.extend(tables.iter().flat_map(|t| t.entries.iter().cloned()));
    let mut decls: BTreeMap<String, Decl> = BTreeMap::new();
    let mut bodies = 0usize;
    for name in names {
        if name == own || decls.contains_key(&name) || Helper::parse(&name).is_some() {
            continue;
        }
        let define = bodies < BODIES_MAX;
        if let Some(decl) = declaration(program, analysis, overlay, &ix, &name, define) {
            bodies += usize::from(matches!(decl.how, Declared::Static { .. }));
            decls.insert(name, decl);
        }
    }
    decls.retain(|name, d| {
        let want = d.ty.params.len();
        call_arities(text, name)
            .into_iter()
            .all(|n| n == want || d.ty.variadic && n > want)
    });
    let sig = text
        .lines()
        .find_map(|l| l.strip_prefix("// signature: "))
        .map(str::trim);
    tables.retain(|t| {
        t.entries
            .iter()
            .all(|e| decls.contains_key(e) || (*e == own && sig.is_some()))
    });
    let mut head: Vec<String> = Vec::new();
    if tables.iter().any(|t| t.entries.contains(&own))
        && let Some(sig) = sig
    {
        head.push(format!("extern {sig};"));
    }
    head.extend(decls.values().filter_map(|d| match &d.how {
        Declared::Extern(line) => Some(line.clone()),
        Declared::Static { .. } => None,
    }));
    head.extend(decls.values().filter_map(|d| match &d.how {
        Declared::Static { sig, body } => Some(format!("static inline {sig} {{ {body} }}")),
        Declared::Extern(_) => None,
    }));
    let own_ty = sig.and_then(|s| fn_ty(s, &own));
    for t in &tables {
        let tys: Vec<Option<&FnTy>> = t
            .entries
            .iter()
            .map(|e| decls.get(e).map(|d| &d.ty).or(own_ty.as_ref()))
            .collect();
        head.push(table_line(t, &tys));
    }
    if head.is_empty() {
        return text.to_owned();
    }
    let mut lines: Vec<String> = text
        .lines()
        .map(|l| {
            let mut l = l.to_owned();
            if !l.starts_with("//") {
                for t in &tables {
                    l = l.replace(&t.spelled, &t.renamed);
                }
            }
            l
        })
        .collect();
    let at = header_len(&lines);
    lines.splice(at..at, head);
    let mut out = lines.join("\n");
    out.push('\n');
    out
}

/// Returns how the unit declares one name the text uses, when it names a
/// runtime helper, a function or an import the unit can declare.
///
/// A runtime helper gets its libgcc prototype, and a function or import
/// the C library names gets the library's. Of the program's own
/// functions, a small leaf the binary does not export is defined
/// ([`definition`]) and any other is declared from its ABI facts.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Its functions.
/// * `overlay` - User names.
/// * `ix` - The program's names.
/// * `name` - The name.
/// * `define` - Whether the unit may define one more body.
fn declaration(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    ix: &Index,
    name: &str,
    define: bool,
) -> Option<Decl> {
    if let Some(proto) = crate::analysis::runtime::helper(name).map(|h| h.proto) {
        return Some(Decl {
            how: Declared::Extern(format!("extern {proto};")),
            ty: fn_ty(proto, name)?,
        });
    }
    let function = ix.functions.get(name).copied();
    if function.is_none() && !ix.imports.contains(name) {
        return None;
    }
    if let Some(d) = library(name, program.format) {
        return Some(d);
    }
    let e = function.filter(|&e| analysis.function(e).is_some_and(|f| f.thunk.is_none()))?;
    let internal = !ix.exported.contains(&e) && !ix.exported.contains(&abi::reached(analysis, e));
    if internal
        && define
        && let Some((sig, body)) = definition(program, analysis, overlay, e, name)
    {
        return Some(Decl {
            ty: fn_ty(&sig, name)?,
            how: Declared::Static { sig, body },
        });
    }
    let p = abi::function::prototype(program, analysis, overlay, e)?;
    Some(Decl {
        how: Declared::Extern(format!("extern {}", p.declaration())),
        ty: FnTy {
            ret: p.ret.to_owned(),
            params: p.params.iter().map(|&t| t.to_owned()).collect(),
            variadic: p.variadic,
        },
    })
}

/// Returns the C library's declaration of a function, when the type
/// library states one in C's own types.
///
/// # Arguments
///
/// * `name` - The function's name.
/// * `format` - The binary's format, which picks the platform.
fn library(name: &str, format: crate::program::BinaryFormat) -> Option<Decl> {
    let d = crate::analysis::typelib::declared(name, format)
        .filter(|d| d.os == crate::analysis::typelib::Os::C)?;
    if !std::iter::once(d.ret)
        .chain(d.params.iter().map(|p| p.ty))
        .all(plain_type)
    {
        return None;
    }
    let mut params: Vec<String> = d
        .params
        .iter()
        .map(|p| format!("{} {}", p.ty, p.name))
        .collect();
    if d.variadic {
        params.push("...".to_owned());
    }
    if params.is_empty() {
        params.push("void".to_owned());
    }
    let sep = if d.ret.ends_with('*') { "" } else { " " };
    Some(Decl {
        how: Declared::Extern(format!(
            "extern {}{sep}{name}({});",
            d.ret,
            params.join(", ")
        )),
        ty: FnTy {
            ret: d.ret.to_owned(),
            params: d.params.iter().map(|p| p.ty.to_owned()).collect(),
            variadic: d.variadic,
        },
    })
}

/// Returns a small leaf function's signature and its body on one line.
///
/// The body qualifies when it fits [`BODY_MAX`] and names nothing but its
/// parameters, its own locals, C's keywords and types, its labels and the
/// helpers the prelude defines: no call, no global, no layout of a
/// pointee, no vector type.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Its functions.
/// * `overlay` - User names.
/// * `entry` - The function's entry.
/// * `name` - Its name as the text spells it.
fn definition(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    entry: u64,
    name: &str,
) -> Option<(String, String)> {
    analysis
        .function(entry)
        .filter(|f| f.entry == entry && f.instr_count <= BODY_INSTRUCTIONS_MAX)?;
    let d = decompiled_cached(program, analysis, overlay, overlay.fingerprint(), entry);
    let bitness = program.arch.bitness().unwrap_or(64);
    let text = tables::inline_tables(
        &polish(&d.as_ref().as_ref()?.text, bitness, &analysis.packs),
        program,
    );
    let notes_global = |l: &str| l.contains("// @ ") || l.contains("// TLS slot");
    if text.lines().any(|l| l.starts_with("// layout "))
        || text
            .lines()
            .filter(|l| !l.starts_with("//"))
            .any(notes_global)
        || vector::declare(&text, program) != text
    {
        return None;
    }
    let sig = text
        .lines()
        .find_map(|l| l.strip_prefix("// signature: "))?
        .trim();
    let ty = fn_ty(sig, name)?;
    if !std::iter::once(ty.ret.as_str())
        .chain(ty.params.iter().map(String::as_str))
        .all(plain_type)
    {
        return None;
    }
    let own: BTreeSet<String> = words(sig)
        .into_iter()
        .chain(words(&declarations(&text)))
        .collect();
    let body = text
        .lines()
        .filter(|l| !l.starts_with("//"))
        .map(|l| code_of(l).trim())
        .filter(|l| !l.is_empty())
        .collect::<Vec<_>>()
        .join(" ");
    let closed = words(&body).iter().all(|w| {
        own.contains(w)
            || C_WORDS.contains(&w.as_str())
            || plain_type(w)
            || Helper::parse(w).is_some()
            || label_name(&format!("{w}:")).is_some()
    });
    (closed && body.len() <= BODY_MAX).then(|| (sig.to_owned(), body))
}

/// Reads a function's type from its signature, `uint32_t f(uint64_t a1)`.
///
/// # Arguments
///
/// * `sig` - The signature, parameter names optional.
/// * `name` - The function's name in it.
///
/// # Returns
///
/// The type, or `None` when the signature does not name `name` before its
/// parameters.
fn fn_ty(sig: &str, name: &str) -> Option<FnTy> {
    let (head, rest) = sig.split_once('(')?;
    let ret = head.trim_end().strip_suffix(name)?.trim_end();
    if ret.is_empty()
        || ret.ends_with(is_ident_char) && !head.trim_end().ends_with(&format!(" {name}"))
    {
        return None;
    }
    let inner = rest.trim_end().trim_end_matches(';').strip_suffix(')')?;
    let mut params: Vec<String> = Vec::new();
    let mut variadic = false;
    for p in split_arguments(inner) {
        match p {
            "" | "void" => {}
            "..." => variadic = true,
            _ => params.push(param_type(p).to_owned()),
        }
    }
    Some(FnTy {
        ret: ret.to_owned(),
        params,
        variadic,
    })
}

/// Returns a parameter's type: the declaration without its trailing name,
/// or the whole text when it names none.
///
/// # Arguments
///
/// * `p` - One parameter, `uint64_t a1` or `const char *s`.
fn param_type(p: &str) -> &str {
    let p = p.trim();
    let name_at = p.rfind(|c: char| !is_ident_char(c)).map_or(0, |i| i + 1);
    let ty = p[..name_at].trim_end();
    if ty.is_empty() || p[name_at..].starts_with(|c: char| c.is_ascii_digit()) {
        p
    } else {
        ty
    }
}

/// Tells whether a type is spelled in C's own types: the fixed-width
/// integers, the plain arithmetic types, `size_t` and `void`, and pointers
/// to them, `const` or not.
///
/// # Arguments
///
/// * `ty` - The type.
fn plain_type(ty: &str) -> bool {
    /// The base types and qualifiers a plain type is made of.
    const WORDS: [&str; 14] = [
        "void",
        "char",
        "short",
        "int",
        "long",
        "signed",
        "unsigned",
        "float",
        "double",
        "bool",
        "const",
        "size_t",
        "uint128_t",
        "int128_t",
    ];
    let words: Vec<&str> = ty
        .split(|c: char| c == '*' || c.is_whitespace())
        .filter(|w| !w.is_empty())
        .collect();
    !words.is_empty()
        && words.iter().all(|w| {
            WORDS.contains(w)
                || w.strip_prefix("uint")
                    .or_else(|| w.strip_prefix("int"))
                    .and_then(|r| r.strip_suffix("_t"))
                    .is_some_and(|bits| matches!(bits, "8" | "16" | "32" | "64"))
        })
}

/// Returns the tables of function addresses the text indexes.
///
/// A table is spelled as a data symbol's address, `&h_dispatch_ops`, or a
/// word-sized cast of a constant, `((uint64_t*)0x4050)`, and its words in
/// read-only data are function entries.
///
/// # Arguments
///
/// * `text` - The decompilation.
/// * `program` - The loaded image.
/// * `analysis` - Its functions.
/// * `overlay` - User names.
/// * `ix` - The program's names.
fn designators(
    text: &str,
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    ix: &Index,
) -> Vec<Table> {
    let bits = if program.is_64 { 64 } else { 32 };
    let cast = format!("((uint{bits}_t*)0x");
    let mut found: BTreeMap<u64, (String, String, String)> = BTreeMap::new();
    let declared = words(&declarations(text));
    for line in text.lines().filter(|l| !l.starts_with("//")) {
        let line = code_of(line);
        for (at, _) in line.match_indices('&') {
            let rest = &line[at + 1..];
            let len = rest.find(|c: char| !is_ident_char(c)).unwrap_or(rest.len());
            let name = &rest[..len];
            if let Some(&addr) = ix.data.get(name)
                && !declared.iter().any(|d| d == name)
            {
                found
                    .entry(addr)
                    .or_insert_with(|| (format!("&{name}"), format!("&{name}"), name.to_owned()));
            }
        }
        for (at, _) in line.match_indices(&cast) {
            let rest = &line[at + cast.len()..];
            let digits = rest
                .find(|c: char| !c.is_ascii_hexdigit())
                .unwrap_or(rest.len());
            if !rest[digits..].starts_with(')') {
                continue;
            }
            let Ok(addr) = u64::from_str_radix(&rest[..digits], 16) else {
                continue;
            };
            let name = format!("g{bits}_{addr:x}");
            if mentions_ident(text, &name) {
                continue;
            }
            let spelled = format!("{cast}{})", &rest[..digits]);
            let renamed = format!("((uint{bits}_t*){name})");
            found.entry(addr).or_insert((spelled, renamed, name));
        }
    }
    found
        .into_iter()
        .filter_map(|(addr, (spelled, renamed, name))| {
            let entries = function_words(program, analysis, addr)?
                .into_iter()
                .map(|e| expr::bare(&name_of(analysis, overlay, e)).to_owned())
                .collect();
            Some(Table {
                spelled,
                renamed,
                name,
                entries,
            })
        })
        .collect()
}

/// Returns the run of function entries the words at `addr` hold.
///
/// The address must lie in data the program only reads: a section
/// neither writable nor executable, or the part of one the loader makes
/// read-only once it is relocated (`.data.rel.ro`).
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Its functions.
/// * `addr` - The table's address.
///
/// # Returns
///
/// The entries, at most [`TABLE_MAX`], or `None` when the first word is
/// no function entry or the data is writable.
fn function_words(program: &Program, analysis: &Analysis, addr: u64) -> Option<Vec<u64>> {
    let section = program.section_at(addr)?;
    let relro = section.name.starts_with(".data.rel.ro");
    if section.executable || section.writable && !relro {
        return None;
    }
    let size: u64 = if program.is_64 { 8 } else { 4 };
    let mut out = Vec::new();
    while out.len() < TABLE_MAX {
        let at = addr.checked_add(size.checked_mul(u64::try_from(out.len()).ok()?)?)?;
        let Some(word) = abi::bound(program, at) else {
            break;
        };
        if analysis.function(word).is_none_or(|f| f.entry != word) {
            break;
        }
        out.push(word);
    }
    (!out.is_empty()).then_some(out)
}

/// Returns the declaration of a table of function designators: an array
/// of pointers of the functions' one type, else of `void *`.
///
/// # Arguments
///
/// * `t` - The table.
/// * `tys` - Each entry's type, in table order.
fn table_line(t: &Table, tys: &[Option<&FnTy>]) -> String {
    let n = t.entries.len();
    if let Some(Some(first)) = tys.first()
        && tys.iter().all(|ty| *ty == Some(*first))
    {
        let mut params = first.params.clone();
        if first.variadic {
            params.push("...".to_owned());
        }
        if params.is_empty() {
            params.push("void".to_owned());
        }
        return format!(
            "static {} (*const {}[{n}])({}) = {{{}}};",
            first.ret,
            t.name,
            params.join(", "),
            t.entries.join(", ")
        );
    }
    let entries: Vec<String> = t.entries.iter().map(|e| format!("(void *){e}")).collect();
    format!(
        "static void *const {}[{n}] = {{{}}};",
        t.name,
        entries.join(", ")
    )
}

/// Returns the declaration lines of a text: those after its header
/// comments and before its first empty line.
///
/// # Arguments
///
/// * `text` - The decompilation.
fn declarations(text: &str) -> String {
    text.lines()
        .skip_while(|l| l.starts_with("//"))
        .take_while(|l| !l.is_empty())
        .collect::<Vec<_>>()
        .join("\n")
}

/// Returns the identifiers a text's code uses, each once, in order of
/// first use: not the header comments, the comment ending a line, string
/// and character literals, or a member a `.` or `->` names.
///
/// # Arguments
///
/// * `text` - The text.
fn words(text: &str) -> Vec<String> {
    let mut seen: BTreeSet<&str> = BTreeSet::new();
    let mut out = Vec::new();
    for line in text.lines().filter(|l| !l.trim_start().starts_with("//")) {
        let code = code_of(line);
        let mut quote: Option<char> = None;
        let mut escaped = false;
        let mut start: Option<usize> = None;
        let mut before = ' ';
        for (i, c) in code
            .char_indices()
            .chain(std::iter::once((code.len(), ' ')))
        {
            if let Some(q) = quote {
                if escaped {
                    escaped = false;
                } else if c == '\\' {
                    escaped = true;
                } else if c == q {
                    quote = None;
                }
                continue;
            }
            if is_ident_char(c) {
                start.get_or_insert(i);
                continue;
            }
            if let Some(s) = start.take() {
                let w = &code[s..i];
                let member = before == '.' || code[..s].ends_with("->");
                if !member && !w.starts_with(|d: char| d.is_ascii_digit()) && seen.insert(w) {
                    out.push(w.to_owned());
                }
            }
            if c == '"' || c == '\'' {
                quote = Some(c);
            }
            if !c.is_whitespace() {
                before = c;
            }
        }
    }
    out
}

/// Returns the argument count of each call of `name` in a text.
///
/// # Arguments
///
/// * `text` - The text.
/// * `name` - The callee.
fn call_arities(text: &str, name: &str) -> Vec<usize> {
    let mut out = Vec::new();
    for line in text.lines().filter(|l| !l.starts_with("//")) {
        let code = code_of(line);
        for at in word_positions(code, name) {
            let open = at + name.len();
            let member = code[..at].ends_with('.') || code[..at].ends_with("->");
            if member || !code[open..].starts_with('(') {
                continue;
            }
            let Some(close) = matching_paren(code, open) else {
                continue;
            };
            let inner = code[open + 1..close].trim();
            out.push(if inner.is_empty() {
                0
            } else {
                split_arguments(inner).len()
            });
        }
    }
    out
}

/// Returns a line without the comment that ends it, outside string and
/// character literals.
///
/// # Arguments
///
/// * `line` - The line.
fn code_of(line: &str) -> &str {
    let mut quote: Option<char> = None;
    let mut escaped = false;
    for (i, c) in line.char_indices() {
        if let Some(q) = quote {
            if escaped {
                escaped = false;
            } else if c == '\\' {
                escaped = true;
            } else if c == q {
                quote = None;
            }
            continue;
        }
        match c {
            '"' | '\'' => quote = Some(c),
            '/' if line[i + 1..].starts_with('/') => return &line[..i],
            _ => {}
        }
    }
    line
}

#[cfg(test)]
mod tests {
    use super::{call_arities, code_of, fn_ty, plain_type, words};

    /// A text's identifiers leave out comments, literals and members.
    ///
    /// # Panics
    ///
    /// When a word is missing or one of those is read as a word.
    #[test]
    fn words_skip_comments_literals_and_members() {
        let text = "// signature: uint64_t f(uint64_t a1)\n\
                    uint64_t g; // @ 0x10 h_hidden\n\
                    return h_is_odd(a1 - 1) + p->op_add + s.op_sub + puts(\"op_mul(\");\n";
        assert_eq!(
            words(text),
            [
                "uint64_t", "g", "return", "h_is_odd", "a1", "p", "s", "puts"
            ]
        );
        assert_eq!(code_of("x = \"//\"; // c"), "x = \"//\"; ");
    }

    /// A signature reads back as its function's type, its parameters'
    /// names dropped.
    ///
    /// # Panics
    ///
    /// When a type is misread.
    #[test]
    fn a_signature_reads_as_its_type() {
        let ty = fn_ty("uint32_t op_add(uint64_t a1, const char *s)", "op_add").unwrap();
        assert_eq!(ty.ret, "uint32_t");
        assert_eq!(ty.params, ["uint64_t", "const char *"]);
        let ty = fn_ty("char *f(void)", "f").unwrap();
        assert_eq!((ty.ret.as_str(), ty.params.len()), ("char *", 0));
        assert!(fn_ty("uint64_t (*)(uint64_t)", "f").is_none());
        assert!(fn_ty("uint64_t xf(uint64_t)", "f").is_none());
        assert!(plain_type("const char *") && plain_type("uint64_t"));
        assert!(!plain_type("HANDLE") && !plain_type("FILE *"));
    }

    /// A call's arguments are counted at its own depth.
    ///
    /// # Panics
    ///
    /// When a count is wrong.
    #[test]
    fn a_call_counts_its_arguments() {
        let text = "x = f(g(a, b), c) + f() + p->f(a);\n";
        assert_eq!(call_arities(text, "f"), [2, 0]);
    }
}
