//! Translation-unit closure: every name a function's text uses, declared
//! in the text.
//!
//! A decompilation a reader compiles is a translation unit, not a lone
//! function. Its body calls other functions, indexes tables of them and
//! calls runtime helpers, and each of those names needs a declaration
//! before the body for the text to mean what the binary does. The closure
//! adds them after the header comments as CIR items ([`cir::Item`]), each
//! name once, in a fixed order:
//!
//! - a definition for each C library type name or debug information
//!   typedef the text or its signature spells (`FILE`, `uLong`), a
//!   `#define` for each constant it names (`SIGALRM`), and an `extern`
//!   for each C library data object it reads (`stderr`, `optind`), from
//!   the type library ([`crate::analysis::typelib::data_type`]);
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
use cir::{CTy, Item, Name, Proto};
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

/// The functions the C standard library's headers declare, separated by
/// spaces: a name a reader's compiler already knows with its own type.
const LIBC: &str = "\
     abort abs acos acosf acosh acosl asctime asin asinf asinh asinl assert atan atan2 atan2f \
     atanf atanh atanl atexit atof atoi atol atoll bsearch btowc cabs calloc cbrt ceil ceilf \
     ceill clearerr clock copysign cos cosf cosh coshf cosl ctime difftime div erf erfc exit \
     exp exp2 expf expl expm1 fabs fabsf fabsl fclose fdim feof ferror fflush fgetc fgetpos \
     fgets fgetwc fgetws floor floorf floorl fma fmax fmaxf fmin fminf fmod fmodf fmodl fopen \
     fprintf fputc fputs fputwc fputws fread free freopen frexp fscanf fseek fsetpos ftell \
     fwide fwprintf fwrite fwscanf getc getchar getenv gets getwc getwchar gmtime hypot ilogb \
     isalnum isalpha isblank iscntrl isdigit isgraph islower isprint ispunct isspace isupper \
     iswalnum iswalpha iswblank iswcntrl iswctype iswdigit iswgraph iswlower iswprint iswpunct \
     iswspace iswupper iswxdigit isxdigit labs ldexp ldexpf ldexpl ldiv llabs lldiv llrint \
     llround localeconv localtime log log10 log10f log1p log2 logb logf logl longjmp lrint \
     lround malloc mblen mbrlen mbrtowc mbsinit mbsrtowcs mbstowcs mbtowc memchr memcmp memcpy \
     memmove memset mktime modf modff nan nanf nearbyint nextafter perror pow powf powl printf \
     putc putchar puts putwc putwchar qsort quick_exit raise rand realloc remainder remove \
     remquo rename rewind rint round roundf scalbn scanf setbuf setjmp setlocale setvbuf signal \
     sin sinf sinh sinhf sinl snprintf sprintf sqrt sqrtf sqrtl srand sscanf strcat strchr \
     strcmp strcoll strcpy strcspn strerror strftime strlen strncat strncmp strncpy strpbrk \
     strrchr strspn strstr strtod strtof strtok strtol strtold strtoll strtoul strtoull strxfrm \
     swprintf swscanf system tan tanf tanh tanhf tanl time tmpfile tmpnam tolower toupper \
     towlower towupper trunc truncf ungetc ungetwc vfprintf vfwprintf vprintf vsnprintf \
     vsprintf vswprintf vwprintf wcrtomb wcscat wcschr wcscmp wcscoll wcscpy wcscspn wcsftime \
     wcslen wcsncat wcsncmp wcsncpy wcspbrk wcsrchr wcsrtombs wcsspn wcsstr wcstod wcstok \
     wcstol wcstombs wcstoul wcsxfrm wctob wctomb wmemchr wmemcmp wmemcpy wmemmove wmemset \
     wprintf wscanf";

/// The segment registers a Linux text reads its thread block through,
/// with the width of the block's first word: `fs` on x86-64, `gs` on x86.
const THREAD_BASES: [(&str, u8); 2] = [("fs", 64), ("gs", 32)];

/// Most type names one unit defines from the libraries and the debug
/// information, typedefs they name included.
const ALIASES_MAX: usize = 64;

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
                let name = expr::bare(&name_of(analysis, overlay, f.entry)).into_owned();
                ix.functions.entry(name).or_insert(f.entry);
            }
            for s in &program.symbols {
                match s.kind {
                    SymbolKind::Import => {
                        ix.imports.insert(expr::bare(&s.name).into_owned());
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

/// One function the unit declares: its prototype and, when the unit
/// defines it, its body.
#[derive(Debug, Clone, PartialEq, Eq)]
struct Declared {
    /// The prototype.
    proto: Proto,
    /// The body, `None` for a function defined outside the unit.
    body: Option<cir::Body>,
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
    let own = expr::bare(&name_of(analysis, overlay, entry)).into_owned();
    let mut tables = designators(text, program, analysis, overlay, &ix);
    let mut names = words(text);
    names.extend(tables.iter().flat_map(|t| t.entries.iter().cloned()));
    let mut decls: BTreeMap<String, Declared> = BTreeMap::new();
    let mut bodies = 0usize;
    for name in names {
        if name == own || decls.contains_key(&name) || Helper::parse(&name).is_some() {
            continue;
        }
        let define = bodies < BODIES_MAX;
        if let Some(d) = declaration(program, analysis, overlay, &ix, &name, define) {
            bodies += usize::from(d.body.is_some());
            decls.insert(name, d);
        }
    }
    decls.retain(|name, d| {
        let p = &d.proto;
        call_arities(text, name)
            .into_iter()
            .all(|n| n == p.params.len() || p.variadic && n > p.params.len())
    });
    let own_proto = text
        .lines()
        .find_map(|l| l.strip_prefix("// signature: "))
        .and_then(|sig| parse_proto(sig.trim(), &own));
    tables.retain(|t| {
        t.entries
            .iter()
            .all(|e| decls.contains_key(e) || (*e == own && own_proto.is_some()))
    });
    let mut items = library_items(
        text,
        program.format,
        &program.debug_typedefs,
        &ix,
        &own,
        &decls,
    );
    if tables.iter().any(|t| t.entries.contains(&own))
        && let Some(p) = &own_proto
    {
        items.push(Item::Extern(p.clone()));
    }
    items.extend(
        decls
            .values()
            .filter(|d| d.body.is_none())
            .map(|d| Item::Extern(d.proto.clone())),
    );
    items.extend(decls.values().filter_map(|d| {
        d.body
            .as_ref()
            .map(|b| Item::Inline(d.proto.clone(), b.clone()))
    }));
    for t in &tables {
        let tys: Vec<Option<CTy>> = t
            .entries
            .iter()
            .map(|e| {
                decls
                    .get(e)
                    .map(|d| &d.proto)
                    .or(own_proto.as_ref())
                    .and_then(pointer_ty)
            })
            .collect();
        let ty = tys
            .first()
            .cloned()
            .flatten()
            .filter(|first| tys.iter().all(|t| t.as_ref() == Some(first)));
        items.push(Item::Table {
            name: Name::of(&t.name),
            ty,
            entries: t.entries.iter().map(|e| Name::of(e)).collect(),
        });
    }
    if items.is_empty() {
        return text.to_owned();
    }
    let mut head = String::new();
    cir::print_items(&items, &mut head);
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
    lines.splice(at..at, head.lines().map(str::to_owned));
    let mut out = lines.join("\n");
    out.push('\n');
    out
}

/// Returns the type names, constants and C library data objects a text
/// uses that it does not declare.
///
/// They are a definition ([`Item::Alias`]) for each
/// type name the library's headers define or the debug information
/// states as a typedef, and each typedef those name; C23's `nullptr` for
/// an older C ([`Item::Nullptr`]); on Linux the thread block's address a
/// segment register's reads are spelled from ([`Item::ThreadBase`]); a
/// `#define` for each constant the type library names by value
/// (`SIGALRM`, `O_RDWR`); then an `extern` for each object the library
/// exports (`extern FILE* stderr;`).
///
/// The signature line counts as code here: a reader compiles it as the
/// function's prototype, so a `FILE *stream` parameter needs `FILE`. A
/// type name is read only where a type stands ([`typed_words`]).
///
/// # Arguments
///
/// * `text` - The decompilation.
/// * `format` - The binary's format, which picks the library.
/// * `typedefs` - The debug information's typedefs, by name.
/// * `ix` - The program's names: an object must be data or an import.
/// * `own` - The function's own name.
/// * `decls` - The functions the unit declares.
///
/// # Returns
///
/// The type names first, in order of first use, then the constants, then
/// the objects.
fn library_items(
    text: &str,
    format: crate::program::BinaryFormat,
    typedefs: &BTreeMap<String, String>,
    ix: &Index,
    own: &str,
    decls: &BTreeMap<String, Declared>,
) -> Vec<Item> {
    let (types, declared) = typed_words(text);
    let used = words(text);
    let objects: Vec<(&String, &'static str)> = used
        .iter()
        .filter(|w| {
            *w != own
                && !declared.contains(w)
                && !decls.contains_key(*w)
                && (ix.data.contains_key(*w) || ix.imports.contains(*w))
        })
        .filter_map(|w| crate::analysis::typelib::data_type(w, format).map(|t| (w, t)))
        .collect();
    let mut named: Vec<String> = Vec::new();
    let mut items: Vec<Item> = Vec::new();
    let mut pending: Vec<String> = types
        .into_iter()
        .chain(objects.iter().flat_map(|(_, t)| words(t)))
        .collect();
    pending.reverse();
    while let Some(w) = pending.pop() {
        if named.contains(&w) || declared.contains(&w) || named.len() >= ALIASES_MAX {
            continue;
        }
        named.push(w);
        let Some(w) = named.last() else { continue };
        if let Some(t) = crate::analysis::typelib::type_definition(w, format) {
            items.push(Item::Alias(CTy::parse(t), Name::of(w)));
        } else if let Some(t) = typedefs.get(w).filter(|_| !standard_type(w)) {
            let t = if t.starts_with("enum ") { "int" } else { t };
            items.push(Item::Alias(CTy::Named(t.to_owned()), Name::of(w)));
            pending.extend(untagged(words(t)).into_iter().rev());
        }
    }
    if used.iter().any(|w| w == "nullptr") {
        items.push(Item::Nullptr);
    }
    if format == crate::program::BinaryFormat::Elf {
        items.extend(
            THREAD_BASES
                .iter()
                .filter(|(seg, _)| {
                    used.iter().any(|w| w == seg) && !declared.iter().any(|w| w == seg)
                })
                .map(|(seg, bits)| Item::ThreadBase(Name::of(seg), *bits)),
        );
    }
    items.extend(
        used.iter()
            .filter(|w| !declared.contains(w) && !w.contains(|c: char| c.is_ascii_lowercase()))
            .filter_map(|w| {
                crate::analysis::typelib::value_of(w, format)
                    .map(|v| Item::Constant(Name::of(w), v))
            }),
    );
    items.extend(
        objects
            .into_iter()
            .map(|(w, t)| Item::Data(CTy::parse(t), Name::of(w))),
    );
    items
}

/// Returns the words a text spells types with and the names it declares:
/// the signature's result and parameter types and its parameters' names,
/// and each declaration's type and declared names.
///
/// A type name can be a variable's name elsewhere (`buffer`), so only a
/// word in a type's place reads as one.
///
/// # Arguments
///
/// * `text` - The decompilation.
///
/// # Returns
///
/// The type words in order of first use, each once, and the declared
/// names.
fn typed_words(text: &str) -> (Vec<String>, Vec<String>) {
    let mut types: Vec<String> = Vec::new();
    let mut names: Vec<String> = Vec::new();
    let mut declarator = |part: &str, typed: bool, named: bool| {
        let head = part.split(['=', '[']).next().unwrap_or(part);
        let mut ws = untagged(words(head));
        if named && let Some(name) = ws.pop() {
            names.push(name);
        }
        if typed {
            for w in ws {
                if !types.contains(&w) {
                    types.push(w);
                }
            }
        }
    };
    if let Some(sig) = text.lines().find_map(|l| l.strip_prefix("// signature: "))
        && let Some((head, rest)) = sig.split_once('(')
    {
        declarator(head, true, true);
        let inner = rest.trim_end().trim_end_matches(';');
        let inner = inner.strip_suffix(')').unwrap_or(inner);
        for p in split_arguments(inner)
            .into_iter()
            .filter(|p| !matches!(*p, "" | "void" | "..."))
        {
            declarator(p, true, param(p).1.is_some());
        }
    }
    for line in declarations(text).lines().filter(|l| !l.starts_with("//")) {
        let code = code_of(line).trim().trim_end_matches(';');
        for (k, part) in split_arguments(code).into_iter().enumerate() {
            declarator(part, k == 0, true);
        }
    }
    (types, names)
}

/// Tells whether a type name is one the C headers every text assumes
/// define (`size_t`, `uint32_t`, `bool`): a typedef the debug information
/// restates for it must not shadow theirs.
///
/// # Arguments
///
/// * `name` - The type's name.
fn standard_type(name: &str) -> bool {
    plain_type(name)
        || matches!(
            name,
            "bool"
                | "intmax_t"
                | "intptr_t"
                | "max_align_t"
                | "ptrdiff_t"
                | "uintmax_t"
                | "uintptr_t"
                | "wchar_t"
        )
}

/// Returns a type's words without the tags it names: `struct`, `union`
/// and `enum` and the word after each, which names a tag and not a type.
///
/// # Arguments
///
/// * `ws` - The words, in order.
fn untagged(ws: Vec<String>) -> Vec<String> {
    let mut out = Vec::with_capacity(ws.len());
    let mut tag = false;
    for w in ws {
        if std::mem::replace(&mut tag, matches!(w.as_str(), "struct" | "union" | "enum")) {
            continue;
        }
        if !tag {
            out.push(w);
        }
    }
    out
}

/// Returns the type of a pointer to a function, [`CTy::FnPtr`], or `None`
/// for a variadic one, which that type cannot spell.
///
/// # Arguments
///
/// * `p` - The function's prototype.
fn pointer_ty(p: &Proto) -> Option<CTy> {
    (!p.variadic).then(|| CTy::FnPtr {
        ret: Box::new(p.ret.clone()),
        params: p.params.iter().map(|(t, _)| t.clone()).collect(),
    })
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
) -> Option<Declared> {
    let outside = |proto| Declared { proto, body: None };
    if let Some(proto) = crate::analysis::runtime::helper(name).map(|h| h.proto) {
        return parse_proto(proto, name).map(outside);
    }
    let function = ix.functions.get(name).copied();
    if function.is_none() && !ix.imports.contains(name) {
        return None;
    }
    if let Some(p) = library(name, program.format) {
        return Some(outside(p));
    }
    if implementation_named(name, program.format) {
        return None;
    }
    let e = function.filter(|&e| analysis.function(e).is_some_and(|f| f.thunk.is_none()))?;
    let internal = !ix.exported.contains(&e) && !ix.exported.contains(&abi::reached(analysis, e));
    if internal
        && define
        && let Some(d) = definition(program, analysis, overlay, e, name)
    {
        return Some(d);
    }
    abi::function::prototype(program, analysis, overlay, e).map(|p| outside(p.proto()))
}

/// Tells whether a name belongs to the C implementation.
///
/// The implementation declares it with a type of its own: a standard
/// library function, any function
/// the type library knows but cannot state in C's own types, or a name
/// C reserves for the implementation (one that starts with `_`).
///
/// A prototype from ABI facts alone would contradict that declaration
/// (`extern uint64_t _exit(uint64_t)` against `void _exit(int)`), so such
/// a name stays undeclared unless the type library states it plainly
/// ([`library`]).
///
/// # Arguments
///
/// * `name` - The function's name.
/// * `format` - The binary's format, which picks the platform.
fn implementation_named(name: &str, format: crate::program::BinaryFormat) -> bool {
    name.starts_with('_')
        || LIBC.split_whitespace().any(|n| n == name)
        || crate::analysis::typelib::declared(name, format).is_some()
}

/// Returns the C library's prototype of a function, when the type library
/// states one in C's own types.
///
/// # Arguments
///
/// * `name` - The function's name.
/// * `format` - The binary's format, which picks the platform.
fn library(name: &str, format: crate::program::BinaryFormat) -> Option<Proto> {
    let d = crate::analysis::typelib::declared(name, format)
        .filter(|d| d.os == crate::analysis::typelib::Os::C)?;
    std::iter::once(d.ret)
        .chain(d.params.iter().map(|p| p.ty))
        .all(plain_type)
        .then(|| Proto {
            ret: CTy::parse(d.ret),
            name: Name::of(name),
            params: d
                .params
                .iter()
                .map(|p| (CTy::parse(p.ty), Some(Name::of(p.name))))
                .collect(),
            variadic: d.variadic,
        })
}

/// Returns a small leaf function's definition: its prototype and body.
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
) -> Option<Declared> {
    analysis
        .function(entry)
        .filter(|f| f.entry == entry && f.instr_count <= BODY_INSTRUCTIONS_MAX)?;
    let d = decompiled_cached(program, analysis, overlay, overlay.fingerprint(), entry);
    let bitness = program.arch.bitness().unwrap_or(64);
    let text = tables::inline_tables(
        &polish_skipping(
            &d.as_ref().as_ref()?.text,
            bitness,
            &analysis.packs,
            overlay.passes,
        ),
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
    let proto = parse_proto(sig, name)?;
    let named: BTreeSet<&str> = proto
        .params
        .iter()
        .filter_map(|(_, n)| n.as_ref().map(Name::as_str))
        .chain(std::iter::once(name))
        .collect();
    let plain = words(sig)
        .iter()
        .all(|w| plain_type(w) || named.contains(w.as_str()));
    let own: BTreeSet<String> = words(sig)
        .into_iter()
        .chain(words(&declarations(&text)))
        .collect();
    let code: String = text
        .lines()
        .filter(|l| !l.starts_with("//"))
        .map(|l| code_of(l).trim_end())
        .filter(|l| !l.trim().is_empty())
        .fold(String::new(), |mut acc, l| {
            acc.push_str(l);
            acc.push('\n');
            acc
        });
    let closed = words(&code).iter().all(|w| {
        own.contains(w)
            || C_WORDS.contains(&w.as_str())
            || plain_type(w)
            || Helper::parse(w).is_some()
            || label_name(&format!("{w}:")).is_some()
    });
    let size: usize = code.lines().map(|l| l.trim().len() + 1).sum();
    (closed && plain && size <= BODY_MAX).then(|| Declared {
        body: Some(cir::build(&code)),
        proto,
    })
}

/// Reads a prototype from its spelling, `uint32_t f(uint64_t a1)`.
///
/// A signature that names two parameters alike (debug information can
/// hand a function an inlined callee's) keeps its types and loses its
/// names, which C would refuse.
///
/// # Arguments
///
/// * `sig` - The signature, parameter names optional.
/// * `name` - The function's name in it.
///
/// # Returns
///
/// The prototype, or `None` when the signature does not name `name`
/// before its parameters.
fn parse_proto(sig: &str, name: &str) -> Option<Proto> {
    let (head, rest) = sig.split_once('(')?;
    let ret = head.trim_end().strip_suffix(name)?.trim_end();
    if ret.is_empty()
        || ret.ends_with(is_ident_char) && !head.trim_end().ends_with(&format!(" {name}"))
    {
        return None;
    }
    let inner = rest.trim_end().trim_end_matches(';').strip_suffix(')')?;
    let mut params = Vec::new();
    let mut variadic = false;
    for p in split_arguments(inner) {
        match p {
            "" | "void" => {}
            "..." => variadic = true,
            _ => params.push(param(p)),
        }
    }
    let named: Vec<&Name> = params.iter().filter_map(|(_, n)| n.as_ref()).collect();
    if named
        .iter()
        .enumerate()
        .any(|(i, n)| named.iter().skip(i + 1).any(|m| m == n))
    {
        for (_, n) in &mut params {
            *n = None;
        }
    }
    Some(Proto {
        ret: CTy::parse(ret),
        name: Name::of(name),
        params,
        variadic,
    })
}

/// Reads one parameter: its type and the name after it, when it has one.
///
/// # Arguments
///
/// * `p` - One parameter, `uint64_t a1`, `const char *s` or `uint64_t`.
fn param(p: &str) -> (CTy, Option<Name>) {
    let p = p.trim();
    let name_at = p.rfind(|c: char| !is_ident_char(c)).map_or(0, |i| i + 1);
    let ty = p[..name_at].trim_end();
    let name = &p[name_at..];
    if ty.is_empty() || name.is_empty() || name.starts_with(|c: char| c.is_ascii_digit()) {
        (CTy::parse(p), None)
    } else {
        (CTy::parse(ty), Some(Name::of(name)))
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
                .map(|e| expr::bare(&name_of(analysis, overlay, e)).into_owned())
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
    use super::{
        Index, Item, call_arities, code_of, implementation_named, library_items, parse_proto,
        plain_type, words,
    };
    use crate::analysis::decompile::cir;
    use crate::program::BinaryFormat;
    use std::collections::BTreeMap;

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

    /// A signature reads into a prototype that prints back as written,
    /// and one that does not name the function is refused.
    ///
    /// # Panics
    ///
    /// When a prototype is misread.
    #[test]
    fn a_signature_reads_into_a_prototype() {
        let p = parse_proto("uint32_t op_add(uint64_t a1, const char *s)", "op_add").unwrap();
        assert_eq!(p.params.len(), 2);
        let mut out = String::new();
        cir::print_items(&[Item::Extern(p)], &mut out);
        assert_eq!(out, "extern uint32_t op_add(uint64_t a1, const char *s);\n");
        let p = parse_proto("char *f(void)", "f").unwrap();
        assert!(p.params.is_empty());
        let mut out = String::new();
        cir::print_items(&[Item::Extern(p)], &mut out);
        assert_eq!(out, "extern char *f(void);\n");
        assert!(parse_proto("uint64_t (*)(uint64_t)", "f").is_none());
        assert!(parse_proto("uint64_t xf(uint64_t)", "f").is_none());
        assert!(plain_type("const char *") && plain_type("uint64_t"));
        assert!(!plain_type("HANDLE") && !plain_type("FILE *"));
    }

    /// A signature naming two parameters alike keeps their types only.
    ///
    /// # Panics
    ///
    /// When a name survives.
    #[test]
    fn a_signature_with_a_repeated_name_loses_its_names() {
        let p = parse_proto("char *f(void *d, size_t n, void *d)", "f").unwrap();
        let mut out = String::new();
        cir::print_items(&[Item::Extern(p)], &mut out);
        assert_eq!(out, "extern char *f(void *, size_t, void *);\n");
    }

    /// A name the C implementation declares is recognized: a standard
    /// function, a reserved name and one the type library knows.
    ///
    /// # Panics
    ///
    /// When one is missed or a program's own name is taken for one.
    #[test]
    fn the_implementation_s_names_are_recognized() {
        for name in ["_exit", "exit", "sqrt", "__scrt_fastfail", "strlen"] {
            assert!(implementation_named(name, BinaryFormat::Pe), "{name}");
        }
        for name in ["h_is_odd", "op_add", "sub_401000"] {
            assert!(!implementation_named(name, BinaryFormat::Elf), "{name}");
        }
    }

    /// The C library's `stderr` a text reads is declared with the type
    /// the headers give it, and `FILE` before it, the signature's use of
    /// `FILE` counted; a PE's library names no such object.
    ///
    /// # Panics
    ///
    /// When a declaration is missing or made for the wrong platform.
    #[test]
    fn the_library_s_data_and_types_are_declared() {
        let mut ix = Index::default();
        ix.data.insert("stderr".to_owned(), 0x4040);
        let text = "// signature: int f(FILE *s, time_t t)\n\
                    \n\
                    fputs(\"x\", *(uint64_t*)&stderr);\n";
        let mut out = String::new();
        let items = library_items(
            text,
            BinaryFormat::Elf,
            &BTreeMap::new(),
            &ix,
            "f",
            &BTreeMap::new(),
        );
        cir::print_items(&items, &mut out);
        assert_eq!(
            out,
            "#define FILE struct _IO_FILE\n#define time_t long\nextern FILE* stderr;\n"
        );
        assert!(
            library_items(
                text,
                BinaryFormat::Pe,
                &BTreeMap::new(),
                &ix,
                "f",
                &BTreeMap::new()
            )
            .is_empty()
        );
    }

    /// A constant the type library names in the text is defined by its
    /// value on the binary's platform, and `nullptr` for a C before C23.
    ///
    /// # Panics
    ///
    /// When a constant is left undefined or given the other platform's
    /// value.
    #[test]
    fn the_library_s_constants_are_defined() {
        let text = "// signature: int f(char *a1)\n\
                    \n\
                    if (a1 == nullptr) {\n  signal(SIGALRM, 0);\n}\n\
                    return open(a1, O_RDWR);\n";
        let mut out = String::new();
        let items = library_items(
            text,
            BinaryFormat::Elf,
            &BTreeMap::new(),
            &Index::default(),
            "f",
            &BTreeMap::new(),
        );
        cir::print_items(&items, &mut out);
        assert_eq!(
            out,
            "#define nullptr ((void *)0)\n#define SIGALRM 14\n#define O_RDWR 2\n"
        );
    }

    /// A typedef the debug information states is defined where the text
    /// spells a type with it.
    ///
    /// So is each typedef its definition names; a word that names a
    /// variable or a tag is no type, a standard header's type keeps the
    /// header's definition, and an enumeration is an `int`.
    ///
    /// # Panics
    ///
    /// When a typedef is left undefined or a variable's name is defined.
    #[test]
    fn the_debug_typedefs_a_text_spells_are_defined() {
        let typedefs: BTreeMap<String, String> = [
            ("z_streamp", "z_stream *"),
            ("z_stream", "struct z_stream_s"),
            ("z_stream_s", "int"),
            ("uLong", "unsigned long"),
            ("buffer", "int"),
            ("size_t", "long unsigned int"),
            ("code_t", "enum code_e"),
        ]
        .into_iter()
        .map(|(n, t)| (n.to_owned(), t.to_owned()))
        .collect();
        let text = "// signature: code_t f(z_streamp strm, char *buffer, size_t n)\n\
                    uLong var1;\n\
                    \n\
                    var1 = buffer[0];\n";
        let mut out = String::new();
        let items = library_items(
            text,
            BinaryFormat::Elf,
            &typedefs,
            &Index::default(),
            "f",
            &BTreeMap::new(),
        );
        cir::print_items(&items, &mut out);
        assert_eq!(
            out,
            "#define code_t int\n#define z_streamp z_stream *\n#define z_stream struct z_stream_s\n#define uLong unsigned long\n"
        );
    }

    /// A Linux text's read through `fs` declares the thread block's
    /// address `fs` stands for; a PE's has no such convention.
    ///
    /// # Panics
    ///
    /// When the block is left undeclared or declared for a PE.
    #[test]
    fn the_thread_block_is_declared_on_linux() {
        let text = "// signature: uint64_t f(void)\n\
                    \n\
                    return *(uint64_t*)(fs + 0x28);\n";
        let mut out = String::new();
        let items = library_items(
            text,
            BinaryFormat::Elf,
            &BTreeMap::new(),
            &Index::default(),
            "f",
            &BTreeMap::new(),
        );
        cir::print_items(&items, &mut out);
        assert_eq!(out, "#define fs (*(uint64_t __seg_fs *)0)\n");
        assert!(
            library_items(
                text,
                BinaryFormat::Pe,
                &BTreeMap::new(),
                &Index::default(),
                "f",
                &BTreeMap::new()
            )
            .is_empty()
        );
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
