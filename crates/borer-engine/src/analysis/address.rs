//! Addresses as an agent types them: hex, decimal or a name, resolved to
//! a virtual address or a function entry, with the nearest names offered
//! when nothing matches.

use super::*;

/// Parses an address as typed by an agent.
///
/// Bare digits are decimal: `140001064` is `0x8583f28`, and hex takes its
/// `0x`. Text with a hex letter and no `0x` (`14000106a`) can only be hex,
/// so it reads as hex. A name that spells a number (`cafe`, `1234`) is
/// [`resolve`]'s to find before this reading applies.
///
/// # Arguments
///
/// * `s` - `0x`-prefixed hex, plain decimal, or bare hex; surrounding whitespace is ignored.
///
/// # Returns
///
/// The address, or `None` when `s` is not a number in any of those forms.
pub fn parse_addr(s: &str) -> Option<u64> {
    let t = s.trim();
    if let Some(h) = t.strip_prefix("0x").or_else(|| t.strip_prefix("0X")) {
        return u64::from_str_radix(h, 16).ok();
    }
    t.parse::<u64>()
        .ok()
        .or_else(|| u64::from_str_radix(t, 16).ok())
}

/// Tells whether address text carries a `0x` prefix, the one spelling that
/// is an address whatever names exist.
///
/// # Arguments
///
/// * `s` - The text as typed; surrounding whitespace is ignored.
#[must_use]
pub fn hex_prefixed(s: &str) -> bool {
    let t = s.trim();
    t.starts_with("0x") || t.starts_with("0X")
}

/// Parses a file offset as typed by an agent: `off:` or `off=` before a
/// number.
///
/// Bytes no section maps (an overlay, the headers, a file with no
/// sections) have no virtual address, so a read names them by where they
/// sit in the file. `off=` is how `strings` and `search` print such a
/// place, so a row can be read back as it was printed.
///
/// # Arguments
///
/// * `s` - The text; the number after the prefix takes any form
///   [`parse_addr`] accepts.
///
/// # Returns
///
/// The offset, or `None` when `s` is not an offset in that form.
pub fn parse_off(s: &str) -> Option<u64> {
    let t = s.trim();
    parse_addr(t.strip_prefix("off:").or_else(|| t.strip_prefix("off="))?)
}

/// Returns the entry of the discovered function containing an address.
///
/// An import's slot holds a pointer to code in another module, so asking
/// for the function there (`decompile GetLastError` where no thunk wraps
/// it) is answered with what the slot is, not as a function not found.
/// The start of a .NET method's IL body is refused the same way: it is not
/// x86 code, and a function a sweep made of its bytes would be noise.
///
/// # Arguments
///
/// * `program` - Supplies the symbol table.
/// * `analysis` - Supplies the functions.
/// * `va` - The address.
///
/// # Returns
///
/// The function's entry.
///
/// # Errors
///
/// Says the address is an import's slot or an IL body, or that no
/// discovered function contains it ([`no_function_at`]).
pub fn function_entry(program: &Program, analysis: &Analysis, va: u64) -> Result<u64, String> {
    if let Some(m) = program
        .clr()
        .and_then(|c| c.method_at(program.image_base, va))
        .filter(|m| m.body == crate::clr::Body::Il)
    {
        return Err(format!(
            "{va:#x} is the IL body of .NET method {:#010x} {}: borer does not decompile IL; disassemble_function, function, function_strings and xrefs on it read its CIL; borer://clr lists the methods",
            m.token, m.name
        ));
    }
    if let Some(f) = analysis.function_at(va) {
        return Ok(f.entry);
    }
    match program
        .symbols
        .iter()
        .find(|s| s.kind == SymbolKind::Import && s.addr == va && va != 0)
    {
        Some(s) => Err(format!(
            "{va:#x} is the import slot of {}: its code is in another module, so no function here; xrefs {va:#x} lists its callers",
            s.name
        )),
        None => Err(no_function_at(program, analysis, va)),
    }
}

/// Says that no discovered function contains `va`, and what to try.
///
/// An address in a section the file holds no bytes for names that
/// section and why it holds none there. One no section declares names the
/// image's span, says whether it lies between sections or outside them
/// and, when the image base plus it is mapped, that address, since an RVA
/// passed for a virtual address is the usual slip; one inside names the
/// nearest function before it.
///
/// # Arguments
///
/// * `program` - Supplies the sections and the image base.
/// * `analysis` - Supplies the functions.
/// * `va` - The address no function contains.
///
/// # Returns
///
/// The sentence a tool answers with.
#[must_use]
pub fn no_function_at(program: &Program, analysis: &Analysis, va: u64) -> String {
    let span = program
        .sections
        .iter()
        .map(|s| (s.span().start, s.span().end))
        .reduce(|(lo, hi), (a, b)| (lo.min(a), hi.max(b)));
    match span {
        Some((lo, hi)) if program.section_at(va).is_none() => {
            if let Some(why) = program.unbacked_at(va) {
                return format!("no discovered function contains {va:#x}: it is {why}");
            }
            let rva = program
                .image_base
                .checked_add(va)
                .filter(|&at| at != va && program.declared_at(at).is_some())
                .map_or_else(String::new, |at| {
                    format!("; as an RVA it is {at:#x}, which is mapped")
                });
            let place = if (lo..hi).contains(&va) {
                "in no section, between the image's sections"
            } else {
                "outside the image"
            };
            format!(
                "no discovered function contains {va:#x}: it is {place} ({lo:#x}..{hi:#x}){rva}"
            )
        }
        Some(_) | None => {
            let before = analysis
                .functions
                .iter()
                .take_while(|f| f.entry <= va)
                .last()
                .map_or_else(String::new, |f| {
                    format!(
                        "; the nearest function before it is {} at {:#x}",
                        f.name
                            .as_deref()
                            .map_or_else(|| format!("sub_{:x}", f.entry), str::to_owned),
                        f.entry
                    )
                });
            format!("no discovered function contains {va:#x}{before}")
        }
    }
}

/// Resolves an address or a name to a virtual address.
///
/// Names match case-insensitively against overlay names, discovered function
/// names, `sub_<hex>`, and symbols (imports and exports, with or without
/// their `dll!` prefix, mangled or demangled). The names the decompiler
/// writes for a class's singleton global (`Class::instance`) and its vtable
/// (`Class::vftable`) resolve too, so a live read can start from either. An
/// import named by both its IAT slot and a thunk function resolves to the
/// function, the thing tools decompile, graph and cross-reference.
///
/// `0x`-prefixed text is always an address. Any other text is looked up as
/// a name first and read as a number ([`parse_addr`]) only when no name
/// matches: a function named `add`, `cafe` or `1234` was unreachable by
/// name while the number reading came first.
///
/// # Arguments
///
/// * `program` - Supplies the symbol table.
/// * `analysis` - Supplies function names and entries.
/// * `overlay` - Supplies user names.
/// * `text` - An address in any form [`parse_addr`] accepts, or a name.
///
/// # Returns
///
/// The unique address the text denotes.
///
/// # Errors
///
/// Returns a message when nothing matches (with the tools to try next) or
/// when several addresses match (listing up to six candidates).
pub fn resolve(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    text: &str,
) -> Result<u64, String> {
    resolve_noting(program, analysis, overlay, text, String::new)
}

/// Resolves an address or a name as [`resolve`] does, and a name nothing
/// matches is answered with the names nearest it ([`nearest_names`]).
///
/// For an agent's argument, where the right name one edit away saves a
/// listing; [`resolve`] stays without the search for callers that try
/// many names and use only the hits.
///
/// # Arguments
///
/// * `program` - Supplies the symbol table.
/// * `analysis` - Supplies function names and entries.
/// * `overlay` - Supplies user names.
/// * `text` - An address in any form [`parse_addr`] accepts, or a name.
///
/// # Returns
///
/// The unique address the text denotes.
///
/// # Errors
///
/// As [`resolve`], a miss naming up to [`NEAREST_NAMES`] names.
pub fn resolve_suggesting(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    text: &str,
) -> Result<u64, String> {
    resolve_noting(program, analysis, overlay, text, || {
        let near = nearest_names(program, analysis, overlay, text);
        if near.is_empty() {
            String::new()
        } else {
            format!("; nearest: {}", near.join(", "))
        }
    })
}

/// What a name nothing matches ends with: the tools that list the names,
/// in the MCP tools' syntax. A caller speaking another syntax (the CLI)
/// replaces it with its own.
pub const LIST_HINT: &str = "; try functions(filter=...) or symbols(filter=...)";

/// Most names a miss suggests ([`resolve_suggesting`]).
pub const NEAREST_NAMES: usize = 3;

/// Returns the names nearest one that names nothing.
///
/// The candidates are the overlay's names, and the functions' and mapped
/// symbols' names without their `dll!` prefix, as [`resolve`] matches
/// them, ranked by [`crate::text::nearest`].
///
/// # Arguments
///
/// * `program` - Supplies the symbol table.
/// * `analysis` - Supplies function names.
/// * `overlay` - Supplies user names.
/// * `text` - The name that matched nothing.
///
/// # Returns
///
/// At most [`NEAREST_NAMES`] names, nearest first, each escaped to one line.
#[must_use]
pub fn nearest_names(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    text: &str,
) -> Vec<String> {
    let names = overlay
        .names
        .values()
        .map(String::as_str)
        .chain(
            analysis
                .functions
                .iter()
                .filter_map(|f| f.name.as_deref().map(bare_name)),
        )
        .chain(
            program
                .symbols
                .iter()
                .filter(|s| s.addr != 0)
                .map(|s| bare_name(&s.name)),
        );
    crate::text::nearest(text, names, NEAREST_NAMES)
        .into_iter()
        .map(crate::text::one_line)
        .collect()
}

/// What [`resolve`] finds a name by besides the overlay: a function, by its
/// entry, or a mapped symbol, by its place in [`Program::symbols`].
#[derive(Debug, Clone, Copy)]
enum Named {
    /// The function with this entry.
    Function(u64),
    /// The symbol at this index.
    Symbol(usize),
}

/// Returns every function and mapped symbol by each lowercased name
/// [`resolve`] matches it by, built once per analysis.
///
/// A function goes under its name and bare name, a symbol under its name,
/// bare name and demangled form. A lookup walked every function and
/// symbol, demangling each, per name: most of a millisecond on a DLL of a
/// few thousand functions, in every tool given a name.
///
/// # Arguments
///
/// * `program` - Supplies the symbol table.
/// * `analysis` - Supplies function names and entries, and holds the index.
fn name_index(program: &Program, analysis: &Analysis) -> Arc<FxHashMap<String, Vec<Named>>> {
    analysis.derived.get_or_build("name_index", (), || {
        let mut ix: FxHashMap<String, Vec<Named>> = FxHashMap::default();
        for f in &analysis.functions {
            if let Some(n) = &f.name {
                for key in [n.to_lowercase(), bare_name(n).to_lowercase()] {
                    ix.entry(key).or_default().push(Named::Function(f.entry));
                }
            }
        }
        for (i, s) in program
            .symbols
            .iter()
            .enumerate()
            .filter(|(_, s)| s.addr != 0)
        {
            let demangled = crate::search::demangled_or_raw(&s.name).to_lowercase();
            for key in [
                s.name.to_lowercase(),
                bare_name(&s.name).to_lowercase(),
                demangled,
            ] {
                ix.entry(key).or_default().push(Named::Symbol(i));
            }
        }
        ix
    })
}

/// Tells whether `name` lowercases to `lower`, a text already lowercased,
/// allocating only when either holds a character past ASCII.
///
/// # Arguments
///
/// * `name` - The name as stored.
/// * `lower` - The lowercased text it is matched against.
fn lower_eq(name: &str, lower: &str) -> bool {
    if name.is_ascii() && lower.is_ascii() {
        name.eq_ignore_ascii_case(lower)
    } else {
        name.to_lowercase() == lower
    }
}

/// [`resolve`], with `miss` saying more about a name nothing matches.
///
/// # Arguments
///
/// * `program` - Supplies the symbol table.
/// * `analysis` - Supplies function names and entries.
/// * `overlay` - Supplies user names.
/// * `text` - An address or a name.
/// * `miss` - Builds what a miss says after its first clause; called only
///   on a miss.
///
/// # Returns
///
/// The unique address the text denotes.
///
/// # Errors
///
/// As [`resolve`].
fn resolve_noting(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    text: &str,
    miss: impl FnOnce() -> String,
) -> Result<u64, String> {
    if hex_prefixed(text)
        && let Some(va) = parse_addr(text)
    {
        return Ok(va);
    }
    let want = text.trim().to_lowercase();
    if let Some(hex) = want.strip_prefix("sub_")
        && let Ok(va) = u64::from_str_radix(hex, 16)
    {
        return Ok(va);
    }
    let mut hits: Vec<(u64, String)> = Vec::new();
    for (va, n) in &overlay.names {
        if lower_eq(n, &want) {
            hits.push((*va, n.clone()));
        }
    }
    let index = name_index(program, analysis);
    let named = index.get(&want).map_or(&[][..], Vec::as_slice);
    let symbols = || {
        named.iter().filter_map(|n| match *n {
            Named::Symbol(i) => program.symbols.get(i),
            Named::Function(_) => None,
        })
    };
    hits.extend(named.iter().filter_map(|n| match *n {
        Named::Function(entry) => analysis.function(entry)?.name.clone().map(|n| (entry, n)),
        Named::Symbol(_) => None,
    }));
    if let Some(class) = want.strip_suffix("::instance") {
        for (addr, c) in &analysis.classes.global_hints {
            if c.to_lowercase() == class {
                hits.push((*addr, format!("{c}::instance")));
            }
        }
    }
    if let Some(class) = want.strip_suffix("::vftable") {
        for (va, c) in &analysis.classes.vtables {
            if c.to_lowercase() == class {
                hits.push((*va, format!("{c}::vftable")));
            }
        }
    }
    hits.extend(symbols().map(|s| (s.addr, format!("{} {}", s.kind.name(), s.name))));
    hits.sort();
    hits.dedup_by_key(|h| h.0);
    if hits.iter().any(|(va, _)| analysis.function(*va).is_some()) {
        hits.retain(|(va, _)| analysis.function(*va).is_some());
    }
    let own: BTreeSet<u64> = symbols()
        .filter(|s| s.kind != SymbolKind::Import)
        .filter(|s| s.name.to_lowercase() == want || bare_name(&s.name).to_lowercase() == want)
        .map(|s| s.addr)
        .collect();
    if hits.len() > 1 && hits.iter().any(|(va, _)| own.contains(va)) {
        hits.retain(|(va, _)| own.contains(va));
    }
    match hits.len() {
        0 => parse_addr(text).ok_or_else(|| {
            format!(
                "{} is neither an address nor a known name{}{LIST_HINT}",
                crate::text::quoted(text),
                miss()
            )
        }),
        1 => Ok(hits[0].0),
        _ => Err(format!(
            "{} is ambiguous: {}",
            crate::text::quoted(text),
            hits.iter()
                .take(6)
                .map(|(va, n)| format!("{va:#x} ({n})"))
                .collect::<Vec<_>>()
                .join(", ")
        )),
    }
}
