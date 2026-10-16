//! Class layouts recovered from the field accesses of a class's methods.
//!
//! The functions named `Class::method` (from symbols, asserts or the
//! overlay) are the class's methods; each is decompiled and every access to
//! the first parameter's object, `*(type*)(a1 + offset)`, is collected with
//! its width, direction and the constant it stores. The union over all
//! methods is the class layout as the program itself uses it: offsets,
//! widths, which methods touch each field, embedded objects whose address is
//! taken, and vftable pointers stored at offset zero. Fields passed to a
//! callee with a declared signature take that callee's type: `this + 0x30`
//! passed as `Util::Array<UI::Icon>::Append`'s `this` is an embedded
//! `Util::Array<UI::Icon>`, a loaded pointer field passed the same way is a
//! `Foo *`, and a field passed for a declared `const Util::String &`
//! parameter is a `Util::String`. An agent asks for a class and gets the
//! whole structure with the evidence attached, instead of building it by
//! hand one function at a time.

use std::borrow::Cow;
use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;
use std::sync::Arc;

use super::decompile::decompile_plain;
use super::fieldrefs::{FieldAccess, FieldRef};
use super::{
    Analysis, Function, Overlay, Signature, name_of, plain_text_cached, single, slot_name_of,
    striped,
};
use crate::fxmap::FxHashMap;
use crate::program::Program;

/// Most methods decompiled for one layout (the biggest classes have a few
/// hundred; beyond this the layout is a sample and says so).
pub const METHODS_MAX: usize = 400;
/// Most vtable slots listed in a layout.
const SLOTS_SHOWN: usize = 48;
/// Most method names listed per field.
const METHODS_SHOWN: usize = 3;

/// One field of a class as its methods use it.
#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct FieldUse {
    /// Access widths seen, in bits (`8`, `32`, `64`, ...); `0` marks a
    /// floating-point access of unknown width.
    pub widths: BTreeSet<u8>,
    /// The field was a floating-point access at least once.
    pub float: bool,
    /// Widths of the floating-point accesses alone, in bits. A constructor
    /// that zeroes eight bytes covers two floats, so its width says nothing
    /// about either one's type.
    pub float_widths: BTreeSet<u8>,
    /// Loads.
    pub reads: usize,
    /// Stores.
    pub writes: usize,
    /// The field's address was taken (`a1 + off` passed on or stored):
    /// an embedded object or array starts here.
    pub address_taken: usize,
    /// Methods (entries) touching the field.
    pub methods: BTreeSet<u64>,
    /// Constants stored into the field (vftable pointers, enum values).
    pub constants: BTreeSet<u64>,
    /// Types the field was passed as, from the declared signatures of the
    /// callees it reached: the callee's class when it was the `this`
    /// argument, else the declared parameter type (a pointer field keeps its
    /// `*`).
    pub types: BTreeSet<String>,
    /// Source names the field was given by asserts, with vote counts: a
    /// guarded assert whose condition reads exactly one field and whose
    /// expression names exactly one `this->member` ties the two (a member
    /// called as a method keeps its `()`: the field behind that getter).
    /// Only the votes [`field_labels`] counts fill it; a layout's fields
    /// carry the outcome in [`ClassLayout::labels`] instead.
    pub names: BTreeMap<String, usize>,
}

/// What a class's own code calls one of its fields.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FieldLabel {
    /// The member's source name (`strLen`), from the class's guarded
    /// asserts, its template siblings' or an inlined setter's.
    Member(String),
    /// The getter every assert reading the field calls (`IsSet` for
    /// `this->IsSet()`), without its parentheses: what reads the field,
    /// not what the field is called.
    ReadBy(String),
}

impl std::fmt::Display for FieldLabel {
    /// Writes a member's name, or a getter's with its parentheses
    /// (`IsSet()`), which is how a layout tells the two apart.
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            FieldLabel::Member(name) => f.write_str(name),
            FieldLabel::ReadBy(getter) => write!(f, "{getter}()"),
        }
    }
}

/// A class layout with its evidence.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ClassLayout {
    /// Qualified class name.
    pub name: String,
    /// Method entries, sorted.
    pub methods: Vec<u64>,
    /// Fields by offset.
    pub fields: BTreeMap<u64, FieldUse>,
    /// What the class's code calls its fields, by offset ([`field_labels`]).
    pub labels: BTreeMap<u64, FieldLabel>,
    /// Methods were capped at [`METHODS_MAX`].
    pub sampled: bool,
}

/// Splits a qualified name into its class part (`a::b::C` for `a::b::C::m`).
///
/// Template arguments may hold `::` of their own; only the last separator at
/// template depth zero counts.
///
/// # Arguments
///
/// * `name` - A qualified function name.
///
/// # Returns
///
/// The class, or `None` for an unqualified name.
pub fn class_of(name: &str) -> Option<&str> {
    let mut depth = 0i32;
    let mut last = None;
    let bytes = name.as_bytes();
    for (i, &b) in bytes.iter().enumerate() {
        match b {
            b'<' => depth += 1,
            b'>' if bytes.get(i.wrapping_sub(1)) != Some(&b'-') => depth -= 1,
            b':' if depth == 0 && bytes.get(i + 1) == Some(&b':') => {
                let rest = name.get(i + 2..).unwrap_or("");
                if rest.strip_prefix("operator").is_some_and(|op| {
                    !op.starts_with(|c: char| c.is_ascii_alphanumeric() || c == '_')
                }) {
                    return name.get(..i).filter(|c| !c.is_empty());
                }
                last = Some(i);
            }
            _ => {}
        }
    }
    last.and_then(|i| name.get(..i)).filter(|c| !c.is_empty())
}

/// Lists the functions named `class::method`.
///
/// # Arguments
///
/// * `analysis` - Discovery results.
/// * `overlay` - User names take precedence.
/// * `class` - Qualified class name.
///
/// # Returns
///
/// The method entries in address order.
pub fn methods_of(analysis: &Analysis, overlay: &Overlay, class: &str) -> Vec<u64> {
    let index = analysis
        .derived
        .get_or_build_named("methods", overlay.fingerprint(), (), || {
            method_index(analysis, overlay)
        });
    index.get(class).cloned().unwrap_or_default()
}

/// Every class's methods in address order, by class: what [`methods_of`]
/// answers, built in one pass over the functions rather than one per
/// question.
type MethodIndex = FxHashMap<String, Vec<u64>>;

/// Builds the [`MethodIndex`]: a function belongs to the class its name
/// qualifies it with and to the class a caller hinted for its `this`.
///
/// # Arguments
///
/// * `analysis` - Discovery results.
/// * `overlay` - User names take precedence.
fn method_index(analysis: &Analysis, overlay: &Overlay) -> MethodIndex {
    let mut out = MethodIndex::default();
    for f in &analysis.functions {
        let named = declared_name(overlay, f).and_then(class_of);
        if let Some(c) = named {
            out.entry(c.to_owned()).or_default().push(f.entry);
        }
        if let Some(hint) = f.param_hints.get(&0)
            && named != Some(hint.as_str())
        {
            out.entry(hint.clone()).or_default().push(f.entry);
        }
    }
    out
}

/// Borrows a function's name, without inventing one for the unnamed.
///
/// A class scan reads every function in the program, so it takes the name by
/// reference rather than cloning it, and skips the `sub_<va>` names
/// [`name_of`] invents, which are never qualified and so
/// never name a class.
///
/// # Arguments
///
/// * `overlay` - User names take precedence.
/// * `f` - The function to name.
///
/// # Returns
///
/// The name a symbol, an assert or the user gave it, or `None`.
fn declared_name<'a>(overlay: &'a Overlay, f: &'a Function) -> Option<&'a str> {
    overlay
        .names
        .get(&f.entry)
        .or(f.name.as_ref())
        .map(String::as_str)
}

/// Resolves a class name against the classes with methods.
///
/// The name itself when a class spells it so, else the class spelled so in
/// another case, else the class whose last segment it is
/// (`AchievementManager` for `Achievements::AchievementManager`), the first
/// by name when several, which is the one `borer://classes` prints beside
/// a registered name.
///
/// # Arguments
///
/// * `analysis` - Discovery results.
/// * `overlay` - User names take precedence.
/// * `name` - A class name, qualified or its last segment, in any case.
///
/// # Returns
///
/// The qualified name as the method index spells it, or `None` when no
/// function belongs to a class so named.
pub fn resolve_class(analysis: &Analysis, overlay: &Overlay, name: &str) -> Option<String> {
    let index = analysis
        .derived
        .get_or_build_named("methods", overlay.fingerprint(), (), || {
            method_index(analysis, overlay)
        });
    if index.contains_key(name) {
        return Some(name.to_owned());
    }
    let want = name.to_lowercase();
    let first = |keep: &dyn Fn(&str) -> bool| index.keys().filter(|c| keep(c)).min().cloned();
    first(&|c| c.to_lowercase() == want).or_else(|| {
        first(&|c| {
            c.rsplit_once("::")
                .map_or(c, |(_, tail)| tail)
                .to_lowercase()
                == want
        })
    })
}

/// Recovers the layout of `class` from its methods.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Discovery results.
/// * `overlay` - User names and comments.
/// * `class` - The class name as [`resolve_class`] reads it: qualified, or
///   its last segment, in any case.
///
/// # Returns
///
/// The layout, named as the methods qualify the class, or `None` when no
/// function belongs to the class.
pub fn class_layout(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    class: &str,
) -> Option<ClassLayout> {
    let class = resolve_class(analysis, overlay, class)?;
    let methods = methods_of(analysis, overlay, &class);
    if methods.is_empty() {
        return None;
    }
    let sampled = methods.len() > METHODS_MAX;
    let mut fields: BTreeMap<u64, FieldUse> = BTreeMap::new();
    let by_name: BTreeMap<Cow<'_, str>, &Signature> = analysis
        .functions
        .iter()
        .filter_map(|f| {
            let name = declared_name(overlay, f)
                .map_or_else(|| Cow::Owned(format!("sub_{:x}", f.entry)), Cow::Borrowed);
            f.signature.as_ref().map(|s| (name, s))
        })
        .collect();
    for &entry in methods.iter().take(METHODS_MAX) {
        let Some(text) = decompile_plain(program, analysis, overlay, entry) else {
            continue;
        };
        for line in text.lines() {
            collect_accesses(line.trim(), entry, &mut fields);
            collect_call_types(line.trim(), entry, &by_name, &mut fields);
        }
    }
    Some(ClassLayout {
        labels: field_labels(program, analysis, overlay, &class),
        name: class,
        methods,
        fields,
        sampled,
    })
}

/// Records every access to the `this` object on one pseudo-C line, the
/// object being `this` when the line names it and `a1` otherwise
/// ([`collect_accesses_of`]).
///
/// # Arguments
///
/// * `line` - The trimmed line.
/// * `entry` - The method it belongs to.
/// * `fields` - The layout being built.
fn collect_accesses(line: &str, entry: u64, fields: &mut BTreeMap<u64, FieldUse>) {
    let token = if line.contains("this") { "this" } else { "a1" };
    collect_accesses_of(token, line, entry, fields);
}

/// Records every access to the object `token` points at on one pseudo-C
/// line.
///
/// Recognized forms: `*(type*)token`, `*(type*)(token + off)` (a store when
/// the statement assigns to it, else a load; a constant on the right-hand
/// side of a store is kept), and a bare `token + off` outside a dereference
/// (the field's address is taken).
///
/// # Arguments
///
/// * `token` - The variable holding the object: `this`, `a2`, `rax`.
/// * `line` - The trimmed line.
/// * `entry` - The function it belongs to.
/// * `fields` - The fields seen so far, by offset.
fn collect_accesses_of(token: &str, line: &str, entry: u64, fields: &mut BTreeMap<u64, FieldUse>) {
    let mut pos = 0;
    while let Some(rel) = line[pos..].find(token) {
        let at = pos + rel;
        pos = at + token.len();
        let after = &line[pos..];
        if after.starts_with(|c: char| c.is_ascii_alphanumeric() || c == '_') {
            continue;
        }
        let before = &line[..at];
        if before.ends_with(|c: char| c.is_ascii_alphanumeric() || c == '_') {
            continue;
        }
        let (offset, consumed) = match after.strip_prefix(" + ") {
            Some(rest) => match parse_number(rest) {
                Some((v, n)) => (v, 3 + n),
                None => continue,
            },
            None => (0, 0),
        };
        let rest = &after[consumed..];
        let deref = deref_width(before, rest);
        if deref.is_none() && consumed == 0 {
            continue;
        }
        let field = fields.entry(offset).or_default();
        field.methods.insert(entry);
        match deref {
            Some(d) => {
                if d.width != 0 {
                    field.widths.insert(d.width);
                    if d.float {
                        field.float_widths.insert(d.width);
                    }
                }
                field.float |= d.float;
                let opens_statement = before
                    .get(..d.cast_start)
                    .is_some_and(|lhs| lhs.trim().is_empty());
                let assigned = assignment_rhs(d.tail);
                if opens_statement && let Some(rhs) = assigned {
                    field.writes += 1;
                    if let Some((c, _)) = parse_number(rhs) {
                        field.constants.insert(c);
                    }
                } else {
                    field.reads += 1;
                }
            }
            None => field.address_taken += 1,
        }
    }
}

/// Types the fields a line passes to callees with declared signatures.
///
/// Every `Name(args)` whose name has a signature is examined: an argument
/// `this + off` (or `this`) is the address of the field at `off`, and
/// `*(uint64_t*)(this + off)` is the pointer stored there. The callee is a
/// member function when its signature is `const` or its name has a class
/// and the call passes one more argument than declared; its first argument
/// is then its `this` and takes the class as type, the others take the
/// declared parameter types (references and `const` dropped for an embedded
/// object, kept for a pointer field).
///
/// # Arguments
///
/// * `line` - The trimmed line.
/// * `entry` - The method the line belongs to.
/// * `by_name` - Declared signatures by function name.
/// * `fields` - The layout being built.
fn collect_call_types(
    line: &str,
    entry: u64,
    by_name: &BTreeMap<Cow<'_, str>, &Signature>,
    fields: &mut BTreeMap<u64, FieldUse>,
) {
    for (i, c) in line.char_indices() {
        if c != '(' {
            continue;
        }
        let Some(callee) = callee_before(line, i) else {
            continue;
        };
        let Some(sig) = by_name.get(callee) else {
            continue;
        };
        let Some(args) = call_args(line, i) else {
            continue;
        };
        let hidden = usize::from(sig.by_pointer);
        let member = sig.is_const
            || (class_of(&sig.name).is_some() && args.len() > sig.params.len() + hidden);
        for (pos, arg) in args.iter().enumerate() {
            let Some((offset, pointer)) = field_operand(arg) else {
                continue;
            };
            let declared = if member && pos == 0 {
                class_of(&sig.name).map(str::to_owned)
            } else {
                let slot = pos - usize::from(member);
                if slot < hidden {
                    Some(sig.ret.clone())
                } else {
                    sig.params.get(slot - hidden).cloned()
                }
            };
            let Some(ty) = declared else {
                continue;
            };
            let ty = if pointer {
                let base = ty.trim_end_matches('&').trim_end();
                if base.ends_with('*') {
                    base.to_owned()
                } else {
                    format!("{base} *")
                }
            } else {
                ty.trim_start_matches("const ")
                    .trim_end_matches(['&', '*', ' '])
                    .to_owned()
            };
            if !ty.is_empty() {
                let field = fields.entry(offset).or_default();
                field.types.insert(ty);
                field.methods.insert(entry);
            }
        }
    }
}

/// Returns what the code of `class` calls its fields, by offset: the one
/// source every reader of a field's name takes it from.
///
/// A member name wins wherever a source gives one: the name most of the
/// member names the class's guarded asserts tie to the field agree on
/// ([`majority_member`]), else the one its template's other
/// instantiations agree on ([`sibling_votes`]), else an inlined setter's
/// ([`setter_names`]). A field no source gives a member name, whose
/// asserts all go through a getter, is labelled by the getter most of
/// them call ([`sole_reader`]). [`class_layout`], a field's typed uses, a
/// live object, an encoder's fields and a message's fields print either
/// label; the decompiler takes only the member names ([`field_names`]).
/// Built once per class under the names in force
/// ([`super::Derived::get_or_build_named`]): a rename that leaves the
/// class's methods as they were can still add or take away a template
/// sibling, or the smart pointer an inlined setter is read through.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Discovery results.
/// * `overlay` - User names.
/// * `class` - Qualified class name.
pub fn field_labels(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    class: &str,
) -> BTreeMap<u64, FieldLabel> {
    analysis
        .derived
        .get_or_build_named(
            "field_names",
            overlay.fingerprint(),
            class.to_owned(),
            || {
                let methods = methods_of(analysis, overlay, class);
                let own = method_votes(program, analysis, overlay, &methods);
                let siblings = sibling_votes(program, analysis, overlay, class);
                let mut labels: BTreeMap<u64, FieldLabel> = BTreeMap::new();
                for (off, u) in own.iter().chain(&siblings) {
                    if let Some(name) = majority_member(u) {
                        labels.entry(*off).or_insert(FieldLabel::Member(name));
                    }
                }
                for (off, name) in setter_names(program, analysis, overlay, class) {
                    labels.entry(off).or_insert(FieldLabel::Member(name));
                }
                for (off, u) in own.iter().chain(&siblings) {
                    if let Some(getter) = sole_reader(u) {
                        labels.entry(*off).or_insert(FieldLabel::ReadBy(getter));
                    }
                }
                labels
            },
        )
        .as_ref()
        .clone()
}

/// Returns the member names of the fields of `class`, by offset: the
/// [`FieldLabel::Member`] labels of [`field_labels`].
///
/// A field known only by the getter that reads it is left out: rendered
/// as `this->IsSet()` it would put a call in the text where the code reads
/// memory.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Discovery results.
/// * `overlay` - User names.
/// * `class` - Qualified class name.
pub fn field_names(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    class: &str,
) -> BTreeMap<u64, String> {
    field_labels(program, analysis, overlay, class)
        .into_iter()
        .filter_map(|(off, label)| match label {
            FieldLabel::Member(name) => Some((off, name)),
            FieldLabel::ReadBy(_) => None,
        })
        .collect()
}

/// Names fields of `class` from the setters inlined into other functions.
///
/// A setter that asserts before it writes (`!this->handled`) leaves its
/// `__FUNCSIG__` in every function it was inlined into, and the write it
/// guards is the next thing that function does to the object: the first
/// `var + off` within the lines after the assert, `var` being what the
/// function bound to the class through a smart pointer, or a copy of it.
/// `Type::SetField` followed by `sub_x(rdi + 32, ...)` names
/// +0x20 `MapId`. Sites are counted and the offset most sites agree on wins.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Discovery results, with the setter strings by class.
/// * `overlay` - User names.
/// * `class` - Qualified class name.
pub(crate) fn setter_names(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    class: &str,
) -> BTreeMap<u64, String> {
    /// Lines after the assert the write may sit on.
    const WINDOW: usize = 4;
    let Some(setters) = analysis.classes.setters.get(class) else {
        return BTreeMap::new();
    };
    let overlay_key = overlay.fingerprint();
    let sites: Vec<(&str, u64)> = setters
        .iter()
        .flat_map(|(target, member)| {
            analysis
                .xrefs
                .get(target)
                .into_iter()
                .flatten()
                .filter_map(|s| s.from_entry)
                .map(move |entry| (member.as_str(), entry))
        })
        .collect();
    let writes = striped(&sites, |&(member, entry)| {
        let text = plain_text_cached(program, analysis, overlay, overlay_key, entry)?;
        let marker = format!("__FUNCSIG__({class}::Set{member})");
        Some(setter_writes(&text, class, &marker, WINDOW))
    });
    let mut votes: BTreeMap<(String, u64), usize> = BTreeMap::new();
    for ((member, _), offs) in sites.iter().zip(writes).filter_map(|(s, w)| Some((s, w??))) {
        for off in offs {
            *votes.entry(((*member).to_owned(), off)).or_insert(0) += 1;
        }
    }
    let mut best: BTreeMap<String, (usize, u64)> = BTreeMap::new();
    for ((member, off), n) in votes {
        let slot = best.entry(member).or_insert((n, off));
        if n > slot.0 {
            *slot = (n, off);
        }
    }
    best.into_iter()
        .map(|(member, (_, off))| (off, member))
        .collect()
}

/// The offsets written right after each occurrence of `marker` in `text`
/// through a variable bound to `class`.
///
/// # Arguments
///
/// * `text` - A function's pseudo-C.
/// * `class` - The class the setter belongs to.
/// * `marker` - The `__FUNCSIG__(...)` text of the setter.
/// * `window` - Lines after the marker the write may sit on.
fn setter_writes(text: &str, class: &str, marker: &str, window: usize) -> Vec<u64> {
    let lines: Vec<&str> = text.lines().map(str::trim).collect();
    let mut bound: BTreeMap<String, String> = BTreeMap::new();
    let mut out = Vec::new();
    for (i, line) in lines.iter().enumerate() {
        if let Some((lhs, rhs)) = line.split_once(" = ")
            && is_identifier(lhs.trim())
        {
            let rhs = rhs.trim().trim_end_matches(';');
            if let Some(c) = smart_pointer_class(rhs) {
                bound.insert(lhs.trim().to_owned(), c);
            } else if is_identifier(rhs) {
                match bound.get(rhs).cloned() {
                    Some(c) => {
                        bound.insert(lhs.trim().to_owned(), c);
                    }
                    None => {
                        bound.remove(lhs.trim());
                    }
                }
            } else {
                bound.remove(lhs.trim());
            }
        }
        if !line.contains(marker) {
            continue;
        }
        let hit = lines.iter().skip(i + 1).take(window).find_map(|l| {
            plus_offsets(l)
                .into_iter()
                .find(|(var, _)| bound.get(var).is_some_and(|c| c == class))
        });
        if let Some((_, off)) = hit {
            out.push(off);
        }
    }
    out
}

/// Every `ident + number` on a line, as `(ident, number)`.
///
/// # Arguments
///
/// * `line` - The line.
fn plus_offsets(line: &str) -> Vec<(String, u64)> {
    let mut out = Vec::new();
    for (i, _) in line.match_indices(" + ") {
        let ident: String = line[..i]
            .chars()
            .rev()
            .take_while(|c| c.is_ascii_alphanumeric() || *c == '_')
            .collect::<String>()
            .chars()
            .rev()
            .collect();
        let number: String = line[i + 3..]
            .chars()
            .take_while(|c| c.is_ascii_alphanumeric())
            .collect();
        if ident.is_empty() || number.is_empty() {
            continue;
        }
        if let Some(off) = super::parse_addr(&number) {
            out.push((ident, off));
        }
    }
    out
}

/// Adds up the assert votes of a class's methods, the reading
/// [`field_labels`] memoizes.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Discovery results.
/// * `overlay` - User names.
/// * `methods` - The class's methods ([`methods_of`]).
///
/// # Returns
///
/// The votes by offset, in [`FieldUse::names`].
fn method_votes(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    methods: &[u64],
) -> BTreeMap<u64, FieldUse> {
    let mut fields: BTreeMap<u64, FieldUse> = BTreeMap::new();
    let read: Vec<u64> = methods.iter().copied().take(METHODS_MAX).collect();
    for votes in striped(&read, |&entry| {
        assert_votes(program, analysis, overlay, entry)
    })
    .iter()
    .flatten()
    {
        add_votes(&mut fields, votes);
    }
    fields
}

/// Adds up the assert votes of a template's other instantiations.
///
/// `Util::Array<T>` stores a pointer to its elements, so every
/// instantiation puts `grow`, `size` and `elements` at the same offsets, but
/// each one is a class of its own and a rarely used instantiation may have
/// too few methods to name them. The instantiations vote together, under the
/// name with its arguments stripped, and [`field_labels`] takes what they
/// agree on only for the offsets the class's own methods left unnamed. A
/// class that is not a template has no siblings and pays nothing.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Discovery results.
/// * `overlay` - User names and comments.
/// * `class` - Qualified class name.
///
/// # Returns
///
/// The siblings' votes by offset, in [`FieldUse::names`].
fn sibling_votes(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    class: &str,
) -> BTreeMap<u64, FieldUse> {
    if !class.contains('<') {
        return BTreeMap::new();
    }
    let templates =
        analysis
            .derived
            .get_or_build_named("templates", overlay.fingerprint(), (), || {
                template_index(analysis, overlay)
            });
    let mut fields: BTreeMap<u64, FieldUse> = BTreeMap::new();
    let siblings: Vec<u64> = templates
        .get(&generic_name(class))
        .into_iter()
        .flatten()
        .filter(|(_, other)| other != class)
        .filter(|(entry, _)| asserts_a_member(program, analysis, *entry))
        .take(SIBLING_METHODS_MAX)
        .map(|(entry, _)| *entry)
        .collect();
    for votes in striped(&siblings, |&entry| {
        assert_votes(program, analysis, overlay, entry)
    })
    .iter()
    .flatten()
    {
        add_votes(&mut fields, votes);
    }
    fields
}

/// The methods of every template's instantiations in address order, by the
/// template's name with its arguments stripped ([`generic_name`]), each
/// with the instantiation it belongs to.
type TemplateIndex = FxHashMap<String, Vec<(u64, String)>>;

/// Builds the [`TemplateIndex`] in one pass over the functions.
///
/// # Arguments
///
/// * `analysis` - Discovery results.
/// * `overlay` - User names take precedence.
fn template_index(analysis: &Analysis, overlay: &Overlay) -> TemplateIndex {
    let mut out = TemplateIndex::default();
    for f in &analysis.functions {
        if let Some(class) = declared_name(overlay, f).and_then(class_of)
            && class.contains('<')
        {
            out.entry(generic_name(class))
                .or_default()
                .push((f.entry, class.to_owned()));
        }
    }
    out
}

/// One method's assertion votes: each `(offset, member, count)` its guarded
/// assertions tie together ([`collect_assert_names`]).
type Votes = Vec<(u64, String, usize)>;

/// The assertion votes of one method, read once from its decompilation.
///
/// A method is asked for by its own class and by every sibling
/// instantiation of its template, and its votes are a few words where its
/// text is kilobytes.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Discovery results.
/// * `overlay` - User names.
/// * `entry` - The method.
fn assert_votes(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    entry: u64,
) -> Arc<Votes> {
    if !asserts_a_member(program, analysis, entry) {
        return Arc::default();
    }
    analysis.derived.get_or_build_item(
        "assert_votes",
        overlay.fingerprint(),
        entry,
        || {
            let mut fields: BTreeMap<u64, FieldUse> = BTreeMap::new();
            if let Some(text) = decompile_plain(program, analysis, overlay, entry) {
                let mut prev = "";
                for line in text.lines() {
                    collect_assert_names(prev, line.trim(), &mut fields);
                    prev = line.trim();
                }
            }
            fields
                .into_iter()
                .flat_map(|(off, u)| u.names.into_iter().map(move |(m, n)| (off, m, n)))
                .collect::<Votes>()
        },
        |votes| {
            votes.capacity() * size_of::<(u64, String, usize)>()
                + votes.iter().map(|(_, m, _)| m.capacity()).sum::<usize>()
        },
    )
}

/// Adds one method's [`Votes`] to a class's field uses.
///
/// # Arguments
///
/// * `fields` - The class's field uses.
/// * `votes` - The method's votes.
fn add_votes(fields: &mut BTreeMap<u64, FieldUse>, votes: &Votes) {
    for (off, member, n) in votes {
        *fields
            .entry(*off)
            .or_default()
            .names
            .entry(member.clone())
            .or_insert(0) += n;
    }
}

/// Returns the member name most of a field's assert votes agree on.
///
/// [`collect_assert_names`] records `IsLocked()` for a condition that calls
/// a method, which says what reads the field, not what the field is called;
/// rendering the field as `this->IsLocked()` would put a call in the text
/// where the code reads memory, so those votes do not stand for a name and
/// do not count against the ones that do.
///
/// # Arguments
///
/// * `f` - The field's uses.
///
/// # Returns
///
/// The name, or `None` when no member name holds a majority.
fn majority_member(f: &FieldUse) -> Option<String> {
    let members = || f.names.iter().filter(|(n, _)| !n.ends_with(')'));
    let total: usize = members().map(|(_, n)| *n).sum();
    members()
        .max_by_key(|(_, n)| **n)
        .filter(|(_, votes)| **votes * 2 > total)
        .map(|(n, _)| n.clone())
}

/// Rewrites a class name with its template arguments stripped.
///
/// `Util::Array<Core::Ptr<UI::Icon> >` becomes `Util::Array<>`, the key the
/// instantiations of one template share.
///
/// # Arguments
///
/// * `class` - Qualified class name.
///
/// # Returns
///
/// The name with each argument list replaced by `<>`.
fn generic_name(class: &str) -> String {
    let mut out = String::with_capacity(class.len());
    let mut depth = 0u32;
    let bytes = class.as_bytes();
    for (i, c) in class.char_indices() {
        match c {
            '<' => {
                depth += 1;
                if depth == 1 {
                    out.push_str("<>");
                }
            }
            '>' if bytes.get(i.wrapping_sub(1)) != Some(&b'-') => depth = depth.saturating_sub(1),
            _ if depth == 0 => out.push(c),
            _ => {}
        }
    }
    out
}

/// Most sibling instantiations decompiled for the shared field names.
///
/// The names a template agrees on repeat in nearly every method, so a small
/// sample settles them and the biggest templates stay cheap.
const SIBLING_METHODS_MAX: usize = 24;

/// Longest assert condition read when looking for a member name.
const MEMBER_STRING_CAP: usize = 160;

/// Tells whether a function can name a field at all.
///
/// [`collect_assert_names`] reads the name out of a quoted condition, so a
/// function that references no string holding `this->` cannot contribute
/// one. Checking the referenced bytes costs a read where decompiling the
/// function costs a decompile, and the classes with the most methods are the
/// ones where that matters.
///
/// # Arguments
///
/// * `program` - The loaded image, read for the strings.
/// * `analysis` - Cross-references.
/// * `entry` - The function's entry address.
///
/// # Returns
///
/// Whether some referenced string mentions a member of `this`.
pub(crate) fn asserts_a_member(program: &Program, analysis: &Analysis, entry: u64) -> bool {
    analysis.refs_from(entry).iter().any(|&(target, _)| {
        program
            .section_at(target)
            .is_some_and(|s| !s.executable)
            .then(|| crate::strings::cstr_at(program, target, 4, MEMBER_STRING_CAP))
            .flatten()
            .is_some_and(|(_, t)| t.contains("this->"))
    })
}

/// Renders the four characters of a code, unprintable bytes as `?`.
///
/// # Arguments
///
/// * `code` - The registered code.
pub(crate) fn four_chars(code: u32) -> String {
    code.to_be_bytes()
        .iter()
        .map(|b| {
            if (0x20..0x7f).contains(b) {
                char::from(*b)
            } else {
                '?'
            }
        })
        .collect()
}

/// Renders a four-character class code as its text, quoted, or as its
/// value when a byte of it is unprintable.
///
/// The value of four printable characters is theirs to compute, so it is
/// not repeated beside them; a code with an unprintable byte has no text
/// that names it exactly and is its value instead.
///
/// # Arguments
///
/// * `code` - The registered code.
///
/// # Returns
///
/// `'GMTg'`, or `0x01584954` when a byte is unprintable.
pub fn fourcc(code: u32) -> String {
    code_text(code).map_or_else(|| format!("{code:#010x}"), |text| format!("'{text}'"))
}

/// Renders a four-character code as its text, unquoted, or as its value
/// when a byte of it is unprintable ([`fourcc`] without the quotes).
///
/// # Arguments
///
/// * `code` - The registered code.
pub(crate) fn code_or_hex(code: u32) -> String {
    code_text(code).unwrap_or_else(|| format!("{code:#010x}"))
}

/// The four characters of a code when every byte is printable.
///
/// # Arguments
///
/// * `code` - The registered code.
fn code_text(code: u32) -> Option<String> {
    let bytes = code.to_be_bytes();
    bytes
        .iter()
        .all(|b| (0x20..0x7f).contains(b))
        .then(|| bytes.iter().map(|&b| char::from(b)).collect())
}

/// Returns the getter more than half of a field's assert votes call, when
/// none of them names a member.
///
/// # Arguments
///
/// * `f` - The field's uses.
///
/// # Returns
///
/// The getter's name without its parentheses (`IsSet`), or `None` when a
/// vote names a member or no getter holds a majority.
fn sole_reader(f: &FieldUse) -> Option<String> {
    if f.names.keys().any(|n| !n.ends_with(')')) {
        return None;
    }
    let total: usize = f.names.values().sum();
    f.names
        .iter()
        .max_by_key(|(_, n)| **n)
        .filter(|(_, votes)| **votes * 2 > total)
        .and_then(|(n, _)| n.strip_suffix("()"))
        .map(str::to_owned)
}

/// Names a field from a guarded assert.
///
/// `if (COND) {` followed by `helper("EXPR", ..., __FUNCSIG__...);` ties the
/// one field `COND` dereferences (`(this + off)`) to the one `this->member`
/// `EXPR` mentions, the way `if (*(uint32_t*)(this + 0x38) < 0) {
/// n_assert("i <= this->strLen") }` names `Util::String`'s field 0x38
/// `strLen`. Anything with several fields or several members is skipped.
///
/// # Arguments
///
/// * `guard` - The previous line.
/// * `call` - The current line.
/// * `fields` - Field uses; the vote lands on the dereferenced offset.
fn collect_assert_names(guard: &str, call: &str, fields: &mut BTreeMap<u64, FieldUse>) {
    if !(guard.starts_with("if (") && guard.ends_with('{') && call.contains("__FUNCSIG__")) {
        return;
    }
    let Some(expr) = call
        .split_once('"')
        .and_then(|(_, rest)| rest.split_once('"'))
        .map(|(e, _)| e)
    else {
        return;
    };
    let members: BTreeSet<String> = expr
        .match_indices("this->")
        .map(|(i, _)| {
            let rest = expr.get(i + 6..).unwrap_or("");
            let ident = ident_prefix(rest);
            if rest.get(ident.len()..).is_some_and(|r| r.starts_with('(')) {
                format!("{ident}()")
            } else {
                ident.to_owned()
            }
        })
        .filter(|m| !m.is_empty() && m != "()")
        .collect();
    let offsets: BTreeSet<u64> = guard
        .match_indices("(this + ")
        .filter_map(|(i, _)| {
            let rest = guard.get(i + 8..)?;
            let end = rest.find(')')?;
            parse_number(rest.get(..end)?).map(|(v, _)| v)
        })
        .collect();
    let (Some(member), Some(off)) = (single(&members), single(&offsets)) else {
        return;
    };
    *fields
        .entry(*off)
        .or_default()
        .names
        .entry(member.clone())
        .or_insert(0) += 1;
}

/// Returns the identifier at the start of `s` (letters, digits, `_`).
///
/// # Arguments
///
/// * `s` - Text starting at the identifier.
fn ident_prefix(s: &str) -> &str {
    let end = s
        .find(|c: char| !(c.is_ascii_alphanumeric() || c == '_'))
        .unwrap_or(s.len());
    s.get(..end).unwrap_or("")
}

/// Returns the qualified callee name ending right before the `(` at `paren`.
///
/// Identifier characters, `::` and balanced template brackets belong to the
/// name; anything else ends it. Keywords such as `if` and `while` return a
/// name too, which no signature matches.
///
/// # Arguments
///
/// * `line` - The line.
/// * `paren` - Byte index of the opening parenthesis.
fn callee_before(line: &str, paren: usize) -> Option<&str> {
    let head = line.get(..paren)?;
    let mut depth = 0i32;
    let mut start = head.len();
    for (i, c) in head.char_indices().rev() {
        match c {
            '>' => depth += 1,
            '<' => depth -= 1,
            _ if depth > 0 => {}
            c if c.is_ascii_alphanumeric() || c == '_' || c == ':' || c == '~' => {}
            _ => break,
        }
        start = i;
    }
    let name = head.get(start..)?;
    (!name.is_empty() && name.starts_with(|c: char| c.is_ascii_alphabetic() || c == '_'))
        .then_some(name)
}

/// Splits the arguments of the call whose `(` is at `paren` at top-level
/// commas, honoring nested parentheses, template brackets and string
/// literals.
///
/// # Arguments
///
/// * `line` - The line.
/// * `paren` - Byte index of the opening parenthesis.
///
/// # Returns
///
/// The trimmed arguments, or `None` when the call is unterminated.
fn call_args(line: &str, paren: usize) -> Option<Vec<&str>> {
    let mut depth = 0i32;
    let mut in_str = false;
    let mut escaped = false;
    let mut start = paren + 1;
    let mut out = Vec::new();
    for (i, c) in line.char_indices().skip_while(|(i, _)| *i <= paren) {
        if in_str {
            if escaped {
                escaped = false;
            } else if c == '\\' {
                escaped = true;
            } else if c == '"' {
                in_str = false;
            }
            continue;
        }
        match c {
            '"' => in_str = true,
            '(' | '<' | '[' => depth += 1,
            ',' if depth == 0 => {
                out.push(line.get(start..i)?.trim());
                start = i + 1;
            }
            ')' | '>' | ']' if depth > 0 => depth -= 1,
            ')' => {
                let last = line.get(start..i)?.trim();
                if !last.is_empty() {
                    out.push(last);
                }
                return Some(out);
            }
            _ => {}
        }
    }
    None
}

/// Recognizes a field operand in a call argument.
///
/// # Arguments
///
/// * `arg` - One trimmed argument.
///
/// # Returns
///
/// `(offset, is_pointer_load)`: `this + off` gives the field's address,
/// `*(uint64_t*)(this + off)` the pointer stored in it; a bare `this` is the
/// object itself passed on, not a field, and yields `None`.
fn field_operand(arg: &str) -> Option<(u64, bool)> {
    let (inner, pointer) = match arg.strip_prefix("*(uint64_t*)") {
        Some(rest) => (
            rest.strip_prefix('(')
                .and_then(|r| r.strip_suffix(')'))
                .unwrap_or(rest),
            true,
        ),
        None => (arg, false),
    };
    if inner == "this" {
        return pointer.then_some((0, true));
    }
    let rest = inner.strip_prefix("this + ")?;
    let (v, n) = parse_number(rest)?;
    (n == rest.len()).then_some((v, pointer))
}

/// Returns the right-hand side when `tail` starts with an assignment
/// (`= v`, `+= v`, `|= v`, ...), not a comparison.
///
/// # Arguments
///
/// * `tail` - Text after the access.
fn assignment_rhs(tail: &str) -> Option<&str> {
    let t = tail.trim_start();
    if t.starts_with("==") {
        return None;
    }
    let t = t.trim_start_matches(|c: char| "+-*/%&|^".contains(c));
    t.strip_prefix('=')
        .filter(|r| !r.starts_with('='))
        .map(str::trim_start)
}

/// Parses a decimal or `0x` hexadecimal literal at the start of `s`.
///
/// # Arguments
///
/// * `s` - Text starting at the literal.
///
/// # Returns
///
/// `(value, bytes consumed)`, or `None`.
fn parse_number(s: &str) -> Option<(u64, usize)> {
    let (digits, radix, skip) = match s.strip_prefix("0x") {
        Some(h) => (h, 16, 2),
        None => (s, 10, 0),
    };
    let n = digits
        .find(|c: char| !c.is_ascii_hexdigit())
        .unwrap_or(digits.len());
    let end = if radix == 10 {
        digits
            .find(|c: char| !c.is_ascii_digit())
            .unwrap_or(digits.len())
    } else {
        n
    };
    if end == 0 {
        return None;
    }
    let v = u64::from_str_radix(digits.get(..end)?, radix).ok()?;
    if digits
        .get(end..)?
        .starts_with(|c: char| c.is_ascii_alphanumeric() || c == '_')
    {
        return None;
    }
    Some((v, skip + end))
}

/// The `*(type*)(` ... `)` cast around an object operand, read.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Deref<'a> {
    /// Width in bits; `0` when the type is unknown.
    width: u8,
    /// The type is floating-point.
    float: bool,
    /// The text after the whole access.
    tail: &'a str,
    /// Index in the text before the operand where the `*(type*)` cast
    /// starts.
    cast_start: usize,
}

/// Recognizes the `*(type*)(` ... `)` around an `a1 [+ off]` operand.
///
/// # Arguments
///
/// * `before` - Text before the operand.
/// * `rest` - Text after the operand (the closing parenthesis, if any).
///
/// # Returns
///
/// The cast, or `None` when the operand is not dereferenced.
fn deref_width<'a>(before: &str, rest: &'a str) -> Option<Deref<'a>> {
    let (head, tail) = if before.ends_with('(') {
        (before.get(..before.len() - 1)?, rest.strip_prefix(')')?)
    } else {
        (before, rest)
    };
    let head = head.trim_end();
    let cast = head.strip_suffix("*)")?;
    let open = cast.rfind('(')?;
    let ty = cast.get(open + 1..)?;
    let star = open.checked_sub(1)?;
    if head.get(star..open)? != "*" {
        return None;
    }
    let (width, float) = match ty {
        "uint8_t" | "int8_t" => (8, false),
        "uint16_t" | "int16_t" => (16, false),
        "uint32_t" | "int32_t" => (32, false),
        "uint64_t" | "int64_t" => (64, false),
        "uint128_t" => (128, false),
        "float" => (32, true),
        "double" => (64, true),
        _ => (0, false),
    };
    Some(Deref {
        width,
        float,
        tail,
        cast_start: star,
    })
}

/// One `(base, offset)` field access a single function makes.
#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct AccessSite {
    /// Access widths seen, in bits (`8`, `32`, `64`, ...); `0` marks a cast
    /// whose width the renderer left unknown.
    pub widths: BTreeSet<u8>,
    /// The access was floating-point at least once.
    pub float: bool,
    /// Loads through the base at this offset.
    pub reads: usize,
    /// Stores through the base at this offset.
    pub writes: usize,
    /// Constants stored here (a vptr, an enum value, a flag).
    pub constants: BTreeSet<u64>,
}

/// Every pointer-relative field access one function makes, as its
/// decompilation shows them, keyed by `(base, byte offset)`.
///
/// This is the per-function counterpart of [`class_layout`]: where that unions
/// a whole class's field uses, this reads one function and reports the offsets
/// it dereferences off each pointer it holds — `this`, an argument, a local, or
/// a register that a `Core::Ptr<T>::operator ->` handed back. A caller with a
/// field it believes a function reads (an SDK's `@derive`-style anchor) can
/// confirm the offset is a real typed access rather than a coincidental byte,
/// and see the width and direction; when a build moves the field, the offset it
/// moved to is right here instead of a byte search coming up empty.
///
/// Both operand orders are read (`base + 0x10` and `0x10 + base`), and a bare
/// `*(T*)base` is offset zero. Only dereferences are recorded, so an address
/// taken for arithmetic is not mistaken for a field.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Discovery results.
/// * `overlay` - Names in force.
/// * `entry` - The function's entry address.
///
/// # Returns
///
/// The accesses by `(base, offset)`, or `None` when the function does not
/// decompile.
pub fn field_accesses(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    entry: u64,
) -> Option<BTreeMap<(String, u64), AccessSite>> {
    let text = decompile_plain(program, analysis, overlay, entry)?;
    let mut sites: BTreeMap<(String, u64), AccessSite> = BTreeMap::new();
    let mut var_class: BTreeMap<String, String> = BTreeMap::new();
    for line in text.lines() {
        let line = line.trim();
        if let Some((lhs, rhs)) = line.split_once(" = ")
            && is_identifier(lhs.trim())
        {
            match smart_pointer_class(rhs) {
                Some(c) => var_class.insert(lhs.trim().to_owned(), c),
                None => var_class.remove(lhs.trim()),
            };
        }
        collect_general_accesses(line, &mut sites, &var_class);
    }
    Some(sites)
}

/// Whether `s` is a bare identifier, the shape of a variable on a line's left.
///
/// # Arguments
///
/// * `s` - The text to test.
fn is_identifier(s: &str) -> bool {
    !s.is_empty() && s.bytes().all(|c| c.is_ascii_alphanumeric() || c == b'_')
}

/// The class a smart pointer holds: `T` for `X<T>` or `X<T, D>` when the
/// template's last name component names a pointer (`Core::Ptr`,
/// `std::shared_ptr`, `ComPtr`, `QPointer`) and `T` is one plain name.
///
/// # Arguments
///
/// * `class` - The smart pointer's class text.
#[must_use]
pub fn smart_pointee(class: &str) -> Option<&str> {
    let class = class.trim();
    let open = class.find('<')?;
    let head = class.get(..open)?;
    let last = head
        .rsplit("::")
        .next()
        .unwrap_or(head)
        .to_ascii_lowercase();
    if !(last.contains("ptr") || last.contains("pointer")) {
        return None;
    }
    let inner = class.strip_suffix('>')?.get(open + 1..)?;
    let first = inner.split(',').next()?.trim();
    (!first.is_empty() && !first.contains('<')).then_some(first)
}

/// Where a line's first smart-pointer dereference starts, and its class.
///
/// `x = Core::Ptr<T>::operator ->(a2)` gives the offset of `Core` and `T`,
/// as does `std::shared_ptr<T>::operator ->(`.
///
/// # Arguments
///
/// * `line` - One pseudo-C line.
#[must_use]
pub fn deref_call(line: &str) -> Option<(usize, &str)> {
    let at = line.find(">::operator ->(")?;
    let mut depth = 0usize;
    let mut open = None;
    for (i, b) in line.get(..=at)?.bytes().enumerate().rev() {
        match b {
            b'>' => depth += 1,
            b'<' => {
                depth = depth.checked_sub(1)?;
                if depth == 0 {
                    open = Some(i);
                    break;
                }
            }
            _ => {}
        }
    }
    let start = line
        .get(..open?)?
        .rfind(|c: char| !(c.is_ascii_alphanumeric() || c == '_' || c == ':'))
        .map_or(0, |i| i + 1);
    Some((start, smart_pointee(line.get(start..=at)?)?))
}

/// The class a line's first smart-pointer dereference hands out; see
/// [`deref_call`].
///
/// # Arguments
///
/// * `line` - One pseudo-C line.
#[must_use]
pub fn deref_pointee(line: &str) -> Option<&str> {
    deref_call(line).map(|(_, class)| class)
}

/// The class a smart pointer's `operator ->` call yields, when the right-hand
/// side of an assignment is one.
///
/// `Core::Ptr<Cmd::Item>::operator ->(&cmd)` yields a
/// `Cmd::Item`, so the variable it is assigned to points at
/// one. A nested template argument is left alone rather than guessed at.
///
/// # Arguments
///
/// * `rhs` - The assignment's right-hand side.
fn smart_pointer_class(rhs: &str) -> Option<String> {
    let head = rhs.split("::operator ->(").next()?;
    let open = head.find('<')?;
    let inner = head.strip_suffix('>')?.get(open + 1..)?.trim();
    (!inner.is_empty() && !inner.contains('<')).then(|| inner.to_owned())
}

/// Records every `*(type*)(base ± off)` and `*(type*)base` dereference on one
/// pseudo-C line into `sites`, keyed by `(base, offset)`.
///
/// # Arguments
///
/// * `line` - The trimmed line.
/// * `sites` - The accesses collected so far.
fn collect_general_accesses(
    line: &str,
    sites: &mut BTreeMap<(String, u64), AccessSite>,
    var_class: &BTreeMap<String, String>,
) {
    let bytes = line.as_bytes();
    let n = line.len();
    let mut i = 0;
    while i < n {
        let starts = {
            let c = bytes[i];
            (c.is_ascii_alphabetic() || c == b'_')
                && (i == 0 || !(bytes[i - 1].is_ascii_alphanumeric() || bytes[i - 1] == b'_'))
        };
        if !starts {
            i += 1;
            continue;
        }
        let s = i;
        let mut e = i + 1;
        while e < n && (bytes[e].is_ascii_alphanumeric() || bytes[e] == b'_') {
            e += 1;
        }
        i = e;
        let base = &line[s..e];
        let (offset, span_start, span_end) = if let Some(rest) = line[e..].strip_prefix(" + ") {
            match parse_number(rest) {
                Some((v, consumed)) => (v, s, e + 3 + consumed),
                None => (0, s, e),
            }
        } else if let Some(head) = line[..s].strip_suffix(" + ") {
            match trailing_number(head) {
                Some((v, start)) => (v, start, e),
                None => (0, s, e),
            }
        } else {
            (0, s, e)
        };
        let Some(d) = deref_width(&line[..span_start], &line[span_end..]) else {
            continue;
        };
        let base = var_class
            .get(base)
            .cloned()
            .unwrap_or_else(|| base.to_owned());
        let site = sites.entry((base, offset)).or_default();
        if d.width != 0 {
            site.widths.insert(d.width);
        }
        site.float |= d.float;
        let opens_statement = line
            .get(..d.cast_start)
            .is_some_and(|lhs| lhs.trim().is_empty());
        if opens_statement && let Some(rhs) = assignment_rhs(d.tail) {
            site.writes += 1;
            if let Some((c, _)) = parse_number(rhs) {
                site.constants.insert(c);
            }
        } else {
            site.reads += 1;
        }
    }
}

/// Parses a decimal or `0x` literal that ends `s`, for the `NUM + base` form.
///
/// # Arguments
///
/// * `s` - Text ending at the literal (the ` + ` already stripped).
///
/// # Returns
///
/// `(value, start index in `s`)` when a whole literal on a token boundary ends
/// `s`, else `None`.
fn trailing_number(s: &str) -> Option<(u64, usize)> {
    let bytes = s.as_bytes();
    let mut start = s.len();
    while start > 0 && {
        let b = bytes[start - 1];
        b.is_ascii_hexdigit() || b == b'x'
    } {
        start -= 1;
    }
    let boundary =
        start == 0 || !(bytes[start - 1].is_ascii_alphanumeric() || bytes[start - 1] == b'_');
    if !boundary {
        return None;
    }
    let cand = s.get(start..)?;
    let (v, consumed) = parse_number(cand)?;
    (consumed == cand.len()).then_some((v, start))
}

/// Renders a function's field accesses as TSV, one row per `(base, offset)`.
///
/// The header names the function; each row is `base`, `offset` (hex), the
/// widths in bytes (slash-separated), the direction (`r`, `w`, or `rw`), and
/// any constants stored there. Rows are ordered by base then offset so a diff
/// of two builds lines up.
///
/// The base is the class of the object when an assignment named it (a smart
/// pointer's `operator ->`), else the variable holding it. Naming the object
/// is what separates the several objects one register carries: the opcode a
/// command handler writes reads as `Cmd::Item 0x24 = 0x13`
/// rather than an anonymous store through `rax` merged with a read of the
/// message at the same offset.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Discovery results.
/// * `overlay` - Names in force.
/// * `entry` - The function's entry address.
///
/// # Returns
///
/// The TSV, or `None` when the function does not decompile.
pub fn fields_tsv(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    entry: u64,
) -> Option<String> {
    let sites = field_accesses(program, analysis, overlay, entry)?;
    let name = name_of(analysis, overlay, entry);
    let mut out = String::new();
    let _ = writeln!(
        out,
        "# fields dereferenced by {name} @ {entry:#x}: {} sites",
        sites.len()
    );
    let _ = writeln!(out, "base\toffset\twidths\tdir\tconstants");
    for ((base, offset), site) in &sites {
        let widths = if site.widths.is_empty() {
            "?".to_owned()
        } else {
            site.widths
                .iter()
                .map(|b| (u16::from(*b) / 8).to_string())
                .collect::<Vec<_>>()
                .join("/")
        };
        let dir = match (site.reads > 0, site.writes > 0) {
            (true, true) => "rw",
            (false, true) => "w",
            _ => "r",
        };
        let consts = site
            .constants
            .iter()
            .map(|c| format!("{c:#x}"))
            .collect::<Vec<_>>()
            .join(",");
        let _ = writeln!(out, "{base}\t{offset:#x}\t{widths}\t{dir}\t{consts}");
    }
    Some(out)
}

/// Most store expressions one function lists in a typed field answer.
const STORES_SHOWN: usize = 3;
/// Longest store expression listed, in characters, before it is clipped.
const STORE_TEXT_MAX: usize = 96;

/// One function's uses of a class's field through a pointer typed as the
/// class.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TypedFieldUse {
    /// The function's entry.
    pub entry: u64,
    /// The variables the function reaches the object through: a parameter
    /// its signature types as the class (`this`, `a2`), or one a smart
    /// pointer's `operator ->` for the class assigned (`rax`).
    pub via: BTreeSet<String>,
    /// The loads, stores and address-takens at the field, with the
    /// constants stored.
    pub field: FieldUse,
    /// Right-hand sides of the stores that are not a constant, clipped, at
    /// most [`STORES_SHOWN`].
    pub stores: Vec<String>,
    /// The function's instructions addressing `[reg + offset]` at a width
    /// and in a direction its typed uses have, in address order.
    pub sites: Vec<u64>,
}

/// Who uses one field of a class, by function.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TypedFieldUses {
    /// The class as the method index spells it.
    pub class: String,
    /// The classes derived from it, whose pointers reach the field too.
    pub derived: Vec<String>,
    /// The field's source name, when asserts give it one.
    pub name: Option<String>,
    /// The functions using the field, in address order.
    pub uses: Vec<TypedFieldUse>,
    /// Functions that might hold a pointer to the class, all decompiled
    /// unless [`TypedFieldUses::sampled`].
    pub candidates: usize,
    /// Only the first [`METHODS_MAX`] candidates were decompiled.
    pub sampled: bool,
}

/// Finds the functions using the field at `offset` of `class` through a
/// pointer typed as the class or as a class derived from it.
///
/// The inverse of [`class_layout`] for one field: a byte search for
/// `[reg + offset]` finds the same sites among every other object's field at
/// that offset, and a filter on function names misses the unnamed ones. The
/// candidates are the methods of the class and of every class derived from
/// it, the functions a caller hinted or a signature declared a parameter of
/// one of them for, and the callers of a smart pointer's `operator ->` for
/// one of them, methods first. A method's object is its first parameter, as
/// [`class_layout`] reads it; any other candidate's own `// signature:` line
/// decides which of its parameters point at the class, as its decompile
/// shows them; and a variable assigned from such an `operator ->` points at
/// it until it is assigned again. Built once per class, offset and overlay.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Discovery results.
/// * `overlay` - Names in force.
/// * `class` - The class as [`resolve_class`] reads it, or a class known by
///   its vtable alone.
/// * `offset` - The field's byte offset in the class.
///
/// # Returns
///
/// The uses, or `None` when no class is so named.
pub fn typed_field_uses(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    class: &str,
    offset: u64,
) -> Option<Arc<TypedFieldUses>> {
    let class = resolve_class(analysis, overlay, class).or_else(|| {
        analysis
            .classes
            .by_name
            .contains_key(class)
            .then(|| class.to_owned())
    })?;
    let key = (class.clone(), offset);
    let names = overlay.fingerprint();
    Some(
        analysis
            .derived
            .get_or_build_named("typed_field_uses", names, key, || {
                let family = class_family(analysis, &class);
                let (methods, candidates) = typed_candidates(analysis, overlay, &family);
                let read = &candidates[..candidates.len().min(METHODS_MAX)];
                let mut uses: Vec<TypedFieldUse> = striped(read, |&entry| {
                    let method = methods.contains(&entry);
                    typed_use_in(program, analysis, overlay, &family, (entry, method), offset)
                })
                .into_iter()
                .flatten()
                .flatten()
                .collect();
                uses.sort_by_key(|u| u.entry);
                TypedFieldUses {
                    name: field_labels(program, analysis, overlay, &class)
                        .remove(&offset)
                        .map(|label| label.to_string()),
                    derived: family.into_iter().filter(|c| *c != class).collect(),
                    class,
                    uses,
                    candidates: candidates.len(),
                    sampled: read.len() < candidates.len(),
                }
            }),
    )
}

/// The class and every class derived from it, directly or not.
///
/// # Arguments
///
/// * `analysis` - Discovery results, with each class's parent.
/// * `class` - The qualified class name.
fn class_family(analysis: &Analysis, class: &str) -> BTreeSet<String> {
    let mut family = BTreeSet::from([class.to_owned()]);
    loop {
        let more: Vec<String> = analysis
            .classes
            .by_name
            .values()
            .filter(|c| {
                !family.contains(&c.name) && c.parent.as_ref().is_some_and(|p| family.contains(p))
            })
            .map(|c| c.name.clone())
            .collect();
        if more.is_empty() {
            return family;
        }
        family.extend(more);
    }
}

/// The functions that may hold a pointer to a class of `family`.
///
/// Its methods come first, then in address order every function a caller
/// hinted or a signature declared a parameter of one for, and every caller
/// of a smart pointer's `operator ->` for one.
///
/// # Arguments
///
/// * `analysis` - Discovery results.
/// * `overlay` - User names take precedence.
/// * `family` - The class and the classes derived from it.
///
/// # Returns
///
/// The methods, and every candidate in that order.
fn typed_candidates(
    analysis: &Analysis,
    overlay: &Overlay,
    family: &BTreeSet<String>,
) -> (BTreeSet<u64>, Vec<u64>) {
    let methods: BTreeSet<u64> = family
        .iter()
        .flat_map(|c| methods_of(analysis, overlay, c))
        .collect();
    let mut others = BTreeSet::new();
    for f in &analysis.functions {
        let hinted = f.param_hints.values().any(|c| family.contains(c));
        let declared = f.signature.as_ref().is_some_and(|s| {
            s.params
                .iter()
                .any(|p| family.iter().any(|c| p.contains(c.as_str())))
        });
        if hinted || declared {
            others.insert(f.entry);
        }
        let accessor = declared_name(overlay, f)
            .filter(|n| n.ends_with("::operator ->"))
            .and_then(class_of)
            .and_then(smart_pointee)
            .is_some_and(|t| family.contains(t));
        if accessor {
            others.extend(&f.callers);
        }
    }
    let all = methods
        .iter()
        .chain(others.difference(&methods))
        .copied()
        .collect();
    (methods, all)
}

/// The parameter a signature's parameter text names when it points at a
/// class of `family` (`Net::Client *a1`, `const Foo &this`).
///
/// # Arguments
///
/// * `param` - One parameter as a `// signature:` line spells it.
/// * `family` - The class and the classes derived from it.
fn typed_pointer(param: &str, family: &BTreeSet<String>) -> Option<String> {
    let start = param.rfind(|c: char| !(c.is_ascii_alphanumeric() || c == '_'))? + 1;
    let (ty, name) = param.split_at(start);
    let pointee = ty
        .trim_end()
        .strip_suffix(['*', '&'])?
        .trim()
        .trim_start_matches("const ");
    let pointee = pointee
        .strip_prefix("class ")
        .or_else(|| pointee.strip_prefix("struct "))
        .unwrap_or(pointee);
    (family.contains(pointee) && is_identifier(name)).then(|| name.to_owned())
}

/// The uses one function makes of the field at `offset` through a pointer
/// typed as a class of `family`.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Discovery results.
/// * `overlay` - Names in force.
/// * `family` - The class and the classes derived from it.
/// * `(entry, method)` - The function's entry, and whether it is a method of
///   a class of `family`, whose first parameter is its object.
/// * `offset` - The field's byte offset.
///
/// # Returns
///
/// The uses, or `None` when the function does not decompile or never
/// touches the field through such a pointer.
fn typed_use_in(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    family: &BTreeSet<String>,
    (entry, method): (u64, bool),
    offset: u64,
) -> Option<TypedFieldUse> {
    let text = decompile_plain(program, analysis, overlay, entry)?;
    let mut vars: BTreeSet<String> = text
        .lines()
        .find_map(|l| l.strip_prefix("// signature: "))
        .and_then(super::schema::signature_params)
        .unwrap_or_default()
        .iter()
        .filter_map(|p| typed_pointer(p, family))
        .collect();
    if method {
        vars.extend(["this", "a1"].map(str::to_owned));
    }
    let mut via = BTreeSet::new();
    let mut fields: BTreeMap<u64, FieldUse> = BTreeMap::new();
    let mut stores = Vec::new();
    let count = |fields: &BTreeMap<u64, FieldUse>| {
        fields
            .get(&offset)
            .map_or((0, 0), |f| (f.reads + f.writes + f.address_taken, f.writes))
    };
    for line in text.lines() {
        let t = line.trim();
        if t.starts_with("//") {
            continue;
        }
        for var in &vars {
            let (seen, writes) = count(&fields);
            collect_accesses_of(var, t, entry, &mut fields);
            let (seen_now, writes_now) = count(&fields);
            if seen_now > seen {
                via.insert(var.clone());
            }
            if writes_now > writes
                && stores.len() < STORES_SHOWN
                && let Some((_, rhs)) = t.split_once(" = ")
            {
                let rhs = rhs.trim_end_matches(';').trim();
                if parse_number(rhs).is_none_or(|(_, n)| n < rhs.len()) {
                    stores.push(rhs.chars().take(STORE_TEXT_MAX).collect());
                }
            }
        }
        if let Some((lhs, rhs)) = t.split_once(" = ")
            && is_identifier(lhs.trim())
        {
            match smart_pointer_class(rhs).filter(|c| family.contains(c)) {
                Some(_) => vars.insert(lhs.trim().to_owned()),
                None => vars.remove(lhs.trim()),
            };
        }
    }
    let field = fields.remove(&offset)?;
    let sites = match (
        analysis.function(entry),
        program.arch.bitness(),
        i64::try_from(offset),
    ) {
        (Some(f), Some(bitness), Ok(off)) => super::fieldrefs::refs_in(program, f, bitness, off)
            .into_iter()
            .filter(|r| typed_site(r, &field))
            .map(|r| r.va)
            .collect(),
        _ => Vec::new(),
    };
    Some(TypedFieldUse {
        entry,
        via,
        field,
        stores,
        sites,
    })
}

/// Whether an instruction addressing the field's offset does what the
/// function's typed uses of the field do: a width they use (or none known)
/// and a direction they have.
///
/// # Arguments
///
/// * `site` - The instruction.
/// * `field` - The typed uses.
fn typed_site(site: &FieldRef, field: &FieldUse) -> bool {
    let width = site.width == 0
        || field.widths.is_empty()
        || site
            .width
            .checked_mul(8)
            .and_then(|bits| u8::try_from(bits).ok())
            .is_some_and(|bits| field.widths.contains(&bits));
    let direction = match site.access {
        FieldAccess::Read => field.reads > 0,
        FieldAccess::Write => field.writes > 0,
        FieldAccess::ReadWrite => field.reads + field.writes > 0,
        FieldAccess::Address => field.address_taken > 0,
    };
    width && direction
}

/// Renders the uses of one class field as a `#`-headed table, one row per
/// function, paged.
///
/// # Arguments
///
/// * `uses` - What [`typed_field_uses`] found.
/// * `analysis` - For function names.
/// * `overlay` - Names in force.
/// * `offset` - The field's byte offset.
/// * `skip` - Rows to skip.
/// * `limit` - Rows shown at most.
/// * `count_only` - Print the header line alone.
#[must_use]
pub fn typed_field_uses_tsv(
    uses: &TypedFieldUses,
    analysis: &Analysis,
    overlay: &Overlay,
    offset: u64,
    skip: usize,
    limit: usize,
    count_only: bool,
) -> String {
    /// Most derived classes the header names.
    const DERIVED_SHOWN: usize = 4;
    let total = uses.uses.len();
    let sum = |f: fn(&FieldUse) -> usize| uses.uses.iter().map(|u| f(&u.field)).sum::<usize>();
    let derived = match uses.derived.len() {
        0 => String::new(),
        n => format!(
            " or as a class derived from it ({}{})",
            uses.derived
                .iter()
                .take(DERIVED_SHOWN)
                .map(String::as_str)
                .collect::<Vec<_>>()
                .join(", "),
            if n > DERIVED_SHOWN {
                format!(", +{}", n - DERIVED_SHOWN)
            } else {
                String::new()
            }
        ),
    };
    let sampled = if uses.sampled {
        format!(
            "; only the first {METHODS_MAX} of {} candidate functions were read",
            uses.candidates
        )
    } else {
        String::new()
    };
    let mut out = format!(
        "# {}+{offset:#x}{}: {total} functions use it through a pointer typed as the class (a method's object, a typed parameter, a smart pointer's operator ->){derived}: {} stores, {} loads, {} address-takens{sampled}",
        uses.class,
        uses.name
            .as_ref()
            .map_or_else(String::new, |n| format!(" {n}")),
        sum(|f| f.writes),
        sum(|f| f.reads),
        sum(|f| f.address_taken),
    );
    if count_only {
        out.push('\n');
        return out;
    }
    let shown = total.saturating_sub(skip).min(limit);
    let _ = writeln!(out, ", showing {shown} from {skip}");
    let _ = writeln!(
        out,
        "# sites: the function's instructions addressing [reg+{offset:#x}] at the width and in the direction it uses the field"
    );
    out.push_str("entry\tfunction\tvia\tdir\tstored\tsites\n");
    for u in uses.uses.iter().skip(skip).take(limit) {
        let dir: String = [
            (u.field.reads > 0, 'r'),
            (u.field.writes > 0, 'w'),
            (u.field.address_taken > 0, '&'),
        ]
        .iter()
        .filter_map(|&(on, c)| on.then_some(c))
        .collect();
        let stored: Vec<String> = u
            .field
            .constants
            .iter()
            .map(|c| format!("{c:#x}"))
            .chain(u.stores.iter().cloned())
            .collect();
        let sites: Vec<String> = u.sites.iter().map(|va| format!("{va:#x}")).collect();
        let _ = writeln!(
            out,
            "{:#x}\t{}\t{}\t{dir}\t{}\t{}",
            u.entry,
            name_of(analysis, overlay, u.entry),
            u.via
                .iter()
                .map(String::as_str)
                .collect::<Vec<_>>()
                .join(","),
            stored.join("; "),
            sites.join(" ")
        );
    }
    out
}

/// Renders a layout as compact text: one line per field with offset, width,
/// reads/writes, address-takens, stored constants and up to three methods.
///
/// # Arguments
///
/// * `layout` - The recovered layout.
/// * `analysis` - For method and constant names.
/// * `overlay` - User names.
pub fn render_layout(layout: &ClassLayout, analysis: &Analysis, overlay: &Overlay) -> String {
    let mut out = String::new();
    let size = layout
        .fields
        .iter()
        .map(|(off, f)| off + u64::from(f.widths.iter().max().copied().unwrap_or(64) / 8))
        .max()
        .unwrap_or(0);
    let _ = writeln!(
        out,
        "class {}: {} methods, {} fields, size >= {size:#x}{}",
        layout.name,
        layout.methods.len(),
        layout.fields.len(),
        if layout.sampled {
            format!(" (first {METHODS_MAX} methods)")
        } else {
            String::new()
        }
    );
    if let Some(info) = analysis.classes.by_name.get(&layout.name) {
        if let Some(p) = &info.parent {
            let _ = writeln!(out, "parent:  {p}");
        }
        if let Some(code) = analysis.classes.ids.get(&layout.name) {
            let _ = writeln!(out, "wire id: {}", fourcc(*code));
        }
        if let Some(v) = info.vtable {
            let _ = writeln!(out, "vftable: {v:#x} ({} slots)", info.slots.len());
            for (i, &s) in info.slots.iter().enumerate().take(SLOTS_SHOWN) {
                let _ = writeln!(out, "  [{i}] {}", slot_name_of(analysis, overlay, s));
            }
            if info.slots.len() > SLOTS_SHOWN {
                let _ = writeln!(out, "  ... {} more", info.slots.len() - SLOTS_SHOWN);
            }
        }
        let names = |entries: &[u64]| -> String {
            entries
                .iter()
                .map(|&e| name_of(analysis, overlay, e))
                .collect::<Vec<_>>()
                .join(", ")
        };
        if !info.ctors.is_empty() {
            let _ = writeln!(out, "constructors: {}", names(&info.ctors));
        }
        if !info.creators.is_empty() {
            let _ = writeln!(out, "factories: {}", names(&info.creators));
        }
    }
    if let Some((off, _)) = analysis
        .classes
        .tls_slots
        .iter()
        .find(|(_, c)| **c == layout.name)
    {
        let _ = writeln!(out, "singleton: TLS slot {off:#x}");
    }
    if let Some((addr, _)) = analysis
        .classes
        .global_hints
        .iter()
        .find(|(_, c)| **c == layout.name)
    {
        let _ = writeln!(out, "singleton: global {addr:#x}");
    }
    let derived: Vec<&str> = analysis
        .classes
        .by_name
        .values()
        .filter(|c| c.parent.as_deref() == Some(layout.name.as_str()))
        .map(|c| c.name.as_str())
        .collect();
    if !derived.is_empty() {
        let _ = writeln!(
            out,
            "derived: {}",
            derived
                .iter()
                .take(16)
                .copied()
                .collect::<Vec<_>>()
                .join(", ")
        );
    }
    out.push_str("offset  type      r/w   methods\n");
    let prefix = format!("{}::", layout.name);
    let has_vtable = analysis
        .classes
        .by_name
        .get(&layout.name)
        .is_some_and(|c| c.vtable.is_some());
    for (off, f) in &layout.fields {
        let ty = if *off == 0 && has_vtable {
            "vftable".to_owned()
        } else if let Some(c) = analysis
            .classes
            .field_hints
            .get(&(layout.name.clone(), *off))
        {
            format!("{c} *")
        } else if let Some(t) = analysis
            .classes
            .field_types
            .get(&(layout.name.clone(), *off))
        {
            t.clone()
        } else if let Some(t) = f.types.iter().min_by_key(|t| t.len()) {
            t.clone()
        } else if f.float {
            match f.float_widths.iter().max() {
                Some(64) => "double".to_owned(),
                _ => "float".to_owned(),
            }
        } else if f.widths.is_empty() {
            "?".to_owned()
        } else {
            f.widths
                .iter()
                .map(|w| format!("u{w}"))
                .collect::<Vec<_>>()
                .join("/")
        };
        let ty = match layout.labels.get(off) {
            Some(label) => format!("{ty} {label}"),
            None => ty,
        };
        let mut names: Vec<String> = f
            .methods
            .iter()
            .take(METHODS_SHOWN)
            .map(|&m| {
                let n = name_of(analysis, overlay, m);
                n.strip_prefix(&prefix).map_or(n.clone(), str::to_owned)
            })
            .collect();
        if f.methods.len() > METHODS_SHOWN {
            names.push(format!("+{}", f.methods.len() - METHODS_SHOWN));
        }
        let mut notes = Vec::new();
        if f.address_taken > 0 {
            notes.push(format!("&x{}", f.address_taken));
        }
        for c in f.constants.iter().take(3) {
            let shown = analysis.function(*c).map_or_else(
                || format!("{c:#x}"),
                |g| name_of(analysis, overlay, g.entry),
            );
            notes.push(format!("= {shown}"));
        }
        let _ = writeln!(
            out,
            "+{off:<#6x} {ty:<9} {:>2}/{:<3} {}{}",
            f.reads,
            f.writes,
            names.join(", "),
            if notes.is_empty() {
                String::new()
            } else {
                format!("  [{}]", notes.join("; "))
            }
        );
    }
    out
}

#[cfg(test)]
mod tests {
    use super::{class_of, setter_writes, smart_pointer_class};

    /// The write after an inlined setter's assert names the offset, through
    /// the variable the smart pointer bound or a copy of it; a write through
    /// something else does not.
    ///
    /// # Panics
    ///
    /// When an offset disagrees with the sample text.
    #[test]
    fn inlined_setters_name_the_field_they_write() {
        let text = "rax = Core::Ptr<Type::Item>::operator ->(&home_0);\nrdi = rax;\nif (rax->handled != 0) {\n  assert_failed(\"!this->handled\", \"msg/protocol.h\", 129, __FUNCSIG__(Type::Item::SetMapId));\n}\nif (rbx != rdi + 32) {\n  sub_1(rdi + 32, rbx);\n}\nrsi = other;\nassert_failed(\"x\", \"f\", 1, __FUNCSIG__(Type::Item::SetExitURL));\nsub_1(rsi + 96, rbx);\n";
        let marker = "__FUNCSIG__(Type::Item::SetMapId)";
        assert_eq!(setter_writes(text, "Type::Item", marker, 4), vec![32]);
        let other = "__FUNCSIG__(Type::Item::SetExitURL)";
        assert!(setter_writes(text, "Type::Item", other, 4).is_empty());
    }

    /// A smart pointer's `operator ->` names the class the variable holds.
    ///
    /// That binding is what lets a field report say a write of `0x13` at
    /// offset 0x24 is an opcode of a `Cmd::Item` rather than
    /// an anonymous store through `rax`. A nested template argument is left
    /// alone, and anything that is not such a call names nothing.
    ///
    /// # Panics
    ///
    /// When an extraction disagrees with its expectation.
    #[test]
    fn a_smart_pointer_call_names_its_class() {
        assert_eq!(
            smart_pointer_class("Core::Ptr<Cmd::Item>::operator ->(&home_10);").as_deref(),
            Some("Cmd::Item")
        );
        assert_eq!(
            smart_pointer_class("Core::Ptr<UI::Icon>::operator ->(this + 120)").as_deref(),
            Some("UI::Icon")
        );
        assert_eq!(
            smart_pointer_class("Core::Ptr<Util::Array<int>>::operator ->(&x)"),
            None,
            "a nested template argument is not guessed at"
        );
        assert_eq!(smart_pointer_class("Memory::Free(7, rdx);"), None);
        assert_eq!(smart_pointer_class("*(uint32_t*)(rax + 0x24)"), None);
    }

    /// The class is everything before the last top-level `::`.
    ///
    /// # Panics
    ///
    /// When a split disagrees with its expectation.
    #[test]
    fn class_split_respects_templates() {
        assert_eq!(
            class_of("UI::BankWidget::GetItemFromIcon"),
            Some("UI::BankWidget")
        );
        assert_eq!(
            class_of("Util::Array<Util::KeyValuePair<a::b,c::d> >::Grow"),
            Some("Util::Array<Util::KeyValuePair<a::b,c::d> >")
        );
        assert_eq!(class_of("main"), None);
        assert_eq!(class_of("::x"), None);
    }
}
