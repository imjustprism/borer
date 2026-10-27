//! A game-modding export: what borer knows about a program's classes and
//! globals, as the files a mod author loads into their own tools.
//!
//! [`build`] gathers one [`Sdk`]: every class a vtable or RTTI names, with
//! the fields its methods access ([`super::classes::class_layout`],
//! [`super::apply::scalar_fields`]) and its virtual slots; every struct the
//! overlay states, which wins over a recovered class of the same name; the
//! global and thread-local singletons and the globals the overlay names or
//! types; and the named functions. Three renderers write it: a C++ header
//! ([`header::header`]), a Cheat Engine table ([`cheat::cheat_table`]) and a
//! ReClass.NET project ([`reclass::reclass`]).
//!
//! A recovered field is evidence, not a declaration: its width is the widest
//! access seen and a recovered class's size is only the end of its last
//! field, so each field carries an [`Evidence`] every renderer spells out.

pub mod cheat;
pub mod header;
pub mod reclass;

use std::collections::{BTreeMap, BTreeSet};

use super::classes::{ClassLayout, FieldUse, class_layout};
use super::utypes::{TypeExpr, UserStruct, UserType, width_of};
use super::vtables::ClassInfo;
use super::{Analysis, NameSource, Overlay, name_of, slot_name_of, striped};
use crate::program::Program;

/// What a mod SDK is made of: a program's classes, globals and functions.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Sdk {
    /// The image's file name, which a module-relative address names
    /// (`game.exe`).
    pub module: String,
    /// The preferred load base every relative address is measured from.
    pub image_base: u64,
    /// The pointer width in bytes, 4 or 8.
    pub word: u64,
    /// The classes, by name.
    pub classes: Vec<Class>,
    /// The globals, by address.
    pub globals: Vec<Global>,
    /// Thread-local singletons: TLS block offset and class, by offset.
    pub tls: Vec<(u64, String)>,
    /// The named functions: entry and name, by entry.
    pub functions: Vec<(u64, String)>,
}

impl Sdk {
    /// Returns an address relative to the image base.
    ///
    /// # Arguments
    ///
    /// * `va` - A virtual address in the image.
    #[must_use]
    pub fn rva(&self, va: u64) -> u64 {
        va.wrapping_sub(self.image_base)
    }

    /// Returns the class named `name`, if the SDK defines it.
    ///
    /// # Arguments
    ///
    /// * `name` - The class name as the program spells it.
    #[must_use]
    pub fn class(&self, name: &str) -> Option<&Class> {
        self.classes
            .binary_search_by(|c| c.name.as_str().cmp(name))
            .ok()
            .and_then(|i| self.classes.get(i))
    }
}

/// How much of a class's size is known.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Size {
    /// The size a struct the overlay states gives, in bytes.
    Stated(u64),
    /// The end of the last field seen, in bytes: the class is at least
    /// this big and may be bigger.
    AtLeast(u64),
}

impl Size {
    /// Returns the size in bytes, a lower bound for [`Size::AtLeast`].
    #[must_use]
    pub fn bytes(self) -> u64 {
        match self {
            Size::Stated(n) | Size::AtLeast(n) => n,
        }
    }
}

/// One class: its layout and its virtual table.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Class {
    /// The name as the program spells it (`Demo::Player`).
    pub name: String,
    /// Its size.
    pub size: Size,
    /// The class whose constructor its constructor calls first, whose
    /// fields its own methods' accesses include.
    pub parent: Option<String>,
    /// The primary vtable's address, whose pointer sits at offset zero.
    pub vtable: Option<u64>,
    /// The vtable's slots in order: the entry each holds (`0` for a word the
    /// table's reading skipped) and its name.
    pub slots: Vec<(u64, String)>,
    /// The fields by offset, none overlapping, the vtable pointer included.
    pub fields: Vec<Field>,
    /// What the layout left out and why, one line each.
    pub notes: Vec<String>,
}

/// What a field's type is.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Ty {
    /// An integer of 1, 2, 4 or 8 bytes.
    Int {
        /// Width in bytes.
        bytes: u8,
        /// Whether the overlay states it signed; a recovered field is not.
        signed: bool,
    },
    /// A 4-byte float.
    Float,
    /// An 8-byte float.
    Double,
    /// A pointer, to the named class or struct when one is known.
    Ptr(Option<String>),
    /// The pointer to the class's own vtable.
    VTable,
    /// Bytes no scalar spells (an array, an embedded struct): the width
    /// and the type the overlay states.
    Bytes(u64, String),
}

impl Ty {
    /// Returns the width in bytes.
    ///
    /// # Arguments
    ///
    /// * `word` - The pointer width in bytes.
    #[must_use]
    pub fn width(&self, word: u64) -> u64 {
        match self {
            Ty::Int { bytes, .. } => u64::from(*bytes),
            Ty::Float => 4,
            Ty::Double => 8,
            Ty::Ptr(_) | Ty::VTable => word,
            Ty::Bytes(n, _) => *n,
        }
    }
}

/// How a field or global came to be known.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Evidence {
    /// A user type the overlay states, or the vtable pointer RTTI places.
    Stated,
    /// Accessed at one width by the class's methods.
    Seen {
        /// Loads.
        reads: usize,
        /// Stores.
        writes: usize,
        /// Methods touching it.
        methods: usize,
    },
    /// Recovered, with a reason to doubt its type or extent.
    Unsure(String),
}

impl std::fmt::Display for Evidence {
    /// Writes the evidence as a renderer's comment says it.
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Evidence::Stated => f.write_str("stated"),
            Evidence::Seen {
                reads,
                writes,
                methods,
            } => write!(
                f,
                "recovered: reads {reads}, writes {writes}, methods {methods}"
            ),
            Evidence::Unsure(why) => write!(f, "unsure: {why}"),
        }
    }
}

/// One field of a class.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Field {
    /// Offset from the object's start, in bytes.
    pub off: u64,
    /// The member name the program or the overlay gives, else `f_<offset>`.
    pub name: String,
    /// Its type.
    pub ty: Ty,
    /// How it came to be known.
    pub evidence: Evidence,
}

/// One global variable.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Global {
    /// Its virtual address.
    pub va: u64,
    /// Its name: the overlay's, else `g_<class>` for a singleton slot.
    pub name: String,
    /// Its type.
    pub ty: Ty,
    /// How it came to be known.
    pub evidence: Evidence,
}

/// Gathers the SDK of a program: its classes, globals and functions.
///
/// The layouts of the classes are recovered across the cores; under a
/// raised [`crate::cancel::Cancel`] the decompiles they read stop early,
/// so a caller holding one checks it before writing what this returns.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Its analysis.
/// * `overlay` - User names and types, which win over what is recovered.
///
/// # Returns
///
/// The SDK, the same for the same inputs.
#[must_use]
pub fn build(program: &Program, analysis: &Analysis, overlay: &Overlay) -> Sdk {
    let word: u64 = if program.is_64 { 8 } else { 4 };
    let names: Vec<&String> = analysis
        .classes
        .by_name
        .keys()
        .chain(analysis.classes.vtables.values())
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect();
    let layouts = striped(&names, |name| {
        class_layout(program, analysis, overlay, name).filter(|l| l.name == **name)
    });
    let mut classes: BTreeMap<String, Class> = BTreeMap::new();
    for (name, layout) in names.iter().zip(layouts) {
        let info = analysis.classes.by_name.get(*name);
        let class = recovered(
            name,
            layout.flatten().as_ref(),
            info,
            analysis,
            overlay,
            word,
        );
        classes.insert((*name).clone(), class);
    }
    for (name, ty) in &overlay.types {
        let UserType::Struct(s) = ty else { continue };
        let stated = stated(name, s, &overlay.types, word);
        match classes.get_mut(name) {
            Some(c) => {
                let room = stated.size.bytes() >= word
                    && stated.fields.first().is_none_or(|f| f.off >= word);
                c.fields.retain(|f| room && f.ty == Ty::VTable);
                c.fields.extend(stated.fields);
                c.size = stated.size;
                c.notes = vec!["fields as the overlay states them".to_owned()];
            }
            None => {
                classes.insert(name.clone(), stated);
            }
        }
    }
    Sdk {
        module: file_name(program),
        image_base: program.image_base,
        word,
        classes: classes.into_values().collect(),
        globals: globals(analysis, overlay, word),
        tls: analysis
            .classes
            .tls_slots
            .iter()
            .map(|(off, c)| (*off, c.clone()))
            .collect(),
        functions: functions(analysis, overlay),
    }
}

/// Returns the image's file name, `module` when the path has none.
///
/// # Arguments
///
/// * `program` - The loaded image.
fn file_name(program: &Program) -> String {
    program
        .path
        .file_name()
        .map_or_else(|| "module".to_owned(), |n| n.to_string_lossy().into_owned())
}

/// Returns a class as its methods use it.
///
/// # Arguments
///
/// * `name` - The class.
/// * `layout` - Its recovered layout, `None` when no method was found.
/// * `info` - What the vtable scan found: vtable, slots, parent.
/// * `analysis` - For the pointer fields' classes and the slots' names.
/// * `overlay` - User names.
/// * `word` - The pointer width in bytes.
#[must_use]
pub fn recovered(
    name: &str,
    layout: Option<&ClassLayout>,
    info: Option<&ClassInfo>,
    analysis: &Analysis,
    overlay: &Overlay,
    word: u64,
) -> Class {
    let vtable = info.and_then(|i| i.vtable);
    let mut fields = Vec::new();
    let mut notes = Vec::new();
    if vtable.is_some() {
        fields.push(Field {
            off: 0,
            name: "vftable".to_owned(),
            ty: Ty::VTable,
            evidence: Evidence::Stated,
        });
    }
    if let Some(layout) = layout {
        let (scalars, left_out) = super::apply::scalar_fields(layout);
        notes = left_out;
        if layout.sampled {
            notes.push(format!(
                "only the first {} methods were read",
                super::classes::METHODS_MAX
            ));
        }
        let start = if vtable.is_some() { word } else { 0 };
        for (off, field_name, ty) in scalars {
            if off < start {
                continue;
            }
            let Some(used) = layout.fields.get(&off) else {
                continue;
            };
            let key = (name.to_owned(), off);
            let ty = match (analysis.classes.field_hints.get(&key), scalar(&ty)) {
                (Some(class), Ty::Int { bytes, .. }) if u64::from(bytes) == word => {
                    Ty::Ptr(Some(class.clone()))
                }
                (_, ty) => ty,
            };
            fields.push(Field {
                off,
                name: field_name,
                ty,
                evidence: evidence_of(used, analysis.classes.field_types.get(&key)),
            });
        }
    }
    let end = fields
        .iter()
        .map(|f| f.off.saturating_add(f.ty.width(word)))
        .max()
        .unwrap_or(0);
    Class {
        name: name.to_owned(),
        size: Size::AtLeast(end),
        parent: info.and_then(|i| i.parent.clone()),
        vtable,
        slots: info.map_or_else(Vec::new, |i| {
            i.slots
                .iter()
                .map(|&s| (s, slot_name_of(analysis, overlay, s)))
                .collect()
        }),
        fields,
        notes,
    }
}

/// Returns how sure a recovered field is: unsure when its accesses differ
/// in width or an embedded object starts at it, else seen.
///
/// # Arguments
///
/// * `used` - The field's accesses.
/// * `embedded` - The type of the object embedded at its offset, if known.
fn evidence_of(used: &FieldUse, embedded: Option<&String>) -> Evidence {
    if used.widths.len() > 1 {
        let bits: Vec<String> = used.widths.iter().map(u8::to_string).collect();
        Evidence::Unsure(format!(
            "accessed {} bits wide; the widest is kept",
            bits.join(" and ")
        ))
    } else if let Some(t) = embedded {
        Evidence::Unsure(format!("a {t} (a base or member) starts here"))
    } else {
        Evidence::Seen {
            reads: used.reads,
            writes: used.writes,
            methods: used.methods.len(),
        }
    }
}

/// Returns a struct the overlay states as a class with no vtable.
///
/// # Arguments
///
/// * `name` - The struct's name.
/// * `s` - The struct.
/// * `known` - Every user type, which sizes an embedded one.
/// * `word` - The pointer width in bytes.
#[must_use]
pub fn stated(name: &str, s: &UserStruct, known: &BTreeMap<String, UserType>, word: u64) -> Class {
    let fields = s
        .fields
        .iter()
        .map(|(&off, f)| Field {
            off,
            name: f.name.clone(),
            ty: of_type(&f.ty, known, word),
            evidence: Evidence::Stated,
        })
        .collect();
    Class {
        name: name.to_owned(),
        size: Size::Stated(s.size),
        parent: None,
        vtable: None,
        slots: Vec::new(),
        fields,
        notes: Vec::new(),
    }
}

/// Returns the type of a scalar the language spells.
///
/// # Arguments
///
/// * `ty` - A scalar or pointer type.
fn scalar(ty: &TypeExpr) -> Ty {
    of_type(ty, &BTreeMap::new(), 8)
}

/// Returns the [`Ty`] a stated type has.
///
/// # Arguments
///
/// * `ty` - The type.
/// * `known` - Every user type, which sizes a named one.
/// * `word` - The pointer width in bytes.
fn of_type(ty: &TypeExpr, known: &BTreeMap<String, UserType>, word: u64) -> Ty {
    let int = |bytes, signed| Ty::Int { bytes, signed };
    let ty = unaliased(ty, known);
    match ty {
        TypeExpr::U8 | TypeExpr::Char => int(1, false),
        TypeExpr::U16 => int(2, false),
        TypeExpr::U32 => int(4, false),
        TypeExpr::U64 => int(8, false),
        TypeExpr::I8 => int(1, true),
        TypeExpr::I16 => int(2, true),
        TypeExpr::I32 => int(4, true),
        TypeExpr::I64 => int(8, true),
        TypeExpr::F32 => Ty::Float,
        TypeExpr::F64 => Ty::Double,
        TypeExpr::Ptr(inner) => Ty::Ptr(match unaliased(inner, known) {
            TypeExpr::Named(n) => Some(n.clone()),
            _ => None,
        }),
        TypeExpr::Named(n) if matches!(known.get(n), Some(UserType::Enum(_))) => int(
            u8::try_from(width_of(known, ty, word).unwrap_or(4)).unwrap_or(4),
            false,
        ),
        TypeExpr::Array(..) | TypeExpr::Named(_) => {
            Ty::Bytes(width_of(known, ty, word).unwrap_or(0), ty.spell())
        }
    }
}

/// Most aliases [`unaliased`] follows; a stated chain is validated not to
/// loop, and the bound keeps an unvalidated one from looping either.
const ALIAS_DEPTH: usize = 16;

/// Returns the type a named alias stands for, through every alias of the
/// chain; any other type is itself.
///
/// # Arguments
///
/// * `ty` - The type.
/// * `known` - Every user type.
fn unaliased<'t>(ty: &'t TypeExpr, known: &'t BTreeMap<String, UserType>) -> &'t TypeExpr {
    let mut ty = ty;
    for _ in 0..ALIAS_DEPTH {
        match ty {
            TypeExpr::Named(n) => match known.get(n) {
                Some(UserType::Alias(inner)) => ty = inner,
                _ => break,
            },
            _ => break,
        }
    }
    ty
}

/// Returns the globals: the singleton slots and what the overlay names
/// or types outside a function, by address.
///
/// # Arguments
///
/// * `analysis` - The singleton slots and the functions.
/// * `overlay` - User names and applied types.
/// * `word` - The pointer width in bytes.
fn globals(analysis: &Analysis, overlay: &Overlay, word: u64) -> Vec<Global> {
    let mut out: BTreeMap<u64, Global> = BTreeMap::new();
    for (&va, class) in &analysis.classes.global_hints {
        out.insert(
            va,
            Global {
                va,
                name: format!("g_{class}"),
                ty: Ty::Ptr(Some(class.clone())),
                evidence: Evidence::Unsure(format!(
                    "a constructor of {class} stores its object here"
                )),
            },
        );
    }
    for (&va, ty) in &overlay.applied {
        let ty = of_type(ty, &overlay.types, word);
        out.insert(
            va,
            Global {
                va,
                name: format!("g_{va:x}"),
                ty,
                evidence: Evidence::Stated,
            },
        );
    }
    for (&va, name) in &overlay.names {
        if analysis.function(va).is_some() {
            continue;
        }
        out.entry(va)
            .or_insert_with(|| Global {
                va,
                name: String::new(),
                ty: Ty::Int {
                    bytes: u8::try_from(word).unwrap_or(8),
                    signed: false,
                },
                evidence: Evidence::Unsure("named, but no type is stated".to_owned()),
            })
            .name
            .clone_from(name);
    }
    out.into_values().collect()
}

/// Returns the functions a mod calls or hooks: every one with a name that
/// is not a library's, a runtime helper's, a funclet's or an import's.
///
/// # Arguments
///
/// * `analysis` - The functions.
/// * `overlay` - User names, which count as names.
fn functions(analysis: &Analysis, overlay: &Overlay) -> Vec<(u64, String)> {
    analysis
        .functions
        .iter()
        .filter(|f| {
            let own = !matches!(
                f.name_source,
                NameSource::None | NameSource::Library | NameSource::Helper | NameSource::Funclet
            );
            f.thunk.is_none() && f.bound.is_none() && (own || overlay.names.contains_key(&f.entry))
        })
        .map(|f| (f.entry, name_of(analysis, overlay, f.entry)))
        .collect()
}

/// One stretch of a class's bytes, in offset order.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Part<'a> {
    /// Bytes no field covers: offset and length.
    Pad(u64, u64),
    /// A field.
    Field(&'a Field),
    /// A field of no width, or one starting inside the field before it,
    /// which no layout can place.
    Skipped(&'a Field),
}

/// Returns a class's bytes as fields and the padding between them, up to
/// its size.
///
/// # Arguments
///
/// * `class` - The class.
/// * `word` - The pointer width in bytes.
#[must_use]
pub fn parts(class: &Class, word: u64) -> Vec<Part<'_>> {
    let mut out = Vec::with_capacity(class.fields.len().saturating_mul(2));
    let mut at = 0u64;
    for f in &class.fields {
        let width = f.ty.width(word);
        if width == 0 || f.off < at {
            out.push(Part::Skipped(f));
            continue;
        }
        if f.off > at {
            out.push(Part::Pad(at, f.off - at));
        }
        out.push(Part::Field(f));
        at = f.off.saturating_add(width);
    }
    if class.size.bytes() > at {
        out.push(Part::Pad(at, class.size.bytes() - at));
    }
    out
}

/// Returns text safe inside an XML attribute or element.
///
/// # Arguments
///
/// * `text` - Any text; it stays whole, a module name in an address
///   included, but for a control character, which XML 1.0 cannot hold
///   and becomes `?`.
#[must_use]
pub fn xml(text: &str) -> String {
    let mut out = String::with_capacity(text.len());
    for c in text.chars() {
        match c {
            '&' => out.push_str("&amp;"),
            '<' => out.push_str("&lt;"),
            '>' => out.push_str("&gt;"),
            '"' => out.push_str("&quot;"),
            c if c.is_control() => out.push('?'),
            c => out.push(c),
        }
    }
    out
}

/// Returns a C++ identifier for a name.
///
/// Every run of other characters becomes one `_` and none is kept at
/// either end; a name left empty or starting with a digit gets `n_` in
/// front. A keyword, `NULL`, and an upper-case name ending `_MIN`, `_MAX`
/// or `_C` (the macros `<cstdint>` defines) get `_` behind, so no macro
/// the header includes can expand in a declaration.
///
/// # Arguments
///
/// * `name` - Any name (`Demo::Player`, `Util::Array<int>`).
#[must_use]
pub fn ident(name: &str) -> String {
    let mut out = String::with_capacity(name.len());
    for c in name.chars() {
        if c.is_ascii_alphanumeric() {
            out.push(c);
        } else if !out.ends_with('_') {
            out.push('_');
        }
    }
    let out = out.trim_matches('_');
    let upper = out
        .bytes()
        .all(|b| b.is_ascii_uppercase() || b.is_ascii_digit() || b == b'_');
    let macro_like =
        out == "NULL" || upper && ["_MIN", "_MAX", "_C"].iter().any(|s| out.ends_with(s));
    if out.is_empty() || out.starts_with(|c: char| c.is_ascii_digit()) {
        format!("n_{out}")
    } else if KEYWORDS.contains(&out) || macro_like {
        format!("{out}_")
    } else {
        out.to_owned()
    }
}

/// Returns `want`, or `want_2`, `want_3`, ... whichever `taken` lacks, and
/// takes it.
///
/// # Arguments
///
/// * `taken` - The names in use in one scope.
/// * `want` - The name wanted.
#[must_use]
pub fn unique(taken: &mut BTreeSet<String>, want: &str) -> String {
    let mut name = want.to_owned();
    let mut n = 2u64;
    while taken.contains(&name) {
        name = format!("{want}_{n}");
        n = n.saturating_add(1);
    }
    taken.insert(name.clone());
    name
}

/// The C++ keywords and alternative tokens no identifier may be.
const KEYWORDS: [&str; 97] = [
    "alignas",
    "alignof",
    "and",
    "and_eq",
    "asm",
    "auto",
    "bitand",
    "bitor",
    "bool",
    "break",
    "case",
    "catch",
    "char",
    "char8_t",
    "char16_t",
    "char32_t",
    "class",
    "compl",
    "concept",
    "const",
    "consteval",
    "constexpr",
    "constinit",
    "const_cast",
    "continue",
    "co_await",
    "co_return",
    "co_yield",
    "decltype",
    "default",
    "delete",
    "do",
    "double",
    "dynamic_cast",
    "else",
    "enum",
    "explicit",
    "export",
    "extern",
    "false",
    "float",
    "for",
    "friend",
    "goto",
    "if",
    "inline",
    "int",
    "long",
    "mutable",
    "namespace",
    "new",
    "noexcept",
    "not",
    "not_eq",
    "nullptr",
    "operator",
    "or",
    "or_eq",
    "private",
    "protected",
    "public",
    "register",
    "reinterpret_cast",
    "requires",
    "return",
    "short",
    "signed",
    "sizeof",
    "static",
    "static_assert",
    "static_cast",
    "struct",
    "switch",
    "template",
    "this",
    "thread_local",
    "throw",
    "true",
    "try",
    "typedef",
    "typeid",
    "typename",
    "union",
    "unsigned",
    "using",
    "virtual",
    "void",
    "volatile",
    "wchar_t",
    "while",
    "xor",
    "xor_eq",
    "offsetof",
    "pad",
    "int8_t",
    "uint8_t",
    "std",
];

#[cfg(test)]
mod tests;
