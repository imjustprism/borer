//! User-defined types: the structs, enums and typedefs an agent states,
//! applied to the globals it states them of, all carried by the overlay.
//!
//! The analysis derives layouts it can prove; the agent often knows one the
//! binary does not say (from documentation, a header, or reading the code).
//! A user type is that knowledge in a small language: the scalar widths, a
//! pointer to anything in the language, an array of anything in it, and
//! by-name references to other user types. Types are stated as structured
//! parameters and parsed here at the boundary, or as C declarations read
//! into the same types by [`super::cdecl`]; anything the language does not
//! spell is refused with a message naming it.

use std::collections::{BTreeMap, BTreeSet};

/// A type in the small language user types are stated in.
///
/// The scalars the decompiler already renders (`u8`..`u64`, `i8`..`i64`,
/// `f32`, `f64`, `char`), a pointer to any of those or to a named user
/// type, an array of any type, and a name standing for another user type.
/// A name is resolved against the overlay's types wherever a width or a
/// field is asked for, so redefining a type changes every reference at
/// once.
#[derive(Debug, Clone, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub enum TypeExpr {
    /// One unsigned byte.
    U8,
    /// One unsigned 16-bit word.
    U16,
    /// One unsigned 32-bit word.
    U32,
    /// One unsigned 64-bit word.
    U64,
    /// One signed byte.
    I8,
    /// One signed 16-bit word.
    I16,
    /// One signed 32-bit word.
    I32,
    /// One signed 64-bit word.
    I64,
    /// A single-precision float.
    F32,
    /// A double-precision float.
    F64,
    /// One byte of text, the width the emitter loads it at.
    Char,
    /// A pointer to a value of the inner type.
    Ptr(Box<TypeExpr>),
    /// That many values of the inner type back to back: at least one and
    /// at most [`ARRAY_LEN_MAX`].
    Array(Box<TypeExpr>, u64),
    /// A user type by its name, resolved where it is asked for.
    Named(String),
}

/// The scalar words of the language, with the widths in bytes.
const SCALARS: [(&str, u64); 11] = [
    ("u8", 1),
    ("u16", 2),
    ("u32", 4),
    ("u64", 8),
    ("i8", 1),
    ("i16", 2),
    ("i32", 4),
    ("i64", 8),
    ("f32", 4),
    ("f64", 8),
    ("char", 1),
];

/// Most pointers and arrays one type stacks over its base word.
///
/// A [`TypeExpr`] is a chain of boxes, one per pointer or array, and
/// spelling, hashing, comparing and dropping one walk the chain by
/// recursion; a cap where a type enters (from a tool's text or a project
/// file) keeps every one of those walks shallow. Sixteen is the depth the
/// debug-information reader follows a chain to, and far past any pointer a
/// program declares.
pub const PTR_DEPTH_MAX: usize = 16;

/// Most values one array type holds: sixteen million, far past any table a
/// program lays out statically, and small enough that no width computed
/// from one overflows.
pub const ARRAY_LEN_MAX: u64 = 1 << 24;

/// Tells whether `text` is an identifier a name may take: a letter or `_`
/// first, then letters, digits or `_`, at most [`crate::text::OUTSIDE_MAX`]
/// of them.
///
/// The bound is what keeps a type or field name in a message on one row:
/// every refusal that names one (`struct X states two fields named Y`,
/// `X resolves to no size`) echoed a 30 KB name whole.
///
/// # Arguments
///
/// * `text` - The candidate name.
pub(crate) fn is_ident(text: &str) -> bool {
    let mut chars = text.chars();
    text.len() <= crate::text::OUTSIDE_MAX
        && matches!(chars.next(), Some(c) if c.is_ascii_alphabetic() || c == '_')
        && chars.all(|c| c.is_ascii_alphanumeric() || c == '_')
}

/// Parses a type as the tools and the project file spell it.
///
/// One scalar (`u32`, `f64`, `char`) or one user type name (`Player`),
/// then pointers and arrays read left to right, each applying to all
/// before it: `Player *`, `Player*`, `Player **`, `char[16]` (sixteen
/// chars), `Rec[4]`, `Rec *[4]` (four pointers) and `char[16] *` (a
/// pointer to sixteen chars) all parse, as do `ptr Player` and `ptr ptr u8`
/// with the pointers before the word. Two bases (`u32 u64`), a stray `*`,
/// an empty text, a word that is not an identifier, an array of no values
/// or of more than [`ARRAY_LEN_MAX`], and more than [`PTR_DEPTH_MAX`]
/// pointers and arrays are refused.
///
/// # Arguments
///
/// * `text` - The type as written.
///
/// # Returns
///
/// The parsed type.
///
/// # Errors
///
/// When the text is empty, is not a type the language spells, or stacks
/// more pointers and arrays than [`PTR_DEPTH_MAX`]; the message names the
/// offending word so the caller can retry.
pub fn parse_type(text: &str) -> anyhow::Result<TypeExpr> {
    let one_word = || {
        anyhow::anyhow!(
            "a type is one word under pointers; {} is not one",
            crate::text::quoted(text)
        )
    };
    let mut base: Option<&str> = None;
    let mut ptrs: usize = 0;
    let mut suffixes: Vec<Option<u64>> = Vec::new();
    let mut rest = text.trim_start();
    while let Some(c) = rest.chars().next() {
        if c == '*' || c == '[' {
            if base.is_none() {
                return Err(one_word());
            }
            if c == '*' {
                suffixes.push(None);
                rest = rest.get(1..).unwrap_or("");
            } else {
                let (len, after) =
                    rest.get(1..).unwrap_or("").split_once(']').ok_or_else(|| {
                        anyhow::anyhow!(
                            "{} opens an array it does not close",
                            crate::text::quoted(text)
                        )
                    })?;
                suffixes.push(Some(array_len(len, text)?));
                rest = after;
            }
        } else {
            let end = rest
                .find(|c: char| c.is_whitespace() || c == '*' || c == '[')
                .unwrap_or(rest.len());
            let (word, after) = rest.split_at(end);
            rest = after;
            match word {
                "ptr" if base.is_none() => ptrs += 1,
                _ if base.is_some() => return Err(one_word()),
                _ => base = Some(word),
            }
        }
        rest = rest.trim_start();
    }
    let base = base.ok_or_else(one_word)?;
    let depth = suffixes.len().saturating_add(ptrs);
    if depth > PTR_DEPTH_MAX {
        let what = if suffixes.iter().any(Option::is_some) {
            "pointers and arrays"
        } else {
            "pointers"
        };
        return Err(anyhow::anyhow!(
            "the type stacks {depth} {what} over {}; {PTR_DEPTH_MAX} is the most",
            crate::text::quoted(base)
        ));
    }
    let ty = match SCALARS.iter().find(|(word, _)| base == *word) {
        Some((word, _)) => scalar(word),
        None => {
            if !is_ident(base) {
                return Err(anyhow::anyhow!(
                    "{} is not a type: use u8..u64, i8..i64, f32, f64, char, a pointer (`T *`, `ptr T`), an array (`T[4]`) or a name",
                    crate::text::quoted(base)
                ));
            }
            TypeExpr::Named(base.to_owned())
        }
    };
    let ty = suffixes.into_iter().fold(ty, |t, s| match s {
        None => TypeExpr::Ptr(Box::new(t)),
        Some(n) => TypeExpr::Array(Box::new(t), n),
    });
    Ok((0..ptrs).fold(ty, |t, _| TypeExpr::Ptr(Box::new(t))))
}

/// Reads an array's length as a type spells it: decimal, or hex after
/// `0x`.
///
/// # Arguments
///
/// * `len` - The text between the brackets.
/// * `text` - The whole type, for the message.
///
/// # Errors
///
/// When the text is no number, or the number is zero or past
/// [`ARRAY_LEN_MAX`].
pub(crate) fn array_len(len: &str, text: &str) -> anyhow::Result<u64> {
    let len = len.trim();
    len.strip_prefix("0x")
        .map_or_else(
            || len.parse::<u64>().ok(),
            |h| u64::from_str_radix(h, 16).ok(),
        )
        .filter(|n| (1..=ARRAY_LEN_MAX).contains(n))
        .ok_or_else(|| {
            anyhow::anyhow!(
                "array length {} in {} is not a count from 1 to {ARRAY_LEN_MAX:#x}",
                crate::text::quoted(len),
                crate::text::quoted(text)
            )
        })
}

/// The scalar a word of the language spells.
///
/// # Arguments
///
/// * `word` - One of the words in [`SCALARS`].
fn scalar(word: &str) -> TypeExpr {
    match word {
        "u8" => TypeExpr::U8,
        "u16" => TypeExpr::U16,
        "u32" => TypeExpr::U32,
        "u64" => TypeExpr::U64,
        "i8" => TypeExpr::I8,
        "i16" => TypeExpr::I16,
        "i32" => TypeExpr::I32,
        "i64" => TypeExpr::I64,
        "f32" => TypeExpr::F32,
        "char" => TypeExpr::Char,
        _ => TypeExpr::F64,
    }
}

impl TypeExpr {
    /// Spells the type as the tools and the project file write it.
    ///
    /// `parse_type` of the spelling is the type again, so a project saved
    /// and loaded states the same types.
    ///
    /// # Returns
    ///
    /// `u32`, `char`, `Player`, `Player *`, `char[16]`, `Rec *[4]`: stars,
    /// never the `ptr` word, so one form round-trips.
    #[must_use]
    pub fn spell(&self) -> String {
        let mut suffixes: Vec<Option<u64>> = Vec::new();
        let mut current = self;
        let base = loop {
            current = match current {
                Self::Ptr(inner) => {
                    suffixes.push(None);
                    inner
                }
                Self::Array(inner, n) => {
                    suffixes.push(Some(*n));
                    inner
                }
                Self::U8 => break "u8",
                Self::U16 => break "u16",
                Self::U32 => break "u32",
                Self::U64 => break "u64",
                Self::I8 => break "i8",
                Self::I16 => break "i16",
                Self::I32 => break "i32",
                Self::I64 => break "i64",
                Self::F32 => break "f32",
                Self::F64 => break "f64",
                Self::Char => break "char",
                Self::Named(n) => break n.as_str(),
            };
        };
        let mut out = base.to_owned();
        let mut star_run = false;
        for s in suffixes.iter().rev() {
            match s {
                None => out.push_str(if star_run { "*" } else { " *" }),
                Some(n) => out.push_str(&format!("[{n}]")),
            }
            star_run = s.is_none();
        }
        out
    }

    /// The C type the decompiler renders a load of this width as, when the
    /// type is a scalar or a pointer.
    ///
    /// # Arguments
    ///
    /// * `word` - The image's pointer width in bytes (4 or 8).
    ///
    /// # Returns
    ///
    /// The cast text inside `*(T*)`, or `None` for a named type, whose width
    /// the types it names say, and for an array, which no one load reads.
    #[must_use]
    pub fn c_name(&self, word: u64) -> Option<String> {
        Some(match self {
            Self::U8 | Self::Char => "uint8_t".to_owned(),
            Self::U16 => "uint16_t".to_owned(),
            Self::U32 => "uint32_t".to_owned(),
            Self::U64 => "uint64_t".to_owned(),
            Self::I8 => "int8_t".to_owned(),
            Self::I16 => "int16_t".to_owned(),
            Self::I32 => "int32_t".to_owned(),
            Self::I64 => "int64_t".to_owned(),
            Self::F32 => "float".to_owned(),
            Self::F64 => "double".to_owned(),
            Self::Ptr(_) => (if word == 4 { "uint32_t" } else { "uint64_t" }).to_owned(),
            Self::Named(_) | Self::Array(..) => return None,
        })
    }
}

/// One field of a user struct.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct UserField {
    /// The field's name, as the decompiler renders it (`v->name`).
    pub name: String,
    /// The field's type in the small language.
    pub ty: TypeExpr,
}

/// A struct an agent stated: its size and its fields by offset.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct UserStruct {
    /// The struct's size in bytes, at least the end of its last field.
    pub size: u64,
    /// The fields by their byte offsets, which do not overlap.
    pub fields: BTreeMap<u64, UserField>,
}

/// An enum an agent stated: named values of one integer width.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct UserEnum {
    /// The enum's width in bytes, always 4 or 8.
    pub size: u64,
    /// `(value, name)` pairs by ascending value, so listing and rendering
    /// are deterministic whatever order the values were stated in.
    pub values: Vec<(u64, String)>,
}

/// A user type: a struct, an enum, or a name for another type.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum UserType {
    /// A struct with fields at offsets.
    Struct(UserStruct),
    /// An enum whose compared constants render by their member names.
    Enum(UserEnum),
    /// A name standing for another type.
    Alias(TypeExpr),
}

impl UserType {
    /// The kind word a listing prints for the type.
    ///
    /// # Returns
    ///
    /// `struct`, `enum` or `typedef`.
    #[must_use]
    pub fn kind(&self) -> &'static str {
        match self {
            Self::Struct(_) => "struct",
            Self::Enum(_) => "enum",
            Self::Alias(_) => "typedef",
        }
    }
}

/// Most user types one overlay holds; a type per name is plenty for a
/// binary's worth of knowledge, and the cap keeps a hostile project file
/// from filling memory.
pub const TYPES_MAX: usize = 4096;

/// Most fields one user struct holds.
pub const FIELDS_MAX: usize = 256;

/// Most values one user enum holds.
pub const ENUM_VALUES_MAX: usize = 256;

/// Builds a struct type from its stated fields, refusing what could not be
/// rendered honestly.
///
/// The name must be an identifier that is not a word of the language; each
/// field name an identifier, unique in the struct; each field type one the
/// language spells whose named references resolve against `known` and the
/// struct's own name (a self-reference only under a pointer, which is the
/// only cycle that ends); and no two fields' bytes overlap. The size is
/// the stated one when it covers every field, else the end of the last
/// field.
///
/// # Arguments
///
/// * `name` - The struct's name.
/// * `size` - The stated size, when the agent stated one.
/// * `fields` - `(offset, field name, type)` per field, in any order.
/// * `known` - The types already defined, for named references.
/// * `word` - The image's pointer width in bytes (4 or 8).
///
/// # Returns
///
/// The built type.
///
/// # Errors
///
/// When a name, a field, a type reference or an overlap is refused; each
/// message names the offender so the caller can retry.
pub fn build_struct(
    name: &str,
    size: Option<u64>,
    fields: &[(u64, String, TypeExpr)],
    known: &BTreeMap<String, UserType>,
    word: u64,
) -> anyhow::Result<UserType> {
    check_type_name(name)?;
    if fields.len() > FIELDS_MAX {
        return Err(anyhow::anyhow!(
            "a struct holds at most {FIELDS_MAX} fields; {name} states {}",
            fields.len()
        ));
    }
    let mut by_offset: BTreeMap<u64, UserField> = BTreeMap::new();
    let mut names: BTreeSet<&str> = BTreeSet::new();
    for &(off, ref field_name, ref ty) in fields {
        if !is_ident(field_name) {
            return Err(anyhow::anyhow!(
                "field name {} is not an identifier",
                crate::text::quoted(field_name)
            ));
        }
        if !names.insert(field_name.as_str()) {
            return Err(anyhow::anyhow!(
                "struct {name} states two fields named {field_name}"
            ));
        }
        let width = named_width(known, ty, name, word).ok_or_else(|| {
            anyhow::anyhow!(
                "field {field_name}'s type {} resolves to no size",
                ty.spell()
            )
        })?;
        if off.checked_add(width).is_none() {
            return Err(anyhow::anyhow!(
                "field {field_name} at {off:#x} ends past every address"
            ));
        }
        if let Some((&prev, _)) = by_offset.range(..off).next_back() {
            let earlier = &by_offset[&prev];
            let earlier_width = named_width(known, &earlier.ty, name, word).unwrap_or(0);
            if prev.checked_add(earlier_width).is_some_and(|end| end > off) {
                return Err(anyhow::anyhow!(
                    "field {field_name} at {off:#x} overlaps {} at {prev:#x}",
                    earlier.name
                ));
            }
        }
        by_offset.insert(
            off,
            UserField {
                name: field_name.clone(),
                ty: ty.clone(),
            },
        );
    }
    let end = by_offset.range(..).next_back().map_or(0, |(&off, f)| {
        off.saturating_add(field_width(known, f, name, word))
    });
    let size = match size {
        Some(s) if s < end => {
            return Err(anyhow::anyhow!(
                "size {s:#x} does not cover the last field, which ends at {end:#x}"
            ));
        }
        Some(s) => s,
        None => end,
    };
    Ok(UserType::Struct(UserStruct {
        size,
        fields: by_offset,
    }))
}

/// Builds a name for another type.
///
/// # Arguments
///
/// * `name` - The alias's name.
/// * `ty` - The type it stands for; its named references must resolve
///   against `known` and the alias's own name.
/// * `known` - The types already defined.
/// * `word` - The image's pointer width in bytes (4 or 8).
///
/// # Returns
///
/// The built type.
///
/// # Errors
///
/// When the name or a type reference is refused.
pub fn build_alias(
    name: &str,
    ty: &TypeExpr,
    known: &BTreeMap<String, UserType>,
    word: u64,
) -> anyhow::Result<UserType> {
    check_type_name(name)?;
    named_width(known, ty, name, word)
        .ok_or_else(|| anyhow::anyhow!("{} resolves to no size", ty.spell()))?;
    Ok(UserType::Alias(ty.clone()))
}

/// Builds an enum type from its stated values, refusing what could not be
/// rendered honestly.
///
/// The name must be an identifier that is not a word of the language; the
/// width 4 or 8 bytes; each value name an identifier, unique in the enum;
/// each value one the width holds (a 4-byte enum holds no value past
/// `u32::MAX`); and every value named at most once, since a value under two
/// names would render as whichever the lookup met first. The values are
/// stored by ascending value whatever order they were stated in.
///
/// # Arguments
///
/// * `name` - The enum's name.
/// * `size` - The enum's width in bytes: 4 or 8.
/// * `values` - `(value, name)` pairs, in any order.
///
/// # Returns
///
/// The built type, its values sorted by value.
///
/// # Errors
///
/// When the name, the width, a value name or a value is refused; each
/// message names the offender so the caller can retry.
pub fn build_enum(name: &str, size: u64, values: &[(u64, String)]) -> anyhow::Result<UserType> {
    check_type_name(name)?;
    if !matches!(size, 4 | 8) {
        return Err(anyhow::anyhow!(
            "enum {name}'s width is {size} byte(s); an enum is 4 or 8 wide"
        ));
    }
    if values.is_empty() {
        return Err(anyhow::anyhow!(
            "enum {name} states no values; give them as name:value"
        ));
    }
    if values.len() > ENUM_VALUES_MAX {
        return Err(anyhow::anyhow!(
            "an enum holds at most {ENUM_VALUES_MAX} values; {name} states {}",
            values.len()
        ));
    }
    let mut names: BTreeSet<&str> = BTreeSet::new();
    for &(value, ref value_name) in values {
        if !is_ident(value_name) {
            return Err(anyhow::anyhow!(
                "value name {} is not an identifier",
                crate::text::quoted(value_name)
            ));
        }
        if !names.insert(value_name.as_str()) {
            return Err(anyhow::anyhow!(
                "enum {name} states two values named {value_name}"
            ));
        }
        let fits = if size == 4 {
            u32::try_from(value).is_ok()
        } else {
            true
        };
        if !fits {
            return Err(anyhow::anyhow!(
                "value {value_name} = {value:#x} does not fit a {size}-byte enum"
            ));
        }
    }
    let mut sorted: Vec<(u64, String)> = values.to_vec();
    sorted.sort_unstable_by_key(|&(value, _)| value);
    for pair in sorted.windows(2) {
        if pair[0].0 == pair[1].0 {
            return Err(anyhow::anyhow!(
                "enum {name} names value {} twice, as {} and {}",
                pair[0].0,
                pair[0].1,
                pair[1].1
            ));
        }
    }
    Ok(UserType::Enum(UserEnum {
        size,
        values: sorted,
    }))
}

/// Refuses a type name that cannot be stated or referenced.
///
/// # Arguments
///
/// * `name` - The candidate name.
///
/// # Errors
///
/// When the name is empty, not an identifier, or a word of the language.
pub(crate) fn check_type_name(name: &str) -> anyhow::Result<()> {
    if !is_ident(name) {
        return Err(anyhow::anyhow!(
            "type name {} is not an identifier",
            crate::text::quoted(name)
        ));
    }
    if SCALARS.iter().any(|(word, _)| name == *word) || name == "ptr" {
        return Err(anyhow::anyhow!(
            "type name {name} spells a type of the language; pick another"
        ));
    }
    Ok(())
}

/// The width in bytes of a type whose names resolve against `known` and
/// `self_name`.
///
/// A name is followed through aliases and into a struct's size; a chain
/// that loops, or a name neither table has, has no width. A self-reference
/// resolves only in a cycle a pointer broke, which [`TypeExpr::Ptr`] sizing
/// to the word without walking its inner type is what ends. An array is its
/// values' width times their count, which [`ARRAY_LEN_MAX`] keeps from
/// overflowing at any depth the language allows.
///
/// # Arguments
///
/// * `known` - The types defined.
/// * `ty` - The type to size.
/// * `self_name` - The type being defined, if any, whose own name counts
///   as reaching itself, which only a pointer out of makes finite.
/// * `word` - The image's pointer width in bytes (4 or 8).
///
/// # Returns
///
/// The width, or `None` when a name does not resolve or a chain loops.
pub fn named_width(
    known: &BTreeMap<String, UserType>,
    ty: &TypeExpr,
    self_name: &str,
    word: u64,
) -> Option<u64> {
    let mut seen: BTreeSet<&str> = BTreeSet::new();
    let mut count: u64 = 1;
    let mut current = ty;
    loop {
        current = match current {
            TypeExpr::Ptr(inner) => {
                return resolves(known, inner, self_name)
                    .then_some(word)?
                    .checked_mul(count);
            }
            TypeExpr::Array(inner, n) => {
                count = count.checked_mul(*n)?;
                inner
            }
            TypeExpr::Named(n) => {
                if n == self_name || !seen.insert(n.as_str()) {
                    return None;
                }
                match known.get(n)? {
                    UserType::Struct(s) => return s.size.checked_mul(count),
                    UserType::Enum(e) => return e.size.checked_mul(count),
                    UserType::Alias(inner) => inner,
                }
            }
            leaf => return scalar_width(leaf)?.checked_mul(count),
        };
    }
}

/// Tells whether every name `ty` references resolves against `known` and
/// `self_name`, following aliases without looping.
///
/// A pointer's own width never depends on what it points at, but the name
/// it points at still has to be a type, so a typo'd target is refused
/// where the pointer is stated rather than silently naming no fields.
///
/// # Arguments
///
/// * `known` - The types defined.
/// * `ty` - The type whose references are checked.
/// * `self_name` - The type being defined, if any, whose own name counts
///   as known: a self-reference under a pointer is a linked structure.
///
/// # Returns
///
/// Whether the references resolve; a chain of aliases that loops does not.
fn resolves(known: &BTreeMap<String, UserType>, ty: &TypeExpr, self_name: &str) -> bool {
    let mut seen: BTreeSet<&str> = BTreeSet::new();
    let mut current = ty;
    loop {
        match current {
            TypeExpr::Ptr(inner) | TypeExpr::Array(inner, _) => current = inner.as_ref(),
            TypeExpr::Named(n) => {
                if n == self_name {
                    return true;
                }
                if !seen.insert(n.as_str()) {
                    return false;
                }
                match known.get(n) {
                    Some(UserType::Struct(_) | UserType::Enum(_)) => return true,
                    Some(UserType::Alias(inner)) => current = inner,
                    None => return false,
                }
            }
            _ => return true,
        }
    }
}

/// The width of a scalar type.
///
/// # Arguments
///
/// * `ty` - The scalar.
fn scalar_width(ty: &TypeExpr) -> Option<u64> {
    Some(match ty {
        TypeExpr::U8 | TypeExpr::I8 | TypeExpr::Char => 1,
        TypeExpr::U16 | TypeExpr::I16 => 2,
        TypeExpr::U32 | TypeExpr::I32 | TypeExpr::F32 => 4,
        TypeExpr::U64 | TypeExpr::I64 | TypeExpr::F64 => 8,
        TypeExpr::Ptr(_) | TypeExpr::Array(..) | TypeExpr::Named(_) => return None,
    })
}

/// The width of one field of a struct being built.
///
/// # Arguments
///
/// * `known` - The types defined so far.
/// * `field` - The field.
/// * `self_name` - The struct being built.
/// * `word` - The image's pointer width in bytes (4 or 8).
fn field_width(
    known: &BTreeMap<String, UserType>,
    field: &UserField,
    self_name: &str,
    word: u64,
) -> u64 {
    named_width(known, &field.ty, self_name, word).unwrap_or(0)
}

/// The width of a type against the image's pointer width.
///
/// # Arguments
///
/// * `known` - The types defined.
/// * `ty` - The type to size.
/// * `word` - The image's pointer width in bytes (4 or 8).
///
/// # Returns
///
/// The width in bytes, or `None` when a name does not resolve or a chain
/// loops.
#[must_use]
pub fn width_of(known: &BTreeMap<String, UserType>, ty: &TypeExpr, word: u64) -> Option<u64> {
    named_width(known, ty, "", word)
}

/// The struct a type points at, through pointers and aliases.
///
/// # Arguments
///
/// * `known` - The types defined.
/// * `ty` - The type; `Player *`, `Handle` (an alias of `Player *`) and
///   `Player` itself all reach `Player`'s fields.
///
/// # Returns
///
/// The struct, or `None` when the type is not a struct or a pointer to
/// one, or a chain of aliases loops.
#[must_use]
pub fn pointee_struct<'t>(
    known: &'t BTreeMap<String, UserType>,
    ty: &TypeExpr,
) -> Option<&'t UserStruct> {
    let mut seen: BTreeSet<&str> = BTreeSet::new();
    let mut current = ty;
    loop {
        match current {
            TypeExpr::Ptr(inner) => current = inner.as_ref(),
            TypeExpr::Named(n) => {
                if !seen.insert(n.as_str()) {
                    return None;
                }
                match known.get(n) {
                    Some(UserType::Struct(s)) => return Some(s),
                    Some(UserType::Enum(_)) => return None,
                    Some(UserType::Alias(inner)) => current = inner,
                    None => return None,
                }
            }
            _ => return None,
        }
    }
}

/// The enum a type names, through aliases.
///
/// # Arguments
///
/// * `known` - The types defined.
/// * `ty` - The type; `State`, and `Mode` (an alias of `State`) both reach
///   `State`'s values. A pointer never does: it is compared as an address,
///   not as one of the enum's values.
///
/// # Returns
///
/// The enum, or `None` when the type is not a name, names no type, or a
/// chain of aliases loops.
#[must_use]
pub fn named_enum<'t>(
    known: &'t BTreeMap<String, UserType>,
    ty: &TypeExpr,
) -> Option<&'t UserEnum> {
    let mut seen: BTreeSet<&str> = BTreeSet::new();
    let mut current = ty;
    loop {
        let TypeExpr::Named(n) = current else {
            return None;
        };
        if !seen.insert(n.as_str()) {
            return None;
        }
        match known.get(n)? {
            UserType::Enum(e) => return Some(e),
            UserType::Alias(inner) => current = inner,
            UserType::Struct(_) => return None,
        }
    }
}

/// Checks a whole overlay's types and applications.
///
/// Every name a type or an application references must be defined, no
/// chain of aliases may loop, and no type may stack more pointers than
/// [`PTR_DEPTH_MAX`]; a project file is edited by hand and passed around,
/// so this is where garbage in it is refused rather than silently dropping
/// a rendering.
///
/// # Arguments
///
/// * `types` - The defined types.
/// * `applied` - The applications, by address.
///
/// # Errors
///
/// When a reference is undefined, a chain loops or a type is too deep; the
/// message names the type and the name that failed.
pub fn validate(
    types: &BTreeMap<String, UserType>,
    applied: &BTreeMap<u64, TypeExpr>,
) -> anyhow::Result<()> {
    if types.len() > TYPES_MAX {
        return Err(anyhow::anyhow!(
            "the project states {} types; {TYPES_MAX} is the most",
            types.len()
        ));
    }
    for (name, ty) in types {
        match ty {
            UserType::Struct(s) => {
                if s.fields.len() > FIELDS_MAX {
                    return Err(anyhow::anyhow!(
                        "struct {name} states {} fields; {FIELDS_MAX} is the most",
                        s.fields.len()
                    ));
                }
                for (off, f) in &s.fields {
                    if !is_ident(&f.name) {
                        return Err(anyhow::anyhow!(
                            "field name {} is not an identifier",
                            crate::text::quoted(&f.name)
                        ));
                    }
                    check_depth(&f.ty, &format!("field {} at {off:#x}", f.name))?;
                    if width_of(types, &f.ty, 8).is_none() {
                        return Err(anyhow::anyhow!(
                            "field {} at {off:#x} has type {}, which resolves to no size",
                            f.name,
                            f.ty.spell()
                        ));
                    }
                }
            }
            UserType::Enum(e) => {
                if !matches!(e.size, 4 | 8) {
                    return Err(anyhow::anyhow!(
                        "enum {name}'s width is {} byte(s); an enum is 4 or 8 wide",
                        e.size
                    ));
                }
                if e.values.len() > ENUM_VALUES_MAX {
                    return Err(anyhow::anyhow!(
                        "enum {name} states {} values; {ENUM_VALUES_MAX} is the most",
                        e.values.len()
                    ));
                }
                let mut names: BTreeSet<&str> = BTreeSet::new();
                for &(value, ref value_name) in &e.values {
                    if !is_ident(value_name) {
                        return Err(anyhow::anyhow!(
                            "value name {} is not an identifier",
                            crate::text::quoted(value_name)
                        ));
                    }
                    if !names.insert(value_name.as_str()) {
                        return Err(anyhow::anyhow!(
                            "enum {name} states two values named {value_name}"
                        ));
                    }
                    if e.size == 4 && u32::try_from(value).is_err() {
                        return Err(anyhow::anyhow!(
                            "value {value_name} = {value:#x} does not fit a 4-byte enum"
                        ));
                    }
                }
                for pair in e.values.windows(2) {
                    if pair[0].0 == pair[1].0 {
                        return Err(anyhow::anyhow!(
                            "enum {name} names value {} twice, as {} and {}",
                            pair[0].0,
                            pair[0].1,
                            pair[1].1
                        ));
                    }
                }
            }
            UserType::Alias(inner) => {
                check_depth(inner, &format!("typedef {name}"))?;
                if width_of(types, inner, 8).is_none() {
                    return Err(anyhow::anyhow!(
                        "typedef {name} is {}, which resolves to no size",
                        inner.spell()
                    ));
                }
            }
        }
    }
    for (addr, ty) in applied {
        check_depth(ty, &format!("the type applied at {addr:#x}"))?;
        if width_of(types, ty, 8).is_none() {
            return Err(anyhow::anyhow!(
                "the type applied at {addr:#x}, {}, resolves to no size",
                ty.spell()
            ));
        }
    }
    Ok(())
}

/// Refuses a type that stacks more pointers and arrays than
/// [`PTR_DEPTH_MAX`], or holds an array of a count [`parse_type`] refuses,
/// so a hand-edited project cannot state a type a tool call cannot.
///
/// # Arguments
///
/// * `ty` - The type.
/// * `what` - What the type is of, for the message (`typedef PS`).
///
/// # Errors
///
/// When the type is deeper than the cap or an array's count is zero or
/// past [`ARRAY_LEN_MAX`]; the message names `what`.
fn check_depth(ty: &TypeExpr, what: &str) -> anyhow::Result<()> {
    let mut depth = 0usize;
    let mut current = ty;
    loop {
        current = match current {
            TypeExpr::Ptr(inner) => inner,
            TypeExpr::Array(inner, n) => {
                if !(1..=ARRAY_LEN_MAX).contains(n) {
                    return Err(anyhow::anyhow!(
                        "{what} holds an array of {n}; an array holds 1 to {ARRAY_LEN_MAX:#x}"
                    ));
                }
                inner
            }
            TypeExpr::U8
            | TypeExpr::U16
            | TypeExpr::U32
            | TypeExpr::U64
            | TypeExpr::I8
            | TypeExpr::I16
            | TypeExpr::I32
            | TypeExpr::I64
            | TypeExpr::F32
            | TypeExpr::F64
            | TypeExpr::Char
            | TypeExpr::Named(_) => break,
        };
        depth += 1;
    }
    if depth > PTR_DEPTH_MAX {
        return Err(anyhow::anyhow!(
            "{what} stacks {depth} pointers; {PTR_DEPTH_MAX} is the most"
        ));
    }
    Ok(())
}

/// Most rows the `types` listing prints before the paging parameters cut
/// it; one overlay's types fit well under the cap every listing shares.
pub const TYPES_ROWS_MAX: usize = 500;

/// Lists the user types and where they are applied, as the `types` tools
/// print them.
///
/// One row per type, then one per application, then the stated prototypes
/// and variables the caller renders ([`crate::analysis::protos::rows`]): a
/// struct with its size and `off name type` per field, an enum with its
/// width and `name = value` per value, a typedef with its target, an
/// application with the address and the type. The filter matches the whole
/// row in any
/// case, so a type's name, a field's name and an application's address hex
/// all find it.
///
/// # Arguments
///
/// * `types` - The defined types.
/// * `applied` - The applications, by address.
/// * `stated` - The rows of the stated prototypes and variables.
/// * `filter` - Case-insensitive substring a row must contain.
/// * `offset` - Rows to skip first.
/// * `limit` - Most rows to show.
///
/// # Returns
///
/// The rows shown, the rows there were, and the table: a `# showing` line,
/// a `#` header line, then the rows.
#[must_use]
pub fn list_tsv(
    types: &BTreeMap<String, UserType>,
    applied: &BTreeMap<u64, TypeExpr>,
    stated: &[String],
    filter: Option<&str>,
    offset: usize,
    limit: usize,
) -> (usize, usize, String) {
    let mut rows: Vec<String> = Vec::new();
    for (name, ty) in types {
        match ty {
            UserType::Struct(s) => {
                let fields = s
                    .fields
                    .iter()
                    .map(|(off, f)| format!("{off:#x} {} {}", f.name, f.ty.spell()))
                    .collect::<Vec<_>>()
                    .join(", ");
                rows.push(format!("struct\t{name}\t{:#x}\t{fields}", s.size));
            }
            UserType::Enum(e) => {
                let values = e
                    .values
                    .iter()
                    .map(|(value, value_name)| format!("{value_name} = {value}"))
                    .collect::<Vec<_>>()
                    .join(", ");
                rows.push(format!("enum\t{name}\t{:#x}\t{values}", e.size));
            }
            UserType::Alias(inner) => {
                rows.push(format!("typedef\t{name}\t-\t{}", inner.spell()));
            }
        }
    }
    for (addr, ty) in applied {
        rows.push(format!("applied\t{addr:#x}\t-\t{}", ty.spell()));
    }
    rows.extend(stated.iter().cloned());
    if let Some(q) = filter {
        let q = q.to_lowercase();
        rows.retain(|r| r.to_lowercase().contains(q.as_str()));
    }
    let total = rows.len();
    let shown = total.saturating_sub(offset).min(limit);
    let mut out = format!(
        "# showing {shown} of {total} rows ({} type(s), {} applied)\n",
        types.len(),
        applied.len()
    );
    out.push_str("# kind\tname\tsize\tfields\n");
    for row in rows.iter().skip(offset).take(limit) {
        out.push_str(row);
        out.push('\n');
    }
    (shown, total, out)
}

#[cfg(test)]
mod tests {
    use super::{TypeExpr, build_struct, list_tsv, parse_type, pointee_struct, validate, width_of};
    use crate::analysis::Overlay;
    use std::collections::BTreeMap;

    /// The language parses every spelling of a type and spells one form
    /// back; two bases, a stray star and a word that is not an identifier
    /// are refused, naming the offender.
    #[test]
    #[expect(
        clippy::missing_panics_doc,
        reason = "assertions are the point of a test"
    )]
    fn the_type_language_parses_and_spells() {
        let player = || TypeExpr::Named("Player".to_owned());
        for (text, ty, spelled) in [
            ("u32", TypeExpr::U32, "u32"),
            ("f64", TypeExpr::F64, "f64"),
            ("char", TypeExpr::Char, "char"),
            (
                "Player **",
                TypeExpr::Ptr(Box::new(TypeExpr::Ptr(Box::new(player())))),
                "Player **",
            ),
            (
                "ptr ptr u8",
                TypeExpr::Ptr(Box::new(TypeExpr::Ptr(Box::new(TypeExpr::U8)))),
                "u8 **",
            ),
            ("Player*", TypeExpr::Ptr(Box::new(player())), "Player *"),
        ] {
            assert_eq!(
                parse_type(text).unwrap_or_else(|e| panic!("{text}: {e}")),
                ty
            );
            assert_eq!(ty.spell(), spelled, "{text}");
        }
        for bad in ["", "u32 u64", "* Player", "not-a-type!", "u32 * extra"] {
            assert!(parse_type(bad).is_err(), "{bad} parsed");
        }
    }

    /// Arrays parse, spell back and size as their values times their count.
    ///
    /// They read left to right with the pointers; an empty or oversized
    /// count, a bracket left open, and a loop of typedefs through arrays
    /// are refused rather than overflowing or recursing for ever.
    #[test]
    #[expect(
        clippy::missing_panics_doc,
        reason = "assertions are the point of a test"
    )]
    fn arrays_parse_spell_and_size() {
        let rec = || Box::new(TypeExpr::Named("Rec".to_owned()));
        for (text, ty, spelled) in [
            (
                "char[16]",
                TypeExpr::Array(Box::new(TypeExpr::Char), 16),
                "char[16]",
            ),
            (
                "Rec *[4]",
                TypeExpr::Array(Box::new(TypeExpr::Ptr(rec())), 4),
                "Rec *[4]",
            ),
            (
                "char[0x10]*",
                TypeExpr::Ptr(Box::new(TypeExpr::Array(Box::new(TypeExpr::Char), 16))),
                "char[16] *",
            ),
            (
                "u8 [2] [3]",
                TypeExpr::Array(Box::new(TypeExpr::Array(Box::new(TypeExpr::U8), 2)), 3),
                "u8[2][3]",
            ),
        ] {
            let parsed = parse_type(text).unwrap_or_else(|e| panic!("{text}: {e}"));
            assert_eq!(parsed, ty, "{text}");
            assert_eq!(parsed.spell(), spelled, "{text}");
            assert_eq!(parse_type(spelled).ok(), Some(ty), "{spelled}");
        }
        let known = BTreeMap::new();
        assert_eq!(
            width_of(&known, &parse_type("u32[3][2]").unwrap(), 8),
            Some(24)
        );
        assert_eq!(
            width_of(&known, &parse_type("u8 *[4]").unwrap(), 4),
            Some(16)
        );
        for bad in ["u8[0]", "u8[0xffffffffffff]", "u8[", "u8[x]", "[4]u8"] {
            assert!(parse_type(bad).is_err(), "{bad} parsed");
        }
        let huge = (0..super::PTR_DEPTH_MAX).fold(TypeExpr::U64, |t, _| {
            TypeExpr::Array(Box::new(t), super::ARRAY_LEN_MAX)
        });
        assert_eq!(width_of(&known, &huge, 8), None, "overflow sizes to none");
        let mut looped = BTreeMap::new();
        looped.insert(
            "A".to_owned(),
            super::UserType::Alias(parse_type("B[2]").unwrap()),
        );
        looped.insert(
            "B".to_owned(),
            super::UserType::Alias(parse_type("A[2]").unwrap()),
        );
        assert!(validate(&looped, &BTreeMap::new()).is_err());
        let mut empty = BTreeMap::new();
        empty.insert(
            "E".to_owned(),
            super::UserType::Alias(TypeExpr::Array(Box::new(TypeExpr::U8), 0)),
        );
        let err = validate(&empty, &BTreeMap::new()).expect_err("an empty array validated");
        assert!(err.to_string().contains("holds an array of 0"), "{err}");
    }

    /// A type deeper than [`super::PTR_DEPTH_MAX`] pointers is refused where
    /// it enters, from a tool's text and from a project's types alike.
    ///
    /// Twenty thousand stars once parsed into a chain of boxes whose
    /// recursive spelling and drop overflowed the stack, even on a dry run.
    #[test]
    #[expect(
        clippy::missing_panics_doc,
        reason = "assertions are the point of a test"
    )]
    fn a_type_deeper_than_the_cap_is_refused() {
        let max = super::PTR_DEPTH_MAX;
        let deepest = format!("u8 {}", "*".repeat(max));
        assert_eq!(
            parse_type(&deepest).map(|t| t.spell()).ok(),
            Some(deepest.clone())
        );
        let err = parse_type(&format!("u8 {}", "*".repeat(20_000)))
            .expect_err("twenty thousand pointers parsed");
        assert!(
            err.to_string().contains(&format!(
                "stacks 20000 pointers over 'u8'; {max} is the most"
            )),
            "{err}"
        );
        assert!(parse_type(&format!("{}u8", "ptr ".repeat(max + 1))).is_err());
        assert!(parse_type(&format!("u8 {}", "* ".repeat(max + 1))).is_err());
        let deep = (0..=max).fold(TypeExpr::U8, |t, _| TypeExpr::Ptr(Box::new(t)));
        let mut types = BTreeMap::new();
        types.insert("Deep".to_owned(), super::UserType::Alias(deep.clone()));
        let err = validate(&types, &BTreeMap::new()).expect_err("a deep typedef validated");
        assert!(err.to_string().contains("typedef Deep stacks"), "{err}");
        let mut applied = BTreeMap::new();
        applied.insert(0x3000, deep);
        assert!(validate(&BTreeMap::new(), &applied).is_err());
    }

    /// A struct builds with its fields by offset and its size covering
    /// them; overlapping fields, a stated size under the last field's end
    /// and unknown type references are refused.
    #[test]
    #[expect(
        clippy::missing_panics_doc,
        reason = "assertions are the point of a test"
    )]
    fn a_struct_builds_and_refuses_what_it_cannot_hold() {
        let fields = vec![
            (0x18, "hp".to_owned(), parse_type("u32").unwrap()),
            (0x1c, "mp".to_owned(), parse_type("u32").unwrap()),
            (0x20, "target".to_owned(), parse_type("Player *").unwrap()),
        ];
        let built = build_struct("Player", None, &fields, &BTreeMap::new(), 8)
            .unwrap_or_else(|e| panic!("{e}"));
        let super::UserType::Struct(s) = &built else {
            panic!("not a struct");
        };
        assert_eq!(s.size, 0x28);
        assert_eq!(s.fields.len(), 3);
        let overlap = vec![
            (0x0, "a".to_owned(), parse_type("u32").unwrap()),
            (0x2, "b".to_owned(), parse_type("u32").unwrap()),
        ];
        assert!(build_struct("S", None, &overlap, &BTreeMap::new(), 8).is_err());
        assert!(build_struct("S", Some(2), &fields, &BTreeMap::new(), 8).is_err());
        let unknown = vec![(0x0, "f".to_owned(), parse_type("Missing *").unwrap())];
        assert!(build_struct("S", None, &unknown, &BTreeMap::new(), 8).is_err());
        assert!(build_struct("u32", None, &fields, &BTreeMap::new(), 8).is_err());
    }

    /// A self-reference under a pointer sizes to the word and a pointer to
    /// an undefined name is refused; a chain of aliases that loops, which
    /// only a hand-edited project can state, is refused by validate.
    #[test]
    #[expect(
        clippy::missing_panics_doc,
        reason = "assertions are the point of a test"
    )]
    fn pointers_break_cycles_and_loops_are_refused() {
        let node = vec![(0x0, "next".to_owned(), parse_type("Node *").unwrap())];
        let node = build_struct("Node", None, &node, &BTreeMap::new(), 8)
            .unwrap_or_else(|e| panic!("{e}"));
        let mut known = BTreeMap::new();
        known.insert("Node".to_owned(), node);
        let mut looped = BTreeMap::new();
        looped.insert(
            "A".to_owned(),
            super::UserType::Alias(parse_type("B").unwrap()),
        );
        looped.insert(
            "B".to_owned(),
            super::UserType::Alias(parse_type("A").unwrap()),
        );
        assert!(validate(&looped, &BTreeMap::new()).is_err());
        let mut applied = BTreeMap::new();
        applied.insert(0x3000, parse_type("Node *").unwrap());
        assert!(validate(&known, &applied).is_ok());
        assert!(pointee_struct(&known, &parse_type("Node *").unwrap()).is_some());
        assert!(pointee_struct(&known, &parse_type("u32").unwrap()).is_none());
    }

    /// A stated overlay's fingerprint folds its types and applications.
    ///
    /// A decompilation memoized under one is never handed back under
    /// another; a struct's fields, an alias's target and an application
    /// each move it.
    #[test]
    #[expect(
        clippy::missing_panics_doc,
        reason = "assertions are the point of a test"
    )]
    fn an_overlay_with_types_has_its_own_fingerprint() {
        let fields = vec![
            (0x0, "x".to_owned(), parse_type("f32").unwrap()),
            (0x8, "name".to_owned(), parse_type("char").unwrap()),
        ];
        let mut o = Overlay::default();
        let vec =
            build_struct("Vec", Some(0x10), &fields, &o.types, 8).unwrap_or_else(|e| panic!("{e}"));
        o.types.insert("Vec".to_owned(), vec);
        o.applied.insert(0x3000, parse_type("Vec *").unwrap());
        let mut other = o.clone();
        assert_eq!(o.fingerprint(), other.fingerprint());
        other.applied.insert(0x3000, parse_type("u32").unwrap());
        assert_ne!(o.fingerprint(), other.fingerprint());
        other = o.clone();
        other.types.remove("Vec");
        assert_ne!(o.fingerprint(), other.fingerprint());
        assert_ne!(o.fingerprint(), Overlay::default().fingerprint());
    }

    /// An enum builds with its values by ascending value, and everything it
    /// cannot render honestly is refused, naming the offender.
    ///
    /// A value under two names, a name under two values, a value past the
    /// stated width, a width that is not 4 or 8, a name that is not an
    /// identifier and a statement of no values are all refused; an enum
    /// reached through an alias still sizes, and `validate` refuses a
    /// hand-edited enum a build would have refused.
    #[test]
    #[expect(
        clippy::missing_panics_doc,
        reason = "assertions are the point of a test"
    )]
    fn an_enum_builds_and_refuses_what_it_cannot_hold() {
        let stated = [(2u64, "Done".to_owned()), (0u64, "Idle".to_owned())];
        let built = super::build_enum("State", 4, &stated).unwrap_or_else(|e| panic!("{e}"));
        let super::UserType::Enum(e) = &built else {
            panic!("not an enum");
        };
        assert_eq!(
            e.values,
            vec![(0, "Idle".to_owned()), (2, "Done".to_owned())]
        );
        assert!(super::build_enum("State", 4, &[]).is_err());
        assert!(super::build_enum("State", 3, &stated).is_err());
        assert!(super::build_enum("u32", 4, &stated).is_err());
        assert!(super::build_enum("State", 4, &[(0, "a-b".to_owned())]).is_err());
        assert!(
            super::build_enum("State", 4, &[(0, "A".to_owned()), (0, "B".to_owned())]).is_err()
        );
        assert!(
            super::build_enum("State", 4, &[(0, "A".to_owned()), (1, "A".to_owned())]).is_err()
        );
        assert!(
            super::build_enum("State", 4, &[(u64::from(u32::MAX) + 1, "Big".to_owned())]).is_err()
        );
        assert_eq!(built.kind(), "enum");

        let mut known = BTreeMap::new();
        known.insert("State".to_owned(), built);
        known.insert(
            "Mode".to_owned(),
            super::UserType::Alias(parse_type("State").unwrap()),
        );
        known.insert(
            "S".to_owned(),
            super::UserType::Struct(super::UserStruct {
                size: 4,
                fields: [(
                    0u64,
                    super::UserField {
                        name: "mode".to_owned(),
                        ty: parse_type("Mode").unwrap(),
                    },
                )]
                .into_iter()
                .collect(),
            }),
        );
        assert_eq!(width_of(&known, &parse_type("Mode").unwrap(), 8), Some(4));
        assert_eq!(width_of(&known, &parse_type("S").unwrap(), 8), Some(4));
        assert_eq!(
            list_tsv(&known, &BTreeMap::new(), &[], None, 0, 10).2,
            "# showing 3 of 3 rows (3 type(s), 0 applied)\n\
             # kind\tname\tsize\tfields\n\
             typedef\tMode\t-\tState\n\
             struct\tS\t0x4\t0x0 mode Mode\n\
             enum\tState\t0x4\tIdle = 0, Done = 2\n"
        );
        let mut hostile = known.clone();
        hostile.insert(
            "Bad".to_owned(),
            super::UserType::Enum(super::UserEnum {
                size: 4,
                values: vec![(0, "A".to_owned()), (0, "B".to_owned())],
            }),
        );
        assert!(validate(&hostile, &BTreeMap::new()).is_err());
    }

    /// An overlay holding an enum has its own fingerprint, which a stated
    /// value moves.
    #[test]
    #[expect(
        clippy::missing_panics_doc,
        reason = "assertions are the point of a test"
    )]
    fn an_overlay_with_an_enum_has_its_own_fingerprint() {
        let stated = [(0u64, "Idle".to_owned()), (1u64, "Run".to_owned())];
        let mut o = Overlay::default();
        o.types.insert(
            "State".to_owned(),
            super::build_enum("State", 4, &stated).unwrap_or_else(|e| panic!("{e}")),
        );
        let mut other = o.clone();
        assert_eq!(o.fingerprint(), other.fingerprint());
        other.types.insert(
            "State".to_owned(),
            super::build_enum(
                "State",
                4,
                &[(0u64, "Idle".to_owned()), (2u64, "Run".to_owned())],
            )
            .unwrap_or_else(|e| panic!("{e}")),
        );
        assert_ne!(o.fingerprint(), other.fingerprint());
    }
}
