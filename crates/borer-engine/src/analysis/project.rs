//! A project file's annotations: an overlay's names, comments, types and
//! statements as editable JSON keyed by address text, and the overlay they
//! read back into.
//!
//! A project file is edited by hand and passed around, so reading one is
//! reading hostile input: each table of a file is refused at the entry
//! past its cap as it is read ([`Capped`]), every table of a project
//! however it was built is counted before any entry is parsed
//! ([`Project::to_overlay`]), and every type and field is held to what the
//! annotating tools hold a statement to. Reading the file from disk,
//! writing it, and judging which binary it was saved for are the server's.

use std::collections::{BTreeMap, BTreeSet};
use std::marker::PhantomData;

use serde::de::{DeserializeSeed, Deserializer, Error as _, MapAccess, SeqAccess, Visitor};

use super::protos::{PROTOTYPES_MAX, Proto, VARS_MAX, Var, VarKey};
use super::stated::Field;
use super::utypes::{
    APPLIED_MAX, ENUM_VALUES_MAX, FIELDS_MAX, TYPES_MAX, TypeExpr, UserField, UserType,
};
use super::{Overlay, parse_addr};

/// A saved annotation overlay: the binary it belongs to, its names,
/// comments and user-defined types, keyed by `0x`-hex address text where an
/// address keys them (editable by hand).
///
/// A key may also be decimal; one that is not an address refuses the file.
#[derive(Debug, Default, serde::Serialize, serde::Deserialize)]
pub struct Project {
    /// Path of the binary the annotations belong to, for the reader: the
    /// binary is identified by [`Project::sha256`] when the file has it.
    pub program: String,
    /// The binary's SHA-256, lowercase hex: what identifies it, so a copy
    /// at another path loads and a rebuild at the same path is refused.
    /// Absent in a project saved before projects recorded it, which is
    /// identified by its path alone.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub sha256: Option<String>,
    /// "0x..." address -> function name.
    #[serde(deserialize_with = "capped_names")]
    pub names: BTreeMap<String, String>,
    /// "0x..." address -> comment.
    #[serde(deserialize_with = "capped_comments")]
    pub comments: BTreeMap<String, String>,
    /// User-defined types by name: a struct's fields at their offsets, or a
    /// typedef's target, as [`Overlay::types`] holds them. Absent in a
    /// project older than user types, which loads as having none.
    #[serde(default, deserialize_with = "capped_types")]
    pub types: BTreeMap<String, UserType>,
    /// "0x..." address -> the type applied there, as its spelling
    /// (`Player *`, `u32`); parsed on load, where one that is not a type
    /// refuses the file.
    #[serde(default, deserialize_with = "capped_applied")]
    pub applied: BTreeMap<String, String>,
    /// "0x..." function entry -> the prototype stated for it, as C without
    /// the function's name (`int (Player *p)`); parsed on load, where one
    /// that does not parse refuses the file. Absent when none is stated.
    #[serde(
        default,
        skip_serializing_if = "BTreeMap::is_empty",
        deserialize_with = "capped_prototypes"
    )]
    pub prototypes: BTreeMap<String, String>,
    /// "0x..." function entry -> variable (`a1`, `local_58`, `sp+0x30`) ->
    /// its stated declaration (`wchar_t *path`, or a name alone); parsed on
    /// load like the prototypes. Absent when none is stated.
    #[serde(
        default,
        skip_serializing_if = "BTreeMap::is_empty",
        deserialize_with = "capped_vars"
    )]
    pub vars: BTreeMap<String, BTreeMap<String, String>>,
    /// Class -> "0x..." field offset -> the field stated there: its name,
    /// then a space and its type when one was stated (`m_count u32`);
    /// parsed and checked on load like the prototypes. Absent when none is
    /// stated.
    #[serde(
        default,
        skip_serializing_if = "BTreeMap::is_empty",
        deserialize_with = "capped_fields"
    )]
    pub fields: BTreeMap<String, BTreeMap<String, String>>,
}

/// What a table's cap says when a file passes it: the verb and the entries
/// (`states`, `names`) and the most the table holds.
type Cap = (&'static str, &'static str, usize);

/// Says that a table passed its cap as it was read, as
/// [`Project::counted`] says it of a whole table.
///
/// # Arguments
///
/// * `(verb, what, most)` - The table's cap.
fn passed<E: serde::de::Error>((verb, what, most): Cap) -> E {
    E::custom(format!(
        "the project {verb} {} {what}; {most} is the most",
        most.saturating_add(1)
    ))
}

/// Reads one table of a project file, refusing the file at the entry past
/// the table's cap.
///
/// serde builds a map an entry at a time, so a table counted only once it
/// was whole had cost every entry first: a 64 MiB file of four million
/// one-entry tables of variables held 2.7 GB before its count refused it.
struct Capped<'r, K, V> {
    /// The table's cap, for the message ([`passed`]).
    cap: Cap,
    /// Entries the table, or the tables sharing its cap, may still take.
    room: &'r mut usize,
    /// The class a table of stated fields is of, and how many classes the
    /// file has stated fields of so far, which its refusal names as
    /// [`super::stated::crowded`] does; `None` for any other table.
    class: Option<(&'r str, usize)>,
    /// The entries' keys and values.
    entries: PhantomData<(K, V)>,
}

impl<'de, K, V> Visitor<'de> for Capped<'_, K, V>
where
    K: serde::Deserialize<'de> + Ord,
    V: serde::Deserialize<'de>,
{
    type Value = BTreeMap<K, V>;

    fn expecting(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "a map of at most {} {}", self.cap.2, self.cap.1)
    }

    fn visit_map<A: MapAccess<'de>>(self, mut map: A) -> Result<Self::Value, A::Error> {
        let mut out = BTreeMap::new();
        while let Some((key, value)) = map.next_entry()? {
            *self.room = self.room.checked_sub(1).ok_or_else(|| match self.class {
                Some((class, classes)) => {
                    let fields = self.cap.2.saturating_add(1);
                    let class = crate::text::one_line(class);
                    A::Error::custom(
                        super::stated::crowded(&class, fields, classes)
                            .err()
                            .unwrap_or_default(),
                    )
                }
                None => passed::<A::Error>(self.cap),
            })?;
            out.insert(key, value);
        }
        Ok(out)
    }
}

impl<'de, K, V> DeserializeSeed<'de> for Capped<'_, K, V>
where
    K: serde::Deserialize<'de> + Ord,
    V: serde::Deserialize<'de>,
{
    type Value = BTreeMap<K, V>;

    fn deserialize<D: Deserializer<'de>>(self, d: D) -> Result<Self::Value, D::Error> {
        d.deserialize_map(self)
    }
}

/// Reads one table of a project file under its own cap ([`Capped`]).
///
/// # Arguments
///
/// * `d` - The table.
/// * `cap` - Its cap.
///
/// # Errors
///
/// When the table is not a map of the entries it holds, or passes its cap.
fn capped<'de, D, K, V>(d: D, cap: Cap) -> Result<BTreeMap<K, V>, D::Error>
where
    D: Deserializer<'de>,
    K: serde::Deserialize<'de> + Ord,
    V: serde::Deserialize<'de>,
{
    let mut room = cap.2;
    Capped {
        cap,
        room: &mut room,
        class: None,
        entries: PhantomData,
    }
    .deserialize(d)
}

/// Reads one list of a project file, refusing the file at the entry past
/// the list's cap, as [`Capped`] reads a table.
struct Listed<V> {
    /// The list's cap, for the message ([`passed`]).
    cap: Cap,
    /// The entries' type.
    entries: PhantomData<V>,
}

impl<'de, V: serde::Deserialize<'de>> Visitor<'de> for Listed<V> {
    type Value = Vec<V>;

    fn expecting(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "a list of at most {} {}", self.cap.2, self.cap.1)
    }

    fn visit_seq<A: SeqAccess<'de>>(self, mut seq: A) -> Result<Self::Value, A::Error> {
        let mut out = Vec::new();
        while let Some(value) = seq.next_element()? {
            if out.len() == self.cap.2 {
                return Err(passed(self.cap));
            }
            out.push(value);
        }
        Ok(out)
    }
}

/// Reads a struct's fields from a project file, at most [`FIELDS_MAX`]
/// ([`capped`]), so a struct stating millions is refused as it is read.
///
/// # Errors
///
/// As [`capped`].
pub(crate) fn capped_struct_fields<'de, D: Deserializer<'de>>(
    d: D,
) -> Result<BTreeMap<u64, UserField>, D::Error> {
    capped(d, ("states", "fields of one struct", FIELDS_MAX))
}

/// Reads an enum's values from a project file, at most
/// [`ENUM_VALUES_MAX`] ([`Listed`]), so an enum stating millions is
/// refused as it is read.
///
/// # Errors
///
/// When the list is not one of values, or passes its cap.
pub(crate) fn capped_enum_values<'de, D: Deserializer<'de>>(
    d: D,
) -> Result<Vec<(u64, String)>, D::Error> {
    d.deserialize_seq(Listed {
        cap: ("states", "values of one enum", ENUM_VALUES_MAX),
        entries: PhantomData,
    })
}

/// Reads [`Project::names`], at most [`NAMES_MAX`].
///
/// # Errors
///
/// As [`capped`].
fn capped_names<'de, D: Deserializer<'de>>(d: D) -> Result<BTreeMap<String, String>, D::Error> {
    capped(d, ("states", "names", NAMES_MAX))
}

/// Reads [`Project::comments`], at most [`COMMENTS_MAX`].
///
/// # Errors
///
/// As [`capped`].
fn capped_comments<'de, D: Deserializer<'de>>(d: D) -> Result<BTreeMap<String, String>, D::Error> {
    capped(d, ("states", "comments", COMMENTS_MAX))
}

/// Reads [`Project::types`], at most [`TYPES_MAX`].
///
/// # Errors
///
/// As [`capped`].
fn capped_types<'de, D: Deserializer<'de>>(d: D) -> Result<BTreeMap<String, UserType>, D::Error> {
    capped(d, ("states", "types", TYPES_MAX))
}

/// Reads [`Project::applied`], at most [`APPLIED_MAX`].
///
/// # Errors
///
/// As [`capped`].
fn capped_applied<'de, D: Deserializer<'de>>(d: D) -> Result<BTreeMap<String, String>, D::Error> {
    capped(d, ("applies", "types", APPLIED_MAX))
}

/// Reads [`Project::prototypes`], at most [`PROTOTYPES_MAX`].
///
/// # Errors
///
/// As [`capped`].
fn capped_prototypes<'de, D: Deserializer<'de>>(
    d: D,
) -> Result<BTreeMap<String, String>, D::Error> {
    capped(d, ("states", "prototypes", PROTOTYPES_MAX))
}

/// Reads a table of tables of a project file: each function's variables
/// under one cap for all of them, or each class's fields under a cap for
/// each class.
struct Tables {
    /// The outer table's cap.
    outer: Cap,
    /// The inner tables' cap: one for all of them, or each one's.
    inner: Cap,
    /// Whether the inner tables share their cap, one stating nothing
    /// taking an entry of it, as [`Project::counted`] counts a function
    /// stating no variable.
    shared: bool,
}

impl<'de> Visitor<'de> for Tables {
    type Value = BTreeMap<String, BTreeMap<String, String>>;

    fn expecting(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "a map of at most {} {}", self.outer.2, self.outer.1)
    }

    fn visit_map<A: MapAccess<'de>>(self, mut map: A) -> Result<Self::Value, A::Error> {
        let (mut outer, mut shared) = (self.outer.2, self.inner.2);
        let mut out = BTreeMap::new();
        while let Some(key) = map.next_key::<String>()? {
            outer = outer
                .checked_sub(1)
                .ok_or_else(|| passed::<A::Error>(self.outer))?;
            let mut own = self.inner.2;
            let (room, class) = if self.shared {
                (&mut shared, None)
            } else {
                (&mut own, Some((key.as_str(), out.len().saturating_add(1))))
            };
            let table: BTreeMap<String, String> = map.next_value_seed(Capped {
                cap: self.inner,
                room,
                class,
                entries: PhantomData,
            })?;
            if self.shared && table.is_empty() {
                shared = shared
                    .checked_sub(1)
                    .ok_or_else(|| passed::<A::Error>(self.inner))?;
            }
            out.insert(key, table);
        }
        Ok(out)
    }
}

/// Reads [`Project::vars`]: at most [`VARS_MAX`] variables in all, a
/// function stating none counted as one ([`Tables`]).
///
/// # Errors
///
/// When the table is not a map of functions' variables, or passes its cap.
fn capped_vars<'de, D: Deserializer<'de>>(
    d: D,
) -> Result<BTreeMap<String, BTreeMap<String, String>>, D::Error> {
    let cap = ("states", "variables", VARS_MAX);
    d.deserialize_map(Tables {
        outer: cap,
        inner: cap,
        shared: true,
    })
}

/// Reads [`Project::fields`]: at most [`TYPES_MAX`] classes, each stating
/// at most [`FIELDS_MAX`] fields ([`Tables`]).
///
/// # Errors
///
/// When the table is not a map of classes' fields, or passes a cap.
fn capped_fields<'de, D: Deserializer<'de>>(
    d: D,
) -> Result<BTreeMap<String, BTreeMap<String, String>>, D::Error> {
    d.deserialize_map(Tables {
        outer: ("states fields of", "classes", TYPES_MAX),
        inner: ("states", "fields of one class", FIELDS_MAX),
        shared: false,
    })
}

/// Keys annotations by `0x`-hex address text, the form the file holds.
///
/// # Arguments
///
/// * `map` - Annotations by address.
fn by_hex(map: &BTreeMap<u64, String>) -> BTreeMap<String, String> {
    map.iter()
        .map(|(k, v)| (format!("{k:#x}"), v.clone()))
        .collect()
}

/// Most keys a refusal of unreadable keys names before it counts the rest.
const BAD_KEYS_SHOWN: usize = 8;

/// Most names one project states: a name for every function and global of
/// a large binary, and few enough that the copy of the overlay each edit
/// keeps stays small.
pub const NAMES_MAX: usize = 1 << 18;

/// Most comments one project states, as many as it states names.
pub const COMMENTS_MAX: usize = 1 << 18;

/// Reads a table's address keys, refusing any key that is not an address.
///
/// A key reads as an address argument does ([`parse_addr`]): `0x`-hex as
/// [`by_hex`] writes it, plain digits as decimal, bare hex with a letter as
/// hex. A key that reads as none of those, or two keys that name one
/// address, refuse the file: mapping either to some address anyway would
/// put an annotation where nobody stated one.
///
/// # Arguments
///
/// * `table` - Which table the keys key (`names`), for the message.
/// * `map` - Entries by address text: annotations, or a function's
///   variables.
///
/// # Returns
///
/// Each entry's key text and value by the address the key names.
///
/// # Errors
///
/// Naming the keys that are not addresses, or the two keys that name one
/// address.
fn keyed<'m, V>(
    table: &str,
    map: &'m BTreeMap<String, V>,
) -> Result<BTreeMap<u64, (&'m str, &'m V)>, String> {
    let mut out: BTreeMap<u64, (&str, &V)> = BTreeMap::new();
    let mut bad: Vec<String> = Vec::new();
    for (k, v) in map {
        let Some(va) = parse_addr(k) else {
            bad.push(crate::text::quoted(k));
            continue;
        };
        if let Some((first, _)) = out.insert(va, (k, v)) {
            return Err(format!(
                "{table} keys {} and {} both name {va:#x}; keep one",
                crate::text::quoted(first),
                crate::text::quoted(k)
            ));
        }
    }
    if bad.is_empty() {
        return Ok(out);
    }
    let more = bad.len().saturating_sub(BAD_KEYS_SHOWN);
    let tail = match (bad.len(), more) {
        (1, _) => " is".to_owned(),
        (_, 0) => " are".to_owned(),
        (_, more) => format!(" and {more} more are"),
    };
    Err(format!(
        "{table} key{} {}{tail} not an address; a key is 0x-hex as save_project writes it, or decimal",
        if bad.len() == 1 { "" } else { "s" },
        bad[..bad.len().min(BAD_KEYS_SHOWN)].join(", "),
    ))
}

/// Keys annotations by address again ([`keyed`]), escaping their text.
///
/// A project file is edited and passed around like any other file, so the
/// text in it comes from outside and is escaped the way the names in a
/// binary are: the listings that print it are one record to a line.
///
/// # Arguments
///
/// * `table` - Which table it is (`names`, `comments`), for the message.
/// * `map` - Annotations by address text.
///
/// # Returns
///
/// The annotations by address.
///
/// # Errors
///
/// As [`keyed`].
fn by_address(
    table: &str,
    map: &BTreeMap<String, String>,
) -> Result<BTreeMap<u64, String>, String> {
    Ok(keyed(table, map)?
        .into_iter()
        .map(|(va, (_, v))| (va, crate::text::one_line(v)))
        .collect())
}

impl Project {
    /// Builds the file contents from an overlay.
    ///
    /// # Arguments
    ///
    /// * `program` - Path of the binary the annotations belong to.
    /// * `sha256` - The binary's SHA-256, lowercase hex; `None` leaves the
    ///   file identifying it by path, for a file that is only read back by
    ///   the session that wrote it.
    /// * `o` - The overlay.
    #[must_use]
    pub fn from_overlay(program: &str, sha256: Option<String>, o: &Overlay) -> Project {
        Project {
            program: program.to_owned(),
            sha256,
            names: by_hex(&o.names),
            comments: by_hex(&o.comments),
            types: BTreeMap::clone(&o.types),
            applied: o
                .applied
                .iter()
                .map(|(k, v)| (format!("{k:#x}"), v.spell()))
                .collect(),
            prototypes: o
                .prototypes
                .iter()
                .map(|(k, p)| (format!("{k:#x}"), p.spell()))
                .collect(),
            vars: o
                .vars
                .iter()
                .map(|(k, vars)| {
                    let vars = vars
                        .iter()
                        .map(|(key, var)| (key.spell_saved(), var.spell()))
                        .collect();
                    (format!("{k:#x}"), vars)
                })
                .collect(),
            fields: o
                .fields
                .iter()
                .map(|(class, fields)| {
                    let fields = fields
                        .iter()
                        .map(|(off, field)| (format!("{off:#x}"), field.spell()))
                        .collect();
                    (class.clone(), fields)
                })
                .collect(),
        }
    }

    /// Rebuilds the overlay.
    ///
    /// Every table is counted first ([`Project::counted`]), so a project
    /// stating millions of entries is refused before any is parsed. Every
    /// address key must read as an address and no two may name one
    /// ([`keyed`]), and the annotation text is escaped to one line
    /// ([`by_address`]); the applied types are parsed and the whole set of
    /// types checked ([`super::utypes::validate`]), so a hand-edited file
    /// that names a type nothing states, or states one in a form the
    /// language does not spell, is refused here with a message naming it
    /// rather than silently naming no fields. An enum's values are put in
    /// value order, as an overlay holds them
    /// ([`super::utypes::UserEnum::values`]), however the file lists them.
    /// The fields stated of classes are read by offset and checked the
    /// same way ([`super::stated::validate`]); a class the file states no
    /// field of is left out, and two keys that read as one class once
    /// escaped to a line refuse the file, as two keys of one address do.
    ///
    /// # Returns
    ///
    /// The overlay.
    ///
    /// # Errors
    ///
    /// When a table states more than an overlay holds, a key is not an
    /// address or two keys name one address or one class, an applied type,
    /// a prototype, a variable or a class's field does not parse, a defined
    /// type's or a field's references do not resolve, or the request's
    /// deadline passed.
    pub fn to_overlay(&self) -> Result<Overlay, String> {
        self.counted()?;
        let mut applied: BTreeMap<u64, TypeExpr> = BTreeMap::new();
        for (va, (_, v)) in keyed("applied", &self.applied)? {
            let ty = super::utypes::parse_type(v).map_err(|e| {
                format!(
                    "the type applied at {va:#x}, {}, {e}",
                    crate::text::quoted(v)
                )
            })?;
            applied.insert(va, ty);
        }
        let mut prototypes = BTreeMap::new();
        for (va, (_, text)) in keyed("prototypes", &self.prototypes)? {
            let proto =
                Proto::parse(text).map_err(|e| format!("the prototype stated at {va:#x}: {e}"))?;
            prototypes.insert(va, proto);
        }
        let mut vars: BTreeMap<u64, BTreeMap<VarKey, Var>> = BTreeMap::new();
        for (va, (_, table)) in keyed("vars", &self.vars)? {
            let into = vars.entry(va).or_default();
            for (key, decl) in table {
                let key = VarKey::parse_saved(key)
                    .map_err(|e| format!("a variable of the function at {va:#x}: {e}"))?;
                let var = Var::parse(decl)
                    .map_err(|e| format!("a variable of the function at {va:#x}: {e}"))?;
                if into.insert(key, var).is_some() {
                    return Err(format!(
                        "the function at {va:#x} states {} twice",
                        key.spell_saved()
                    ));
                }
            }
        }
        let mut fields: BTreeMap<String, BTreeMap<u64, Field>> = BTreeMap::new();
        let mut classes: BTreeSet<String> = BTreeSet::new();
        for (class, table) in &self.fields {
            let class = crate::text::one_line(class);
            if !classes.insert(class.clone()) {
                return Err(format!(
                    "fields names class {} under two keys; keep one",
                    crate::text::quoted(&class)
                ));
            }
            for (off, (_, text)) in keyed(&format!("fields of {class}"), table)? {
                let field = Field::parse(text)
                    .map_err(|e| format!("the field of {class} at {off:#x}: {e}"))?;
                fields.entry(class.clone()).or_default().insert(off, field);
            }
        }
        let mut types = self.types.clone();
        for ty in types.values_mut() {
            if let UserType::Enum(e) = ty {
                e.values.sort_by_key(|&(value, _)| value);
            }
        }
        let o = Overlay {
            names: by_address("names", &self.names)?.into(),
            comments: by_address("comments", &self.comments)?.into(),
            types: types.into(),
            applied: applied.into(),
            prototypes: prototypes.into(),
            vars: vars.into(),
            fields: fields.into(),
            ..Overlay::default()
        };
        super::utypes::validate(&o.types, &o.applied).map_err(|e| e.to_string())?;
        super::stated::validate(&o)?;
        Ok(o)
    }

    /// Refuses a file whose tables state more than an overlay holds, by
    /// their counts alone, before any entry is parsed or sized.
    ///
    /// The names and comments are counted, the types as an overlay's are
    /// ([`super::utypes::counted`]), then the prototypes, the variables,
    /// and each class's stated fields ([`super::stated::crowded`]). A count
    /// is of the entries the file holds, so it is never under what loads,
    /// and a function stating no variable counts as one.
    ///
    /// # Errors
    ///
    /// When a count passes its cap; the message names the table.
    fn counted(&self) -> Result<(), String> {
        if self.names.len() > NAMES_MAX || self.comments.len() > COMMENTS_MAX {
            return Err(format!(
                "the project states {} names and {} comments; {NAMES_MAX} and {COMMENTS_MAX} are the most",
                self.names.len(),
                self.comments.len()
            ));
        }
        super::utypes::counted(&self.types, self.applied.len()).map_err(|e| e.to_string())?;
        let held: usize = self.vars.values().map(|table| table.len().max(1)).sum();
        if self.prototypes.len() > PROTOTYPES_MAX || held > VARS_MAX {
            return Err(format!(
                "the project states {} prototypes and {held} variables; {PROTOTYPES_MAX} and {VARS_MAX} are the most",
                self.prototypes.len()
            ));
        }
        for (class, table) in &self.fields {
            let class = crate::text::one_line(class);
            super::stated::crowded(&class, table.len(), self.fields.len())?;
        }
        Ok(())
    }
}
