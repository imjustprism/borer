//! A project file's annotations: an overlay's names, comments, types and
//! statements as editable JSON keyed by address text, and the overlay they
//! read back into.
//!
//! A project file is edited by hand and passed around, so reading one is
//! reading hostile input: each table of a file is refused at the entry
//! past its cap as it is read ([`Capped`]), every table of a project
//! however it was built is counted before any entry is parsed
//! ([`Project::to_overlay`]), and every type and field is held to what the
//! annotating tools hold a statement to. Which binary a file was saved for
//! is judged here ([`Project::identify`]), and what of it a binary keeps
//! ([`admit`]); reading the file from disk and writing it are the
//! front end's.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;
use std::marker::PhantomData;
use std::path::{Component, Path, Prefix};
use std::sync::Arc;

use serde::de::{DeserializeSeed, Deserializer, Error as _, MapAccess, SeqAccess, Visitor};

use super::edit::{self, Edit, Force, Plan};
use super::protos::{PROTOTYPES_MAX, Proto, VARS_MAX, Var, VarKey};
use super::stated::Field;
use super::utypes::{
    APPLIED_MAX, ENUM_VALUES_MAX, FIELDS_MAX, TYPES_MAX, TypeExpr, UserField, UserType,
};
use super::{Analysis, EnumSource, Overlay, parse_addr, settable};
use crate::program::Program;
use crate::text::short_path;

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

/// Says that a table of a project file states one key twice.
///
/// # Arguments
///
/// * `key` - The repeated key.
fn duplicate_key<E: serde::de::Error, K: std::fmt::Display + ?Sized>(key: &K) -> E {
    E::custom(format!(
        "duplicate key {}",
        crate::text::quoted(&format!("{key}"))
    ))
}

/// Reads one table of a project file, refusing the file when a key is
/// stated twice or at the entry past the table's cap.
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
    K: serde::Deserialize<'de> + Ord + std::fmt::Display,
    V: serde::Deserialize<'de>,
{
    type Value = BTreeMap<K, V>;

    fn expecting(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "a map of at most {} {}", self.cap.2, self.cap.1)
    }

    fn visit_map<A: MapAccess<'de>>(self, mut map: A) -> Result<Self::Value, A::Error> {
        let mut out = BTreeMap::new();
        while let Some(key) = map.next_key::<K>()? {
            if out.contains_key(&key) {
                return Err(duplicate_key(&key));
            }
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
            out.insert(key, map.next_value::<V>()?);
        }
        Ok(out)
    }
}

impl<'de, K, V> DeserializeSeed<'de> for Capped<'_, K, V>
where
    K: serde::Deserialize<'de> + Ord + std::fmt::Display,
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
/// When the table is not a map of the entries it holds, states a key twice,
/// or passes its cap.
fn capped<'de, D, K, V>(d: D, cap: Cap) -> Result<BTreeMap<K, V>, D::Error>
where
    D: Deserializer<'de>,
    K: serde::Deserialize<'de> + Ord + std::fmt::Display,
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
            if out.contains_key(&key) {
                return Err(duplicate_key(key.as_str()));
            }
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
/// When the table is not a map of functions' variables, states a key twice,
/// or passes its cap.
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
/// When the table is not a map of classes' fields, states a key twice, or
/// passes a cap.
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

/// Refuses `count` entries of a table a project file holds at most `most`
/// of ([`held`]).
///
/// # Arguments
///
/// * `what` - The table, for the message (`names`).
/// * `count` - How many entries the table would hold.
/// * `most` - Its cap.
///
/// # Errors
///
/// When `count` passes `most`; the message names the table and the cap.
pub fn room(what: &str, count: usize, most: usize) -> Result<(), String> {
    if count <= most {
        return Ok(());
    }
    Err(format!(
        "the session would hold {count} {what}, past the {most} a project file holds, so nothing was applied"
    ))
}

/// Refuses an overlay whose tables count more entries than a project file
/// may state; the file's bytes are bounded where it is saved.
///
/// It counts what [`Project::counted`] counts of a file: the names and the
/// comments, the prototypes, the variables (a function stating none counts
/// as one), the types and their applications ([`super::utypes::counted`])
/// and the fields stated of each class ([`super::stated::crowded`]), so a
/// session held to it saves no project that [`Project::to_overlay`]
/// refuses for those counts.
///
/// # Arguments
///
/// * `o` - The overlay an edit would leave.
///
/// # Errors
///
/// When a table passes its cap; the message names the table and the cap.
pub fn held(o: &Overlay) -> Result<(), String> {
    room("names", o.names.len(), NAMES_MAX)?;
    room("comments", o.comments.len(), COMMENTS_MAX)?;
    room("prototypes", o.prototypes.len(), PROTOTYPES_MAX)?;
    let variables = o.vars.values().map(|table| table.len().max(1)).sum();
    room("variables", variables, VARS_MAX)?;
    super::utypes::counted(&o.types, o.applied.len()).map_err(|e| e.to_string())?;
    o.fields.iter().try_for_each(|(class, fields)| {
        super::stated::crowded(&crate::text::one_line(class), fields.len(), o.fields.len())
    })
}

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
/// address, or when the request's deadline passed.
fn keyed<'m, V>(
    table: &str,
    map: &'m BTreeMap<String, V>,
) -> Result<BTreeMap<u64, (&'m str, &'m V)>, String> {
    let mut out: BTreeMap<u64, (&str, &V)> = BTreeMap::new();
    let mut bad: Vec<String> = Vec::new();
    for (k, v) in map {
        crate::cancel::Cancel::whole(())?;
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
    /// escaped to a line refuse the file, as two keys of one address do. A
    /// function the file states no variable of is left out too, so the
    /// overlay counts its variables as a session does, one a variable.
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
            if table.is_empty() {
                continue;
            }
            let into = vars.entry(va).or_default();
            for (key, decl) in table {
                crate::cancel::Cancel::whole(())?;
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
        crate::cancel::Cancel::whole(o)
    }

    /// Checks that every table of the project stays within its entry cap,
    /// by the counts of its entries alone.
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
    pub fn counted(&self) -> Result<(), String> {
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

/// How a project file's binary compares with the loaded one
/// ([`Project::identify`]).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Identity {
    /// The project records the loaded binary's SHA-256.
    Same,
    /// The project records another SHA-256: another build or another file.
    Other,
    /// The project records no hash, and its path is the loaded binary's.
    PathOnly,
    /// The project records no hash, and its path is another file's.
    OtherPath,
}

/// Returns what identifies a binary in a project file: the SHA-256 of its
/// bytes, as lowercase hex.
///
/// # Arguments
///
/// * `bytes` - The whole file.
#[must_use]
pub fn identity(bytes: &[u8]) -> String {
    hex(crate::hashing::sha256(bytes))
}

/// Returns [`identity`] of a loaded binary, from the hash it keeps
/// ([`Program::digest`]), so the file is hashed once per program.
///
/// # Arguments
///
/// * `program` - The loaded binary.
#[must_use]
pub fn program_identity(program: &Program) -> String {
    hex(program.digest())
}

/// Spells a SHA-256 as lowercase hex.
///
/// # Arguments
///
/// * `digest` - The hash.
fn hex(digest: [u8; 32]) -> String {
    digest.iter().map(|b| format!("{b:02x}")).collect()
}

/// Explains why a hashless project saved for `saved` was refused on `loaded`.
///
/// # Arguments
///
/// * `saved` - Shortened path recorded in the project file.
/// * `loaded` - Shortened path of the loaded binary.
#[must_use]
pub fn other_path_verdict(saved: &str, loaded: &str) -> String {
    format!(
        "the project was saved for {saved}, but {loaded} is loaded, another path as text: the project records no sha-256, so its path names its binary; nothing was loaded"
    )
}

/// Largest project file read or written, in bytes ([`Project::to_json`]).
pub const PROJECT_MAX: u64 = 1 << 26;

/// Buffers serialized JSON up to `cap` bytes, either aborting once the
/// stream passes `cap` or counting the remaining bytes in constant space.
struct BoundedJson {
    /// Stored prefix of the stream, at most `cap` bytes.
    bytes: Vec<u8>,
    /// Total bytes written to the stream so far.
    total: u64,
    /// Maximum bytes `bytes` stores and allocates for.
    cap: usize,
    /// Whether passing `cap` returns an [`std::io::Error`] immediately.
    abort_past_cap: bool,
}

impl std::io::Write for BoundedJson {
    fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
        self.total = self.total.saturating_add(crate::num::from_usize(buf.len()));
        let keep = buf.len().min(self.cap.saturating_sub(self.bytes.len()));
        if keep > 0 {
            let needed = self.bytes.len().saturating_add(keep);
            if needed > self.bytes.capacity() {
                let target = self
                    .bytes
                    .capacity()
                    .saturating_mul(2)
                    .max(1024)
                    .min(self.cap)
                    .max(needed);
                self.bytes
                    .reserve_exact(target.saturating_sub(self.bytes.len()));
            }
            self.bytes.extend_from_slice(&buf[..keep]);
        }
        if self.abort_past_cap && self.total > crate::num::from_usize(self.cap) {
            return Err(std::io::Error::other("past PROJECT_MAX"));
        }
        Ok(buf.len())
    }

    fn flush(&mut self) -> std::io::Result<()> {
        Ok(())
    }
}

/// Leaves out of an overlay what `set_name`, `set_comment` and `set_type`
/// refuse of the loaded binary: an annotation at an address no section
/// holds, and a blank name or comment.
///
/// A project file is edited by hand and may be loaded into a binary other
/// than the one it was saved for; an annotation outside every section would
/// sit in the overlay and never be shown, and a blank name names nothing.
///
/// # Arguments
///
/// * `o` - The overlay a project file rebuilt; left holding what fits.
/// * `program` - The loaded binary.
///
/// # Returns
///
/// What was left out, one `name at 0x0 (in no section)` entry per
/// annotation: names, then comments, applied types, prototypes and
/// variables, each in address order.
pub fn keep_placeable(o: &mut Overlay, program: &Program) -> Vec<String> {
    let mut left_out: Vec<String> = Vec::new();
    let mut keep = |what: &str, va: u64, text: Option<&str>| {
        let why = if program.section_at(va).is_none() {
            "in no section"
        } else if text.is_some_and(|t| t.trim().is_empty()) {
            "blank"
        } else {
            return true;
        };
        left_out.push(format!("{what} at {va:#x} ({why})"));
        false
    };
    o.names.retain(|&va, n| keep("name", va, Some(n.as_str())));
    o.comments
        .retain(|&va, c| keep("comment", va, Some(c.as_str())));
    o.applied.retain(|&va, _| keep("type", va, None));
    o.prototypes.retain(|&va, _| keep("prototype", va, None));
    o.vars.retain(|&va, _| keep("variables", va, None));
    left_out
}

/// Returns a path's components as its text names them, read off no disk.
///
/// # Arguments
///
/// * `path` - The path.
///
/// # Returns
///
/// [`Path::components`] with `.` dropped and each `..` folded into the
/// component before it (at a root, into the root).
fn lexical(path: &Path) -> Vec<Component<'_>> {
    let mut out = Vec::new();
    for part in path.components() {
        match part {
            Component::CurDir => {}
            Component::ParentDir if matches!(out.last(), Some(Component::Normal(_))) => {
                out.pop();
            }
            Component::ParentDir if matches!(out.last(), Some(Component::RootDir)) => {}
            part => out.push(part),
        }
    }
    out
}

/// Tells whether two components name one thing as text: on Windows a name
/// in either ASCII case, and a drive in its long `\\?\` form, as Windows
/// reads them; elsewhere only the same text.
///
/// # Arguments
///
/// * `a` - A component of one path.
/// * `b` - The component of the other path at the same place.
fn alike(a: &Component<'_>, b: &Component<'_>) -> bool {
    let drive = |c: &Component<'_>| {
        if let Component::Prefix(p) = c
            && let Prefix::Disk(d) | Prefix::VerbatimDisk(d) = p.kind()
        {
            Some(d)
        } else {
            None
        }
    };
    match (a, b) {
        (Component::Normal(x), Component::Normal(y)) if cfg!(windows) => x.eq_ignore_ascii_case(y),
        _ if cfg!(windows) && drive(a).is_some() => drive(a) == drive(b),
        _ => a == b,
    }
}

impl Project {
    /// Judges whether the project was saved for the loaded binary.
    ///
    /// A project with its binary's SHA-256 belongs to the same bytes
    /// wherever they were loaded from, and to nothing else: a rebuild at
    /// the same path has other addresses, and took the old names silently
    /// while the path was the identity. One saved before projects recorded
    /// the hash is judged by its path ([`Project::is_for`]).
    ///
    /// # Arguments
    ///
    /// * `program` - The loaded binary.
    #[must_use]
    pub fn identify(&self, program: &Program) -> Identity {
        match &self.sha256 {
            Some(saved) if saved.eq_ignore_ascii_case(&program_identity(program)) => Identity::Same,
            Some(_) => Identity::Other,
            None if self.is_for(&program.path) => Identity::PathOnly,
            None => Identity::OtherPath,
        }
    }

    /// Tells whether the project was saved for the binary at `path`.
    ///
    /// A project with its binary's SHA-256 is matched by the hash alone
    /// ([`Project::identify`]); one without is matched here, by the path
    /// it records and the loaded one compared as text ([`lexical`],
    /// [`alike`]), never on disk, so a project file never makes borer open
    /// a path. On Windows a name matches in either ASCII case (even inside a
    /// case-sensitive directory, so `A.exe` matches `a.exe`) and a drive in
    /// its long `\\?\` form, as Windows ordinarily reads them. `..` folds as
    /// the text says on every system, though off Windows the kernel resolves
    /// it through a link. Two spellings only the disk shows to be one file (a
    /// link, an 8.3 name) are two paths, so [`admit`] refuses the project
    /// unless forced.
    ///
    /// # Arguments
    ///
    /// * `path` - Where the loaded binary was loaded from.
    #[must_use]
    pub fn is_for(&self, path: &Path) -> bool {
        let (saved, loaded) = (lexical(Path::new(&self.program)), lexical(path));
        saved.len() == loaded.len() && saved.iter().zip(&loaded).all(|(a, b)| alike(a, b))
    }

    /// Returns the file's text as pretty-printed JSON, or unindented when
    /// only the unindented form fits [`PROJECT_MAX`].
    ///
    /// # Returns
    ///
    /// The bytes a project file holds, at most [`PROJECT_MAX`].
    ///
    /// # Errors
    ///
    /// When a table passes [`Project::counted`], the file would be longer
    /// than [`PROJECT_MAX`] even unindented, which [`Project::from_json`]'s
    /// readers refuse, or serialization fails; each says nothing was written.
    pub fn to_json(&self) -> Result<Vec<u8>, String> {
        self.counted()
            .map_err(|why| format!("{why}; nothing was written"))?;
        let mut out = BoundedJson {
            bytes: Vec::new(),
            total: 0,
            cap: crate::num::saturating_usize(PROJECT_MAX),
            abort_past_cap: true,
        };
        if let Err(e) = serde_json::to_writer_pretty(&mut out, self) {
            if out.total <= PROJECT_MAX {
                return Err(format!("serialize: {e}"));
            }
            out.bytes.clear();
            out.total = 0;
            out.abort_past_cap = false;
            serde_json::to_writer(&mut out, self).map_err(|e| format!("serialize: {e}"))?;
        }
        if out.total > PROJECT_MAX {
            return Err(format!(
                "the project is {} bytes even unindented, past the {PROJECT_MAX} a project file holds, so nothing was written",
                out.total
            ));
        }
        Ok(out.bytes)
    }

    /// Parses a project file's bytes, each table held to its cap as it is
    /// read ([`Capped`]).
    ///
    /// It takes bytes, not text, so a file that is not UTF-8 is refused by
    /// the parser at the place it stops, as it always was.
    ///
    /// # Arguments
    ///
    /// * `json` - The file's bytes.
    ///
    /// # Errors
    ///
    /// When the bytes are not a valid project file: what the parser says of
    /// them, escaped to one line, since it quotes the file.
    pub fn from_json(json: &[u8]) -> Result<Project, String> {
        serde_json::from_slice(json).map_err(|e| crate::text::one_line(&e.to_string()))
    }
}

/// What [`admit`] made of a project file: the plan that puts its
/// annotations in place of the overlay's, and the answer that says it.
#[derive(Debug, Clone)]
pub struct Admitted {
    /// The plan, made over the overlay [`admit`] was given.
    pub plan: Plan,
    /// The edit the plan was made of, to plan again over an overlay a
    /// commit changed meanwhile ([`super::edit::Stale`]).
    pub edit: Edit,
    /// What was loaded and left out, and why, one line each.
    pub said: String,
}

/// Holds a project file to the loaded binary and plans putting what it
/// keeps in place of the overlay.
///
/// A project's addresses belong to the binary it was saved for, and
/// loading replaces every annotation, so a project saved for another
/// binary ([`Project::identify`]: by its SHA-256, or by its path in a
/// project older than the hash) is refused unless `force` says to admit it
/// anyway; a rebuild is pointed at `borer://carry`. Either way the
/// annotations the annotating tools would refuse of the loaded binary are
/// skipped and listed ([`keep_placeable`], [`settable::keep_settable`]),
/// and the fields the file states of classes are held to the binary's code
/// ([`super::stated::settled`]): those of a class the code contradicts, or that
/// no function belongs to, are skipped with the reason
/// ([`skipped_classes`]).
///
/// # Arguments
///
/// * `program` - The loaded binary.
/// * `analysis` - Hands over its analysis, which the stated fields are
///   held to; called once, only for a file this binary admits that states
///   fields of a class, so a caller that has not computed it yet need not
///   for any other; its refusal is the file's. The plan reads no code: a
///   project's edit only puts entries in place.
/// * `overlay` - The overlay the plan replaces.
/// * `file` - The project file.
/// * `force` - Whether a project saved for another binary is admitted.
///
/// # Returns
///
/// The plan and the answer ([`Admitted`]).
///
/// # Errors
///
/// When the file was saved for another binary and `force` is not set, it
/// states something the overlay cannot hold or a struct that does not lay
/// out with the binary's pointers ([`super::utypes::laid_at`]), `analysis`
/// refuses, or holding its class fields to the code is cut short by the
/// deadline.
pub fn admit(
    program: &Program,
    analysis: impl FnOnce() -> Result<Arc<Analysis>, String>,
    overlay: &Overlay,
    file: &Project,
    force: bool,
) -> anyhow::Result<Admitted> {
    /// Most left-out annotations the answer names before counting the rest.
    const LEFT_OUT_SHOWN: usize = 8;
    let identity = file.identify(program);
    let foreign = matches!(identity, Identity::Other | Identity::OtherPath);
    let saved_for = short_path(&file.program);
    let loaded_path = program.path.display().to_string();
    if foreign && !force {
        return Err(anyhow::Error::msg(refusal(program, file, &saved_for)));
    }
    let mut loaded = file.to_overlay().map_err(anyhow::Error::msg)?;
    let word: u64 = if program.is_64 { 8 } else { 4 };
    super::utypes::laid_at(&loaded.types, word).map_err(|e| {
        anyhow::anyhow!(
            "{e} with the {word}-byte pointers of {}; nothing was loaded",
            short_path(&loaded_path)
        )
    })?;
    let mut left_out = keep_placeable(&mut loaded, program);
    let placed = left_out.len();
    let room = LEFT_OUT_SHOWN.saturating_sub(placed);
    let skipped = placed.saturating_add(settable::keep_settable(&mut loaded, room, &mut left_out));
    let mut unsettled = super::stated::Unsettled::default();
    if !loaded.fields.is_empty() {
        let tabled = Overlay {
            enum_source: EnumSource::Binary,
            ..loaded.clone()
        };
        let analysis = analysis().map_err(anyhow::Error::msg)?;
        unsettled =
            super::stated::settled(program, &analysis, &tabled).map_err(anyhow::Error::msg)?;
    }
    let gone = unsettled.leave_out(&mut loaded);
    let stated = stated_counts(
        loaded.prototypes.len(),
        loaded.vars.values().map(BTreeMap::len).sum(),
        loaded.fields.values().map(BTreeMap::len).sum(),
    );
    let mut said = format!(
        "loaded {} names + {} comments + {} types + {} applied{stated}\n",
        loaded.names.len(),
        loaded.comments.len(),
        loaded.types.len(),
        loaded.applied.len()
    );
    if skipped > 0 {
        let shown = left_out.len().min(LEFT_OUT_SHOWN);
        let _ = writeln!(
            said,
            "# skipped {skipped} (showing {shown} of {skipped}): {}",
            left_out[..shown].join(", ")
        );
    }
    said.push_str(&skipped_classes(&unsettled, gone));
    if foreign {
        let _ = writeln!(
            said,
            "# forced: the project was saved for {saved_for}, so its names may sit on other code here"
        );
    }
    if matches!(identity, Identity::PathOnly | Identity::OtherPath) {
        said.push_str("# the project names its binary by path alone (saved before projects recorded its sha-256; matched ignoring ASCII case on Windows), so a rebuild or case twin at that path loads it too; save_project records the hash\n");
    }
    let put = Edit::Project(Box::new(loaded));
    let plan = edit::plan(
        program,
        &Analysis::default(),
        overlay,
        std::slice::from_ref(&put),
        Force::Refuse,
    )?;
    Ok(Admitted {
        plan,
        edit: put,
        said,
    })
}

/// Says why a project saved for another binary is refused, and what to do
/// instead ([`admit`]).
///
/// # Arguments
///
/// * `program` - The loaded binary.
/// * `file` - The project file.
/// * `saved_for` - The file's binary, shortened.
fn refusal(program: &Program, file: &Project, saved_for: &str) -> String {
    /// Hex digits of a SHA-256 a message shows.
    const HASH_SHOWN: usize = 12;
    let loaded_path = program.path.display().to_string();
    let short = |hash: &str| hash.chars().take(HASH_SHOWN).collect::<String>();
    match &file.sha256 {
        Some(saved) => format!(
            "the project was saved for another build (sha-256 {}... at {saved_for}), but {} is sha-256 {}...; nothing was loaded. Its addresses belong to that build: load it with this project, then borer://carry/{} carries the names to this one; or pass force=true to load the project anyway",
            short(&crate::text::one_line(saved)),
            short_path(&loaded_path),
            short(&program_identity(program)),
            short_path(&loaded_path.replace('\\', "/"))
        ),
        None => format!(
            "{}. Load that binary first, or pass force=true to load the project anyway and save_project to record the hash",
            other_path_verdict(saved_for, &short_path(&loaded_path))
        ),
    }
}

/// Words what a project states beyond its names, comments and types, for
/// the answers of saving and admitting one.
///
/// # Arguments
///
/// * `prototypes` - Prototypes stated.
/// * `vars` - Variables stated, over every function.
/// * `fields` - Fields stated, over every class.
///
/// # Returns
///
/// ` + 2 prototypes + 3 variables` when there is either, then
/// ` + 1 stated fields` when there are any; empty when there is none.
#[must_use]
pub fn stated_counts(prototypes: usize, vars: usize, fields: usize) -> String {
    let mut out = String::new();
    if prototypes + vars > 0 {
        let _ = write!(out, " + {prototypes} prototypes + {vars} variables");
    }
    if fields > 0 {
        let _ = write!(out, " + {fields} stated fields");
    }
    out
}

/// Words the stated fields an admitted project could not keep, a line per
/// reason, for [`admit`]'s answer and a command's stderr.
///
/// # Arguments
///
/// * `unsettled` - The classes whose fields were left out, and why.
/// * `gone` - How many fields went with the classes of no function, then
///   with the classes the code contradicts
///   ([`super::stated::Unsettled::leave_out`]).
///
/// # Returns
///
/// `# skipped 2 stated field(s) of 1 class(es) that name no class of this
/// binary (showing 1 of 1): Ghost`, and the like for the classes the code
/// contradicts, each with the refusal that names the field; at most eight
/// classes are named on a line and the rest counted. Where borer reads no
/// code of the binary, one line says the fields were kept unheld and why.
/// Empty when every class was held and kept its fields.
#[must_use]
pub fn skipped_classes(unsettled: &super::stated::Unsettled, gone: (usize, usize)) -> String {
    /// Most classes a line names before it counts the rest.
    const SHOWN: usize = 8;
    let refused: Vec<String> = unsettled
        .contradicted
        .iter()
        .map(|(class, why)| format!("{class} ({why})"))
        .collect();
    let mut out = String::new();
    for (fields, why, classes) in [
        (
            gone.0,
            "that name no class of this binary",
            &unsettled.absent,
        ),
        (gone.1, "the binary's code contradicts", &refused),
    ] {
        if !classes.is_empty() {
            let shown = classes.len().min(SHOWN);
            let _ = writeln!(
                out,
                "# skipped {fields} stated field(s) of {total} class(es) {why} (showing {shown} of {total}): {}",
                classes[..shown].join(", "),
                total = classes.len()
            );
        }
    }
    if let Some(why) = &unsettled.unread {
        let _ = writeln!(
            out,
            "# kept the stated fields as stated, held to no code: {why}"
        );
    }
    out
}

#[cfg(test)]
#[expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]
mod tests {
    use std::io::Write as _;

    use super::{BoundedJson, PROJECT_MAX, Project};
    use crate::cancel::Cancel;

    /// [`BoundedJson`] aborts past `cap` when asked, never allocates past
    /// `cap`, and counts the full stream length on reuse.
    #[test]
    fn bounded_json_caps_allocation_and_counts_exact_bytes() {
        let cap = crate::num::saturating_usize(PROJECT_MAX);
        let mut out = BoundedJson {
            bytes: Vec::new(),
            total: 0,
            cap,
            abort_past_cap: true,
        };
        let chunk = vec![b'x'; 4093];
        let mut written = 0usize;
        while written <= cap {
            let res = out.write(&chunk);
            written += chunk.len();
            if written > cap {
                assert!(res.is_err());
                break;
            }
            assert_eq!(res.ok(), Some(chunk.len()));
        }
        assert_eq!(out.bytes.len(), cap);
        assert_eq!(out.bytes.capacity(), cap);
        out.bytes.clear();
        out.total = 0;
        out.abort_past_cap = false;
        let big = vec![b'y'; 1 << 20];
        for _ in 0..100 {
            out.write_all(&big).expect("counting pass");
        }
        assert_eq!(out.total, 100 << 20);
        assert_eq!(out.bytes.len(), cap);
        assert_eq!(out.bytes.capacity(), cap);
    }

    /// Rebuilding an overlay under a raised [`Cancel`] refuses the result
    /// even when the project states only names and no types or fields.
    #[test]
    fn to_overlay_stops_when_the_deadline_passed() {
        let project = Project {
            names: [("0x1000".to_owned(), "main".to_owned())].into(),
            ..Project::default()
        };
        let flag = Cancel::new();
        flag.raise();
        let refused = flag
            .within(|| project.to_overlay())
            .expect_err("a cancelled load returned an overlay");
        assert!(refused.contains("deadline passed"), "{refused}");
    }

    /// Any table of a project file that repeats a JSON key is refused as it
    /// is read rather than letting the later value overwrite the earlier one.
    #[test]
    fn duplicate_keys_in_any_table_are_refused() {
        for tail in [
            r#""names":{"0x1000":"a","0x1000":"b"},"comments":{}"#,
            r#""names":{},"comments":{"0x1000":"a","0x1000":"b"}"#,
            r#""names":{},"comments":{},"types":{"T":{"Alias":"U8"},"T":{"Alias":"U16"}}"#,
            r#""names":{},"comments":{},"types":{"S":{"Struct":{"size":2,"fields":{"0":{"name":"a","ty":"U8"},"0":{"name":"b","ty":"U8"}}}}}"#,
            r#""names":{},"comments":{},"applied":{"0x1000":"u8","0x1000":"u16"}"#,
            r#""names":{},"comments":{},"prototypes":{"0x1000":"void (void)","0x1000":"int (void)"}"#,
            r#""names":{},"comments":{},"vars":{"0x1000":{"a1":"x"},"0x1000":{"a1":"y"}}"#,
            r#""names":{},"comments":{},"vars":{"0x1000":{"a1":"x","a1":"y"}}"#,
            r#""names":{},"comments":{},"fields":{"C":{"0x0":"a"},"C":{"0x0":"b"}}"#,
            r#""names":{},"comments":{},"fields":{"C":{"0x0":"a","0x0":"b"}}"#,
        ] {
            let json = format!(r#"{{"program":"b",{tail}}}"#);
            let refused = serde_json::from_str::<Project>(&json)
                .expect_err("a duplicate JSON key was accepted")
                .to_string();
            assert!(refused.contains("duplicate key"), "{tail}: {refused}");
        }
    }

    /// Repeated save and load cycles keep `names` and `comments` unchanged.
    ///
    /// Covers Windows backslashes, escaped control characters, chat turns and
    /// cut lines across consecutive [`Project::from_overlay`] and
    /// [`Project::to_overlay`] passes.
    #[test]
    fn repeated_overlay_cycles_preserve_names_and_comments_byte_for_byte() {
        let initial = Project {
            names: [
                ("0x1000".to_owned(), r"C:\temp\sample.exe".to_owned()),
                ("0x1010".to_owned(), "line\nfeed\x07bell".to_owned()),
            ]
            .into(),
            comments: [
                ("0x2000".to_owned(), r"path C:\dir\sub\file.bin".to_owned()),
                ("0x2010".to_owned(), "Human: \n".to_owned()),
                ("0x2020".to_owned(), format!("{}\n", "a".repeat(254))),
                ("0x2030".to_owned(), "<system-reminder>tag".to_owned()),
            ]
            .into(),
            ..Project::default()
        };
        let first = initial.to_overlay().expect("first load");
        let second = Project::from_overlay("b", None, &first)
            .to_overlay()
            .expect("second load");
        let third = Project::from_overlay("b", None, &second)
            .to_overlay()
            .expect("third load");
        assert_eq!(first.names, second.names);
        assert_eq!(first.comments, second.comments);
        assert_eq!(second.names, third.names);
        assert_eq!(second.comments, third.comments);
        assert_eq!(
            first.names.get(&0x1000).map(String::as_str),
            Some(r"C:\temp\sample.exe")
        );
    }

    /// A saved local deeper than [`crate::dwarf::FRAME_SPAN`] loads.
    ///
    /// A function with a large stack buffer names such a local; the
    /// project loads with its name and saves it back under the same key.
    #[test]
    fn a_saved_local_past_the_frame_span_loads() {
        use crate::analysis::protos::VarKey;
        let project = Project {
            vars: [(
                "0x1000".to_owned(),
                [("local_18000".to_owned(), "buf".to_owned())].into(),
            )]
            .into(),
            ..Project::default()
        };
        let overlay = project.to_overlay().expect("a deep local loads");
        let vars = overlay.vars.get(&0x1000).expect("the function's vars");
        assert_eq!(
            vars.get(&VarKey::Slot(-0x18000)).map(|v| v.name.as_str()),
            Some("buf")
        );
        let saved = Project::from_overlay("b", None, &overlay);
        assert_eq!(saved.vars, project.vars);
    }
}
