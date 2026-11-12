//! Project persistence: overlay annotations saved as an editable JSON file.

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Component, Path};

use borer_engine::analysis::Overlay;
use borer_engine::analysis::protos::{PROTOTYPES_MAX, Proto, VARS_MAX, Var, VarKey};
use borer_engine::analysis::stated::Field;
use borer_engine::analysis::utypes::UserType;
use borer_engine::program::Program;

/// A saved annotation overlay: the binary it belongs to, its names,
/// comments and user-defined types, keyed by `0x`-hex address text where an
/// address keys them (editable by hand).
///
/// A key may also be decimal; one that is not an address refuses the file.
#[derive(Debug, serde::Serialize, serde::Deserialize)]
pub struct ProjectFile {
    /// Path of the binary the annotations belong to, for the reader: the
    /// binary is identified by [`ProjectFile::sha256`] when the file has it.
    pub program: String,
    /// The binary's SHA-256, lowercase hex ([`identity`]): what identifies
    /// it, so a copy at another path loads and a rebuild at the same path
    /// is refused. Absent in a project saved before projects recorded it,
    /// which is identified by its path alone.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub sha256: Option<String>,
    /// "0x..." address -> function name.
    pub names: BTreeMap<String, String>,
    /// "0x..." address -> comment.
    pub comments: BTreeMap<String, String>,
    /// User-defined types by name: a struct's fields at their offsets, or a
    /// typedef's target, as [`Overlay::types`] holds them. Absent in a
    /// project older than user types, which loads as having none.
    #[serde(default)]
    pub types: BTreeMap<String, UserType>,
    /// "0x..." address -> the type applied there, as its spelling
    /// (`Player *`, `u32`); parsed on load, where one that is not a type
    /// refuses the file.
    #[serde(default)]
    pub applied: BTreeMap<String, String>,
    /// "0x..." function entry -> the prototype stated for it, as C without
    /// the function's name (`int (Player *p)`); parsed on load, where one
    /// that does not parse refuses the file. Absent when none is stated.
    #[serde(default, skip_serializing_if = "BTreeMap::is_empty")]
    pub prototypes: BTreeMap<String, String>,
    /// "0x..." function entry -> variable (`a1`, `local_58`, `sp+0x30`) ->
    /// its stated declaration (`wchar_t *path`, or a name alone); parsed on
    /// load like the prototypes. Absent when none is stated.
    #[serde(default, skip_serializing_if = "BTreeMap::is_empty")]
    pub vars: BTreeMap<String, BTreeMap<String, String>>,
    /// Class -> "0x..." field offset -> the field stated there: its name,
    /// then a space and its type when one was stated (`m_count u32`);
    /// parsed and checked on load like the prototypes. Absent when none is
    /// stated.
    #[serde(default, skip_serializing_if = "BTreeMap::is_empty")]
    pub fields: BTreeMap<String, BTreeMap<String, String>>,
}

/// How a project file's binary compares with the loaded one
/// ([`ProjectFile::identify`]).
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
    borer_engine::hashing::sha256(bytes)
        .iter()
        .map(|b| format!("{b:02x}"))
        .collect()
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

/// Largest project file read, in bytes: past any overlay the caps on names,
/// comments, types and prototypes let a session hold.
const PROJECT_MAX: u64 = 1 << 26;

/// Reads a table's address keys, refusing any key that is not an address.
///
/// A key reads as an address argument does
/// ([`borer_engine::analysis::parse_addr`]): `0x`-hex as [`by_hex`] writes
/// it, plain digits as decimal, bare hex with a letter as hex. A key that
/// reads as none of those, or two keys that name one address, refuse the
/// file: mapping either to some address anyway would put an annotation
/// where nobody stated one.
///
/// # Arguments
///
/// * `table` - Which table the keys key (`names`), for the message.
/// * `map` - Entries by address text.
///
/// # Returns
///
/// Each entry's key text and value by the address the key names.
///
/// # Errors
///
/// Naming the keys that are not addresses, or the two keys that name one
/// address.
fn keyed<'m>(
    table: &str,
    map: &'m BTreeMap<String, String>,
) -> Result<BTreeMap<u64, (&'m str, &'m str)>, String> {
    let mut out: BTreeMap<u64, (&str, &str)> = BTreeMap::new();
    let mut bad: Vec<String> = Vec::new();
    for (k, v) in map {
        let Some(va) = borer_engine::analysis::parse_addr(k) else {
            bad.push(borer_engine::text::quoted(k));
            continue;
        };
        if let Some((first, _)) = out.insert(va, (k, v)) {
            return Err(format!(
                "{table} keys {} and {} both name {va:#x}; keep one",
                borer_engine::text::quoted(first),
                borer_engine::text::quoted(k)
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
        .map(|(va, (_, v))| (va, borer_engine::text::one_line(v)))
        .collect())
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
/// component before it (at a root, into the root). Names keep their letter
/// case; only a drive letter compares in either case, as std parses it.
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

impl ProjectFile {
    /// Builds the file contents from an overlay.
    ///
    /// # Arguments
    ///
    /// * `program` - Path of the binary the annotations belong to.
    /// * `sha256` - The binary's [`identity`]; `None` leaves the file
    ///   identifying it by path, for a file that is only read back by the
    ///   session that wrote it.
    /// * `o` - The overlay.
    pub fn from_overlay(program: &str, sha256: Option<String>, o: &Overlay) -> ProjectFile {
        ProjectFile {
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
    /// Every table is counted first ([`ProjectFile::counted`]), so a file
    /// stating millions of entries is refused before any is read. Every
    /// address key must read as an address and no two may name one
    /// ([`keyed`]), and the annotation text is escaped to one line
    /// ([`by_address`]); the applied types are parsed and the whole set of
    /// types checked ([`borer_engine::analysis::utypes::validate`]), so a
    /// hand-edited file that names a type nothing states, or states one in
    /// a form the language does not spell, is refused here with a message
    /// naming it rather than silently naming no fields. The fields stated
    /// of classes are read by offset and checked the same way
    /// ([`borer_engine::analysis::stated::validate`]); a class the file
    /// states no field of is left out, and two keys that read as one class
    /// once escaped to a line refuse the file, as two keys of one address
    /// do.
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
        let mut applied: BTreeMap<u64, borer_engine::analysis::utypes::TypeExpr> = BTreeMap::new();
        for (va, (_, v)) in keyed("applied", &self.applied)? {
            let ty = borer_engine::analysis::utypes::parse_type(v).map_err(|e| {
                format!(
                    "the type applied at {va:#x}, {}, {e}",
                    borer_engine::text::quoted(v)
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
        for (k, table) in &self.vars {
            let va = borer_engine::analysis::parse_addr(k).ok_or_else(|| {
                format!(
                    "vars key {} is not an address; a key is 0x-hex as save_project writes it",
                    borer_engine::text::quoted(k)
                )
            })?;
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
            let class = borer_engine::text::one_line(class);
            if !classes.insert(class.clone()) {
                return Err(format!(
                    "fields names class {} under two keys; keep one",
                    borer_engine::text::quoted(&class)
                ));
            }
            for (off, (_, text)) in keyed(&format!("fields of {class}"), table)? {
                let field = Field::parse(text)
                    .map_err(|e| format!("the field of {class} at {off:#x}: {e}"))?;
                fields.entry(class.clone()).or_default().insert(off, field);
            }
        }
        let o = Overlay {
            names: by_address("names", &self.names)?.into(),
            comments: by_address("comments", &self.comments)?.into(),
            types: self.types.clone().into(),
            applied: applied.into(),
            prototypes: prototypes.into(),
            vars: vars.into(),
            fields: fields.into(),
            ..Overlay::default()
        };
        borer_engine::analysis::utypes::validate(&o.types, &o.applied)
            .map_err(|e| e.to_string())?;
        borer_engine::analysis::stated::validate(&o)?;
        Ok(o)
    }

    /// Refuses a file whose tables state more than an overlay holds, by
    /// their counts alone, before any entry is parsed or sized.
    ///
    /// The types are counted as an overlay's are
    /// ([`borer_engine::analysis::utypes::counted`]), then the prototypes,
    /// the variables, and each class's stated fields
    /// ([`borer_engine::analysis::stated::crowded`]). A count is of the
    /// entries the file holds, so it is never under what loads, and a
    /// function stating no variable counts as one.
    ///
    /// # Errors
    ///
    /// When a count passes its cap; the message names the table.
    fn counted(&self) -> Result<(), String> {
        borer_engine::analysis::utypes::counted(&self.types, self.applied.len())
            .map_err(|e| e.to_string())?;
        let held: usize = self.vars.values().map(|table| table.len().max(1)).sum();
        if self.prototypes.len() > PROTOTYPES_MAX || held > VARS_MAX {
            return Err(format!(
                "the project states {} prototypes and {held} variables; {PROTOTYPES_MAX} and {VARS_MAX} are the most",
                self.prototypes.len()
            ));
        }
        for (class, table) in &self.fields {
            let class = borer_engine::text::one_line(class);
            borer_engine::analysis::stated::crowded(&class, table.len(), self.fields.len())?;
        }
        Ok(())
    }

    /// Judges whether the project was saved for the loaded binary.
    ///
    /// A project with its binary's SHA-256 belongs to the same bytes
    /// wherever they were loaded from, and to nothing else: a rebuild at
    /// the same path has other addresses, and took the old names silently
    /// while the path was the identity. One saved before projects recorded
    /// the hash is judged by its path ([`ProjectFile::is_for`]).
    ///
    /// # Arguments
    ///
    /// * `program` - The loaded binary.
    #[must_use]
    pub fn identify(&self, program: &Program) -> Identity {
        match &self.sha256 {
            Some(saved) if saved.eq_ignore_ascii_case(&identity(&program.bytes)) => Identity::Same,
            Some(_) => Identity::Other,
            None if self.is_for(&program.path) => Identity::PathOnly,
            None => Identity::OtherPath,
        }
    }

    /// Tells whether the project was saved for the binary at `path`.
    ///
    /// A project with its binary's SHA-256 is matched by the hash alone
    /// ([`ProjectFile::identify`]); one without is matched here, by the path
    /// it records and the loaded one compared as text ([`lexical`]), never
    /// on disk, so a project file never makes borer open a path. Two
    /// spellings only the disk shows to be one file (a link, an 8.3 name, a
    /// name in another letter case) are two paths, so `load_project`
    /// refuses the project unless forced.
    ///
    /// # Arguments
    ///
    /// * `path` - Where the loaded binary was loaded from.
    #[must_use]
    pub fn is_for(&self, path: &Path) -> bool {
        lexical(Path::new(&self.program)) == lexical(path)
    }

    /// Writes the file as pretty-printed JSON.
    ///
    /// A device is refused: a project is written so it can be loaded again,
    /// and [`Self::load`] refuses a device, so saving to one reported success
    /// and put the overlay on the console.
    ///
    /// # Arguments
    ///
    /// * `path` - Destination path.
    /// * `existing` - Whether a regular file already at `path` is
    ///   replaced; a link there is never written through.
    ///
    /// # Errors
    ///
    /// When the path is a device, a file is there and `existing` keeps it,
    /// or serialization or the write fails.
    pub fn save(&self, path: &str, existing: crate::output::Existing) -> Result<(), String> {
        let json = serde_json::to_string_pretty(self).map_err(|e| format!("serialize: {e}"))?;
        if let Some(why) = borer_engine::program::unusable_path(Path::new(path)) {
            return Err(format!("{why}; nothing was written"));
        }
        let shown = borer_engine::text::short_path(path);
        let mut file = crate::output::create(Path::new(path), existing)
            .map_err(|e| format!("write {shown}: {e}"))?;
        std::io::Write::write_all(&mut file, json.as_bytes())
            .map_err(|e| format!("write {shown}: {e}"))
    }

    /// Reads and parses a project file.
    ///
    /// # Arguments
    ///
    /// * `path` - Source path.
    ///
    /// # Errors
    ///
    /// When the path is a device, a share or not a regular file, the file
    /// is past [`PROJECT_MAX`] bytes or cannot be read, or it is not a valid
    /// project file.
    pub fn load(path: &str) -> Result<ProjectFile, String> {
        let shown = borer_engine::text::short_path(path);
        let bytes = borer_engine::program::read_regular(Path::new(path), PROJECT_MAX)
            .map_err(|e| format!("{e:#}"))?;
        serde_json::from_slice(&bytes).map_err(|e| format!("parse {shown}: {e}"))
    }
}
