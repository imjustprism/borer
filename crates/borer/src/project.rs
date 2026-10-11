//! Project persistence: overlay annotations saved as an editable JSON file.

use std::collections::BTreeMap;
use std::path::Path;

use borer_engine::analysis::Overlay;
use borer_engine::analysis::utypes::UserType;

/// A saved annotation overlay: the binary it belongs to, its names,
/// comments and user-defined types, keyed by `0x`-hex address text where an
/// address keys them (editable by hand).
#[derive(Debug, serde::Serialize, serde::Deserialize)]
pub struct ProjectFile {
    /// Path of the binary the annotations belong to.
    pub program: String,
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

/// Keys annotations by address again; an unparsable key maps to `0`.
///
/// A project file is edited and passed around like any other file, so the
/// text in it comes from outside and is escaped the way the names in a
/// binary are: the listings that print it are one record to a line.
///
/// # Arguments
///
/// * `map` - Annotations by `0x`-hex address text.
fn by_address(map: &BTreeMap<String, String>) -> BTreeMap<u64, String> {
    map.iter()
        .map(|(k, v)| {
            (
                u64::from_str_radix(k.trim_start_matches("0x"), 16).unwrap_or(0),
                borer_engine::text::one_line(v),
            )
        })
        .collect()
}

impl ProjectFile {
    /// Builds the file contents from an overlay.
    ///
    /// # Arguments
    ///
    /// * `program` - Path of the binary the annotations belong to.
    /// * `o` - The overlay.
    pub fn from_overlay(program: &str, o: &Overlay) -> ProjectFile {
        ProjectFile {
            program: program.to_owned(),
            names: by_hex(&o.names),
            comments: by_hex(&o.comments),
            types: o.types.clone(),
            applied: o
                .applied
                .iter()
                .map(|(k, v)| (format!("{k:#x}"), v.spell()))
                .collect(),
        }
    }

    /// Rebuilds the overlay.
    ///
    /// An unparsable address key maps to `0` and the annotation text is
    /// escaped to one line ([`by_address`]); the applied types are parsed
    /// and the whole set of types checked ([`borer_engine::analysis::utypes::validate`]),
    /// so a hand-edited file that names a type nothing states, or states
    /// one in a form the language does not spell, is refused here with a
    /// message naming it rather than silently naming no fields.
    ///
    /// # Returns
    ///
    /// The overlay.
    ///
    /// # Errors
    ///
    /// When an applied type does not parse or a defined type's references
    /// do not resolve.
    pub fn to_overlay(&self) -> Result<Overlay, String> {
        let mut applied: BTreeMap<u64, borer_engine::analysis::utypes::TypeExpr> = BTreeMap::new();
        for (k, v) in &self.applied {
            let ty = borer_engine::analysis::utypes::parse_type(v)
                .map_err(|e| format!("the type applied at {k}, {v}, {e}"))?;
            applied.insert(
                u64::from_str_radix(k.trim_start_matches("0x"), 16).unwrap_or(0),
                ty,
            );
        }
        let o = Overlay {
            names: by_address(&self.names),
            comments: by_address(&self.comments),
            types: self.types.clone(),
            applied,
            ..Overlay::default()
        };
        borer_engine::analysis::utypes::validate(&o.types, &o.applied)
            .map_err(|e| e.to_string())
            .map(|_| o)
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
    ///
    /// # Errors
    ///
    /// When the path is a device, or serialization or the write fails.
    pub fn save(&self, path: &str) -> Result<(), String> {
        let json = serde_json::to_string_pretty(self).map_err(|e| format!("serialize: {e}"))?;
        if let Some(why) = borer_engine::program::unusable_path(Path::new(path)) {
            return Err(format!("{why}; nothing was written"));
        }
        std::fs::write(Path::new(path), json).map_err(|e| format!("write {path}: {e}"))
    }

    /// Reads and parses a project file.
    ///
    /// # Arguments
    ///
    /// * `path` - Source path.
    ///
    /// # Errors
    ///
    /// When the file cannot be read or is not a valid project file.
    pub fn load(path: &str) -> Result<ProjectFile, String> {
        if let Some(why) = borer_engine::program::unusable_path(Path::new(path)) {
            return Err(why);
        }
        let text =
            std::fs::read_to_string(Path::new(path)).map_err(|e| format!("read {path}: {e}"))?;
        serde_json::from_str(&text).map_err(|e| format!("parse {path}: {e}"))
    }
}
