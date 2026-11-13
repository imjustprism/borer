//! Project persistence: overlay annotations saved as an editable JSON file.

use std::path::{Component, Path};

use borer_engine::analysis::Overlay;
use borer_engine::analysis::project::Project;
use borer_engine::program::Program;

/// A project file as the server reads and writes it: the annotations the
/// engine parses ([`Project`]), read and written on disk here and judged
/// against the loaded binary.
///
/// Its fields and [`Project::to_overlay`] are the engine's, reached
/// through [`std::ops::Deref`]; the file holds the same JSON.
#[derive(Debug, serde::Serialize, serde::Deserialize)]
#[serde(transparent)]
pub struct ProjectFile(pub Project);

impl std::ops::Deref for ProjectFile {
    type Target = Project;

    /// Returns the annotations the file holds.
    fn deref(&self) -> &Project {
        &self.0
    }
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

/// Largest project file read or written, in bytes ([`ProjectFile::load`],
/// [`ProjectFile::save`]).
const PROJECT_MAX: u64 = 1 << 26;

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
    /// Builds the file contents from an overlay ([`Project::from_overlay`]).
    ///
    /// # Arguments
    ///
    /// * `program` - Path of the binary the annotations belong to.
    /// * `sha256` - The binary's [`identity`]; `None` leaves the file
    ///   identifying it by path, for a file that is only read back by the
    ///   session that wrote it.
    /// * `o` - The overlay.
    pub fn from_overlay(program: &str, sha256: Option<String>, o: &Overlay) -> ProjectFile {
        ProjectFile(Project::from_overlay(program, sha256, o))
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
    /// the file would be longer than [`PROJECT_MAX`] even unindented, which
    /// [`Self::load`] refuses, or serialization or the write fails; nothing
    /// is written unless the write itself fails.
    pub fn save(&self, path: &str, existing: crate::output::Existing) -> Result<(), String> {
        let fits = |json: &str| borer_engine::num::from_usize(json.len()) <= PROJECT_MAX;
        let mut json = serde_json::to_string_pretty(self).map_err(|e| format!("serialize: {e}"))?;
        if !fits(&json) {
            json = serde_json::to_string(self).map_err(|e| format!("serialize: {e}"))?;
        }
        if !fits(&json) {
            return Err(format!(
                "the project is {} bytes even unindented, past the {PROJECT_MAX} a project file holds, so nothing was written",
                json.len()
            ));
        }
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
    /// project file: what the parser says of it, escaped to one line, since
    /// it quotes the file.
    pub fn load(path: &str) -> Result<ProjectFile, String> {
        let shown = borer_engine::text::short_path(path);
        let bytes = borer_engine::program::read_regular(Path::new(path), PROJECT_MAX)
            .map_err(|e| format!("{e:#}"))?;
        serde_json::from_slice(&bytes).map_err(|e| {
            format!(
                "parse {shown}: {}",
                borer_engine::text::one_line(&e.to_string())
            )
        })
    }
}
