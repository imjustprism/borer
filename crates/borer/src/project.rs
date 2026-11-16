//! Project persistence: overlay annotations saved as an editable JSON file.
//!
//! The file's form, which binary it belongs to and what of it a binary
//! keeps are the engine's ([`borer_engine::analysis::project`]); reading it
//! from disk and writing it under the output rules are the server's.

use std::path::Path;

use borer_engine::analysis::Overlay;
pub use borer_engine::analysis::project::{Identity, identity, program_identity};
use borer_engine::analysis::project::{PROJECT_MAX, Project};

/// A project file as the server reads and writes it: the annotations the
/// engine parses ([`Project`]), read and written on disk here.
///
/// Its fields and the engine's methods ([`Project::to_overlay`],
/// [`Project::identify`], [`Project::is_for`]) are reached through
/// [`std::ops::Deref`]; the file holds the same JSON.
#[derive(Debug, serde::Serialize, serde::Deserialize)]
#[serde(transparent)]
pub struct ProjectFile(
    /// The parsed project annotations.
    pub Project,
);

impl std::ops::Deref for ProjectFile {
    type Target = Project;

    /// Returns the annotations the file holds.
    fn deref(&self) -> &Project {
        &self.0
    }
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

    /// Writes the file as the engine spells it ([`Project::to_json`]).
    ///
    /// An unusable path is refused before serializing: a project is written
    /// so it can be loaded again, and [`Self::load`] refuses a device or a
    /// share, so saving to a device reported success and put the overlay on
    /// the console.
    ///
    /// # Arguments
    ///
    /// * `path` - Destination path.
    /// * `existing` - Whether a regular file already at `path` is
    ///   replaced; a link there is never written through.
    ///
    /// # Errors
    ///
    /// When `path` is unusable ([`borer_engine::program::unusable_path`]:
    /// empty, a device, an NT object path or a network share), the engine
    /// refuses to spell the file ([`Project::to_json`]), a file or link is
    /// there and `existing` refuses it, or the write fails; nothing is
    /// written unless the write itself fails.
    pub fn save(&self, path: &str, existing: crate::output::Existing) -> Result<(), String> {
        if let Some(why) = borer_engine::program::unusable_path(Path::new(path)) {
            return Err(format!("{why}; nothing was written"));
        }
        let bytes = self.0.to_json()?;
        let shown = borer_engine::text::short_path(path);
        let mut file = crate::output::create(Path::new(path), existing)
            .map_err(|e| format!("write {shown}: {e}"))?;
        std::io::Write::write_all(&mut file, &bytes).map_err(|e| format!("write {shown}: {e}"))
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
    /// project file ([`Project::from_json`]).
    pub fn load(path: &str) -> Result<ProjectFile, String> {
        let shown = borer_engine::text::short_path(path);
        let bytes = borer_engine::program::read_regular(Path::new(path), PROJECT_MAX)
            .map_err(|e| format!("{e:#}"))?;
        Project::from_json(&bytes)
            .map(ProjectFile)
            .map_err(|why| format!("parse {shown}: {why}"))
    }
}

#[cfg(test)]
#[expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]
mod tests {
    use super::PROJECT_MAX;

    /// Saving an over-cap [`super::ProjectFile`] fails before touching an
    /// existing destination file.
    #[test]
    fn save_refuses_over_cap_tables_without_touching_existing_file() {
        let dir = std::env::temp_dir().join(format!("borer-save-cap-{}", std::process::id()));
        std::fs::create_dir_all(&dir).expect("temp dir");
        let path = dir.join("p.json");
        let shown = path.display().to_string();
        super::ProjectFile::from_overlay("b", None, &super::Overlay::default())
            .save(&shown, crate::output::Existing::Replace)
            .expect("seed project");
        let before = borer_engine::program::read_regular(&path, PROJECT_MAX).expect("seed bytes");
        let mut crowded = super::Overlay::default();
        for va in 0..=borer_engine::num::from_usize(borer_engine::analysis::project::NAMES_MAX) {
            crowded.names.insert(va, "n".to_owned());
        }
        let err = super::ProjectFile::from_overlay("b", None, &crowded)
            .save(&shown, crate::output::Existing::Replace)
            .expect_err("over-cap save must fail");
        let after =
            borer_engine::program::read_regular(&path, PROJECT_MAX).expect("seed bytes preserved");
        std::fs::remove_dir_all(&dir).ok();
        assert!(err.contains("262145 names"), "{err}");
        assert_eq!(before, after);
    }
}
