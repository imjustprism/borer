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

    /// Writes the file as the engine spells it, whole or not at all
    /// ([`borer_front::project_file::write`]).
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
    /// there and `existing` refuses it, or the write fails; nothing at
    /// `path` changed.
    pub fn save(&self, path: &str, existing: crate::output::Existing) -> Result<(), String> {
        borer_front::project_file::write(Path::new(path), &self.0, existing)
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
