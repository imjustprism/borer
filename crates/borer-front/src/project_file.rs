//! Writing a project file the way both front ends do: the engine spells it
//! ([`Project::to_json`]), and it lands whole or not at all.

use std::io::Write as _;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};

use borer_engine::analysis::project::Project;
use borer_engine::program::unusable_path;
use borer_engine::text::short_path;

/// What a write does to a file already at its destination.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Existing {
    /// The write is refused and the file is left as it was.
    Keep,
    /// The file is replaced, when it is a regular file and not a link.
    Replace,
}

impl Existing {
    /// Reads a tool's `overwrite` flag.
    ///
    /// # Arguments
    ///
    /// * `overwrite` - The flag, `None` when the call left it out.
    ///
    /// # Returns
    ///
    /// [`Existing::Replace`] only for an explicit `true`.
    #[must_use]
    pub fn from_flag(overwrite: Option<bool>) -> Self {
        if overwrite.unwrap_or(false) {
            Self::Replace
        } else {
            Self::Keep
        }
    }
}

/// Writes `file` to `path` as the engine spells it.
///
/// An unusable path ([`unusable_path`]: empty, a device, an NT object path or a network
/// share) is refused before anything is spelled, and so is a link or anything but a
/// regular file at `path`, which is never written through. The bytes go to a new file
/// beside `path`, named for this process and this save, that then takes `path`'s place
/// ([`land`]), so a failed write leaves what was there.
///
/// Replacing renames the new file over the old one, so the file at `path` has the new
/// file's ACL or mode rather than the old one's, a hard link to the old file keeps the old
/// bytes, and on Windows the rename is refused while another process holds the old file
/// open.
///
/// # Arguments
///
/// * `path` - Destination path.
/// * `file` - The project.
/// * `existing` - Whether a regular file already at `path` is replaced.
///
/// # Errors
///
/// When `path` is unusable, the engine refuses to spell the file, a link or other
/// non-file is there, a file is there and `existing` is [`Existing::Keep`], or the write,
/// the rename or the link fails; nothing at `path` changed.
pub fn write(path: &Path, file: &Project, existing: Existing) -> Result<(), String> {
    if let Some(why) = unusable_path(path) {
        return Err(format!("{why}; nothing was written"));
    }
    let bytes = file.to_json()?;
    let shown = short_path(&path.to_string_lossy());
    #[expect(clippy::disallowed_methods, reason = "unusable_path cleared path")]
    let there = std::fs::symlink_metadata(path);
    match there {
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => {}
        Err(e) => return Err(format!("write {shown}: {e}")),
        Ok(m) if m.file_type().is_symlink() || !m.is_file() => {
            return Err(format!(
                "write {shown}: a link or not a regular file is there"
            ));
        }
        Ok(_) => {}
    }
    let staged = staging(path);
    put(&staged, &bytes)
        .and_then(|()| land(&staged, path, existing))
        .map_err(|e| format!("write {shown}: {e}"))
}

/// Returns the file beside `path` its bytes are written to before they land, named for
/// this process and this save, so two saves never share one.
///
/// # Arguments
///
/// * `path` - Destination path.
fn staging(path: &Path) -> PathBuf {
    /// Saves this process has staged.
    static SAVES: AtomicU64 = AtomicU64::new(0);
    let save = SAVES.fetch_add(1, Ordering::Relaxed);
    let name = path.file_name().unwrap_or_default().to_string_lossy();
    path.with_file_name(format!(".{name}.{}.{save}.tmp", std::process::id()))
}

/// Puts the filled staging file at `path`; the staging name is gone after either way.
///
/// [`Existing::Replace`] renames it over what is there, and [`Existing::Keep`] links it
/// there, which fails when anything is there by then, so a file that appeared since the
/// check is never replaced.
///
/// # Arguments
///
/// * `staged` - The filled staging file.
/// * `path` - Destination path.
/// * `existing` - Whether a file at `path` is replaced.
///
/// # Errors
///
/// When the rename or the link fails, or the staging name cannot be removed after the
/// link.
fn land(staged: &Path, path: &Path, existing: Existing) -> std::io::Result<()> {
    match existing {
        Existing::Replace => std::fs::rename(staged, path).map_err(|e| discard(staged, e)),
        Existing::Keep => {
            std::fs::hard_link(staged, path).map_err(|e| discard(staged, e))?;
            std::fs::remove_file(staged).map_err(|left| {
                std::io::Error::other(format!("written, but {} is left: {left}", staged.display()))
            })
        }
    }
}

/// Writes `bytes` to a file at `staged` that must not be there yet, so a link planted
/// there is never written through; a file it made and could not fill is removed.
///
/// # Arguments
///
/// * `staged` - The staging path ([`staging`]).
/// * `bytes` - The file's bytes.
///
/// # Errors
///
/// When something is at `staged` or the write fails.
fn put(staged: &Path, bytes: &[u8]) -> std::io::Result<()> {
    #[expect(
        clippy::disallowed_methods,
        reason = "a new file beside a checked path"
    )]
    let mut out = std::fs::OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(staged)?;
    let filled = out.write_all(bytes).and_then(|()| out.sync_all());
    drop(out);
    filled.map_err(|e| discard(staged, e))
}

/// Removes the staging file this write made after `e` stopped it, and returns `e`, saying
/// so when the file could not be removed.
///
/// # Arguments
///
/// * `staged` - The staging file.
/// * `e` - What stopped the write.
fn discard(staged: &Path, e: std::io::Error) -> std::io::Error {
    match std::fs::remove_file(staged) {
        Ok(()) => e,
        Err(left) => std::io::Error::other(format!("{e}; {} is left: {left}", staged.display())),
    }
}

#[cfg(test)]
mod tests {
    use std::path::{Path, PathBuf};

    use borer_engine::analysis::Overlay;
    use borer_engine::analysis::project::{PROJECT_MAX, Project};
    use borer_engine::program::read_regular;

    use super::{Existing, land, write};

    /// Returns a fresh directory of the tests named for `what`.
    ///
    /// # Panics
    ///
    /// Panics if the directory cannot be made.
    fn scratch(what: &str) -> PathBuf {
        let dir = std::env::temp_dir().join(format!("borer-front-{what}-{}", std::process::id()));
        std::fs::remove_dir_all(&dir).ok();
        std::fs::create_dir_all(&dir).unwrap();
        dir
    }

    /// Returns the bytes of the file at `path`.
    ///
    /// # Panics
    ///
    /// Panics if it does not read.
    fn bytes(path: &Path) -> Vec<u8> {
        read_regular(path, PROJECT_MAX).unwrap()
    }

    /// Returns an empty project.
    fn empty() -> Project {
        Project::from_overlay("b", None, &Overlay::default())
    }

    /// A project is written whole, a file there is kept unless replacing is asked for, and
    /// a project past a cap leaves the file there as it was with no staging file behind.
    ///
    /// # Panics
    ///
    /// Panics if a write lands when it must not, or leaves a file other than the project.
    #[test]
    #[expect(
        clippy::disallowed_methods,
        reason = "the test lists its own directory"
    )]
    fn a_project_lands_whole_or_not_at_all() {
        let dir = scratch("write");
        let path = dir.join("p.json");
        write(&path, &empty(), Existing::Keep).unwrap();
        let first = bytes(&path);
        assert!(write(&path, &empty(), Existing::Keep).is_err());
        let mut crowded = Overlay::default();
        for va in 0..=borer_engine::num::from_usize(borer_engine::analysis::project::NAMES_MAX) {
            crowded.names.insert(va, "n".to_owned());
        }
        let over = Project::from_overlay("b", None, &crowded);
        let err = write(&path, &over, Existing::Replace).unwrap_err();
        assert!(err.contains("262145 names"), "{err}");
        assert_eq!(bytes(&path), first);
        write(&path, &empty(), Existing::Replace).unwrap();
        let left: Vec<_> = std::fs::read_dir(&dir).unwrap().flatten().collect();
        std::fs::remove_dir_all(&dir).unwrap();
        assert_eq!(left.len(), 1);
    }

    /// A staged file that cannot land leaves what is at its destination as it was and is
    /// removed.
    ///
    /// The cases: a link refused because a file appeared there since the check, and a
    /// rename refused because a directory holding a file is there.
    ///
    /// # Panics
    ///
    /// Panics if the destination changes or the staged file stays.
    #[test]
    #[expect(
        clippy::disallowed_methods,
        reason = "the test lists its own directory"
    )]
    fn a_landing_that_fails_leaves_the_destination() {
        let dir = scratch("land");
        let path = dir.join("p.json");
        std::fs::write(&path, b"there first").unwrap();
        let staged = dir.join("staged");
        std::fs::write(&staged, b"new").unwrap();
        assert!(land(&staged, &path, Existing::Keep).is_err());
        assert_eq!(bytes(&path), b"there first");
        let held = dir.join("held");
        std::fs::create_dir_all(&held).unwrap();
        std::fs::write(held.join("inside"), b"kept").unwrap();
        std::fs::write(&staged, b"new").unwrap();
        assert!(land(&staged, &held, Existing::Replace).is_err());
        assert_eq!(bytes(&held.join("inside")), b"kept");
        let mut left: Vec<_> = std::fs::read_dir(&dir)
            .unwrap()
            .flatten()
            .map(|e| e.file_name())
            .collect();
        left.sort();
        std::fs::remove_dir_all(&dir).unwrap();
        assert_eq!(left, ["held", "p.json"]);
    }

    /// A save into a directory nothing can be created in fails and leaves the file there.
    /// Skipped when the directory takes a file anyway, as it does for root.
    ///
    /// # Panics
    ///
    /// Panics if the save lands or changes the file.
    #[cfg(unix)]
    #[test]
    fn a_save_that_cannot_stage_leaves_the_file() {
        use std::os::unix::fs::PermissionsExt as _;
        let dir = scratch("stage");
        let path = dir.join("p.json");
        std::fs::write(&path, b"there first").unwrap();
        let mode = |m| std::fs::set_permissions(&dir, std::fs::Permissions::from_mode(m));
        mode(0o555).unwrap();
        let writable = std::fs::write(dir.join("probe"), b"").is_ok();
        let saved = write(&path, &empty(), Existing::Replace);
        mode(0o755).unwrap();
        let after = bytes(&path);
        std::fs::remove_dir_all(&dir).unwrap();
        if writable {
            return;
        }
        assert!(saved.is_err());
        assert_eq!(after, b"there first");
    }

    /// A link at the destination is refused and what it points at is left as it was. On
    /// Windows the test is skipped when the account may not make a link (no developer mode
    /// or privilege).
    ///
    /// # Panics
    ///
    /// Panics if the save goes through the link.
    #[test]
    fn a_link_at_the_destination_is_refused() {
        let dir = scratch("link");
        let target = dir.join("target.json");
        std::fs::write(&target, b"kept").unwrap();
        let path = dir.join("p.json");
        #[cfg(unix)]
        let linked = std::os::unix::fs::symlink(&target, &path);
        #[cfg(windows)]
        let linked = std::os::windows::fs::symlink_file(&target, &path);
        if linked.is_err() {
            std::fs::remove_dir_all(&dir).unwrap();
            return;
        }
        let err = write(&path, &empty(), Existing::Replace).unwrap_err();
        let after = bytes(&target);
        std::fs::remove_dir_all(&dir).unwrap();
        assert!(
            err.contains("a link or not a regular file is there"),
            "{err}"
        );
        assert_eq!(after, b"kept");
    }
}
