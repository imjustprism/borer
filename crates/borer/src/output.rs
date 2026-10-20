//! Where the server writes the files a tool call asks for.
//!
//! A tool argument can come from text inside the analyzed binary, so a
//! path an agent passes is not trusted to name a place worth writing: every
//! file the server writes lands under one output root, the directory
//! `BORER_OUTPUT_DIR` names, else the loaded binary's project directory in
//! the borer data directory (`%LOCALAPPDATA%\borer\projects\<name>-<hash>`,
//! `$XDG_DATA_HOME/borer/projects/...`, `~/.local/share/borer/projects/...`).
//! A relative path is taken under the root and an absolute one must already
//! be under it; `..`, a directory link that leads out of the root, a link
//! at the file itself, a file without the expected extension and an
//! existing file (unless the call says to replace it) are all refused. The
//! command line writes where its user says and does not go through here.

use std::path::{Component, Path, PathBuf};

/// The environment variable naming the output root.
pub const OUTPUT_ENV: &str = "BORER_OUTPUT_DIR";

/// Longest binary file stem a project directory name keeps, in characters.
const STEM_MAX: usize = 64;

/// Hex digits of the binary's SHA-256 a project directory name keeps.
const HASH_SHOWN: usize = 12;

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

/// The base of the borer data directory, before `borer`.
///
/// # Returns
///
/// `%LOCALAPPDATA%`, `$XDG_DATA_HOME` or `~/.local/share`, or `None` when
/// no environment variable names one.
fn data_base() -> Option<PathBuf> {
    std::env::var_os("LOCALAPPDATA")
        .or_else(|| std::env::var_os("XDG_DATA_HOME"))
        .map(PathBuf::from)
        .or_else(|| std::env::var_os("HOME").map(|h| PathBuf::from(h).join(".local").join("share")))
}

/// The output root for a loaded binary.
///
/// # Arguments
///
/// * `binary` - The path the binary was loaded from.
/// * `sha256` - Its SHA-256 as hex, which names its project directory so
///   two builds at one path never share one.
///
/// # Returns
///
/// `$BORER_OUTPUT_DIR` when it is set and not empty, else the binary's
/// project directory under the data directory.
///
/// # Errors
///
/// When the variable is unset and no environment variable names a data
/// directory.
pub fn root(binary: &Path, sha256: &str) -> Result<PathBuf, String> {
    if let Some(dir) = std::env::var_os(OUTPUT_ENV).filter(|d| !d.is_empty()) {
        return Ok(PathBuf::from(dir));
    }
    let stem: String = binary
        .file_stem()
        .map(|s| s.to_string_lossy())
        .unwrap_or_default()
        .chars()
        .map(|c| {
            if c.is_ascii_alphanumeric() || matches!(c, '.' | '_' | '-') {
                c
            } else {
                '_'
            }
        })
        .take(STEM_MAX)
        .collect();
    let hash: String = sha256.chars().take(HASH_SHOWN).collect();
    let base = data_base().ok_or_else(|| {
        format!("no output directory: set {OUTPUT_ENV}, LOCALAPPDATA, XDG_DATA_HOME or HOME")
    })?;
    Ok(base
        .join("borer")
        .join("projects")
        .join(format!("{stem}-{hash}")))
}

/// Resolves a requested output path to the file a write may create.
///
/// The root is made if it is missing and canonicalized, a relative path is
/// joined to it, and the destination's directory is made and canonicalized
/// in turn, so a directory link that leads out of the root is caught by
/// what the directory really is, not by how the path spells it.
///
/// # Arguments
///
/// * `root` - The output root ([`root`]).
/// * `requested` - The path the call named, relative to the root or
///   absolute under it.
/// * `extensions` - The extensions accepted, lowercase without the dot.
/// * `existing` - Whether a file already there may be replaced.
///
/// # Returns
///
/// The absolute destination: the canonical directory joined to the file
/// name.
///
/// # Errors
///
/// When the path is empty, a device or a share, holds `..`, lacks an
/// accepted extension, leads outside the root, names a link or something
/// other than a regular file, or names an existing file and `existing` is
/// [`Existing::Keep`]; also when a directory cannot be made. Each message
/// names the root and says what to change.
pub fn confine(
    root: &Path,
    requested: &str,
    extensions: &[&str],
    existing: Existing,
) -> Result<PathBuf, String> {
    let path = Path::new(requested);
    let shown = borer_engine::text::short_path(requested);
    if let Some(why) = borer_engine::program::unusable_path(path) {
        return Err(format!("{why}; nothing was written"));
    }
    if path.components().any(|c| matches!(c, Component::ParentDir)) {
        return Err(format!(
            "{shown} holds `..`; name a file under the output root {}",
            root.display()
        ));
    }
    let ext = path
        .extension()
        .map(|e| e.to_string_lossy().to_ascii_lowercase());
    if !ext.as_deref().is_some_and(|e| extensions.contains(&e)) {
        return Err(format!(
            "{shown} does not end in .{}; nothing was written",
            extensions.join(" or .")
        ));
    }
    std::fs::create_dir_all(root)
        .map_err(|e| format!("making the output root {}: {e}", root.display()))?;
    let base = std::fs::canonicalize(root)
        .map_err(|e| format!("reading the output root {}: {e}", root.display()))?;
    let joined = if path.is_absolute() {
        path.to_path_buf()
    } else {
        base.join(path)
    };
    let outside = || {
        format!(
            "{shown} is outside the output root {}; give a path under it, or set {OUTPUT_ENV}",
            base.display()
        )
    };
    let (Some(parent), Some(name)) = (joined.parent(), joined.file_name()) else {
        return Err(outside());
    };
    let mut made = parent;
    while !made.exists() {
        made = made.parent().ok_or_else(outside)?;
    }
    if !std::fs::canonicalize(made).is_ok_and(|p| p.starts_with(&base)) {
        return Err(outside());
    }
    std::fs::create_dir_all(parent).map_err(|e| format!("making {}: {e}", parent.display()))?;
    let dir =
        std::fs::canonicalize(parent).map_err(|e| format!("reading {}: {e}", parent.display()))?;
    if !dir.starts_with(&base) {
        return Err(outside());
    }
    let dest = dir.join(name);
    match std::fs::symlink_metadata(&dest) {
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => Ok(dest),
        Err(e) => Err(format!("reading {}: {e}", dest.display())),
        Ok(m) if m.file_type().is_symlink() || !m.is_file() => Err(format!(
            "{} is a link or not a regular file; nothing was written",
            dest.display()
        )),
        Ok(_) => match existing {
            Existing::Keep => Err(format!(
                "{} exists; pass overwrite=true to replace it",
                dest.display()
            )),
            Existing::Replace => Ok(dest),
        },
    }
}

/// Resolves a requested output path under a loaded program's output root.
///
/// # Arguments
///
/// * `program` - The loaded binary, whose path and SHA-256 name its root.
/// * `requested` - The path the call named.
/// * `extensions` - The extensions accepted, lowercase without the dot.
/// * `existing` - Whether a file already there may be replaced.
///
/// # Returns
///
/// The absolute destination, as [`confine`] answers.
///
/// # Errors
///
/// As [`root`] and [`confine`].
pub fn for_program(
    program: &borer_engine::program::Program,
    requested: &str,
    extensions: &[&str],
    existing: Existing,
) -> Result<PathBuf, String> {
    let root = root(&program.path, &crate::project::identity(&program.bytes))?;
    confine(&root, requested, extensions, existing)
}

/// Creates a file for writing, never through a link.
///
/// # Arguments
///
/// * `path` - The file.
/// * `existing` - Whether a regular file already there is truncated.
///
/// # Returns
///
/// The file, open for writing and empty.
///
/// # Errors
///
/// When something other than a regular file is there, a file is there
/// and `existing` is [`Existing::Keep`], or the open fails.
pub fn create(path: &Path, existing: Existing) -> std::io::Result<std::fs::File> {
    let mut options = std::fs::OpenOptions::new();
    options.write(true);
    match std::fs::symlink_metadata(path) {
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => {
            options.create_new(true);
        }
        Err(e) => return Err(e),
        Ok(m) if m.file_type().is_symlink() || !m.is_file() => {
            return Err(std::io::Error::other(
                "a link or not a regular file is there",
            ));
        }
        Ok(_) => match existing {
            Existing::Keep => {
                options.create_new(true);
            }
            Existing::Replace => {
                options.truncate(true);
            }
        },
    }
    options.open(path)
}

#[cfg(test)]
mod tests {
    use super::{Existing, confine, create};
    use std::path::{Path, PathBuf};

    /// A fresh directory under the temporary directory.
    ///
    /// # Panics
    ///
    /// When the directory cannot be made.
    fn scratch(name: &str) -> PathBuf {
        let dir = std::env::temp_dir().join(format!("borer_output_{name}_{}", std::process::id()));
        std::fs::remove_dir_all(&dir).ok();
        std::fs::create_dir_all(&dir).expect("a scratch directory");
        dir
    }

    /// A relative name lands under the root, an absolute one under it is
    /// accepted, and the answer is absolute.
    ///
    /// # Panics
    ///
    /// When a path under the root is refused or resolves elsewhere.
    #[test]
    fn a_path_under_the_root_resolves_absolute() {
        let root = scratch("under");
        let base = std::fs::canonicalize(&root).expect("canonical");
        let rel = confine(&root, "sub/all.c", &["c"], Existing::Keep).expect("relative");
        assert_eq!(rel, base.join("sub").join("all.c"));
        assert!(rel.is_absolute());
        let abs = base.join("p.json").display().to_string();
        let got = confine(&root, &abs, &["json"], Existing::Keep).expect("absolute under");
        assert_eq!(got, base.join("p.json"));
        std::fs::remove_dir_all(&root).ok();
    }

    /// `..`, a path outside the root, a wrong extension and an existing
    /// file without overwrite are each refused.
    ///
    /// # Panics
    ///
    /// When a hostile path is accepted.
    #[test]
    fn a_path_that_escapes_is_refused() {
        let root = scratch("escape");
        let outside = std::env::temp_dir().join("borer_output_elsewhere.c");
        for bad in [
            "../x.c".to_owned(),
            "a/../../x.c".to_owned(),
            outside.display().to_string(),
            "x.exe".to_owned(),
            "x".to_owned(),
            String::new(),
        ] {
            assert!(
                confine(&root, &bad, &["c"], Existing::Replace).is_err(),
                "{bad} was accepted"
            );
        }
        if cfg!(windows) {
            for share in [r"\\host\share\x.c", "//host/share/x.c", r"\\.\pipe\x.c"] {
                let why = confine(&root, share, &["c"], Existing::Replace)
                    .expect_err("a share or a device is refused");
                assert!(why.contains("nothing was written"), "{why}");
            }
        }
        let dest = confine(&root, "kept.c", &["c"], Existing::Keep).expect("new");
        std::fs::write(&dest, b"first").expect("written");
        let kept = confine(&root, "kept.c", &["c"], Existing::Keep).expect_err("exists");
        assert!(kept.contains("overwrite=true"), "{kept}");
        assert!(
            create(&dest, Existing::Keep).is_err(),
            "create keeps it too"
        );
        assert_eq!(
            confine(&root, "kept.c", &["c"], Existing::Replace).expect("replace"),
            dest
        );
        assert_eq!(std::fs::read(&dest).expect("read"), b"first");
        std::fs::remove_dir_all(&root).ok();
    }

    /// A directory link that leads out of the root, and a link at the file
    /// itself, are refused; skipped where links cannot be made.
    ///
    /// # Panics
    ///
    /// When a write would follow a link out of the root.
    #[test]
    fn a_link_out_of_the_root_is_refused() {
        let root = scratch("link");
        let away = scratch("link_away");
        let target = away.join("victim.c");
        std::fs::write(&target, b"untouched").expect("written");
        #[cfg(unix)]
        let made = std::os::unix::fs::symlink(&away, root.join("out")).is_ok()
            && std::os::unix::fs::symlink(&target, root.join("file.c")).is_ok();
        #[cfg(windows)]
        let made = std::os::windows::fs::symlink_dir(&away, root.join("out")).is_ok()
            && std::os::windows::fs::symlink_file(&target, root.join("file.c")).is_ok();
        if made {
            assert!(confine(&root, "out/victim.c", &["c"], Existing::Replace).is_err());
            assert!(confine(&root, "out/new.c", &["c"], Existing::Replace).is_err());
            assert!(confine(&root, "file.c", &["c"], Existing::Replace).is_err());
            assert!(create(&root.join("file.c"), Existing::Replace).is_err());
            assert_eq!(std::fs::read(&target).expect("read"), b"untouched");
        }
        std::fs::remove_dir_all(&root).ok();
        std::fs::remove_dir_all(&away).ok();
        assert!(!Path::new(&root).exists());
    }
}
