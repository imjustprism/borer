//! Where the app and Zed keep their files on each platform: the config directory (settings,
//! keymap, themes) and the data directory (database, logs, layout).
//!
//! Zed's `paths` crate keeps its config under the data directory once one is set
//! (`set_custom_data_dir` makes `config_dir` the data directory's `config`) and has no
//! override for config alone, so the app resolves its config directory here and reads and
//! writes the person's settings and themes there itself.

use std::ffi::OsString;
use std::path::{Path, PathBuf};
use std::sync::OnceLock;

use anyhow::Context as _;

/// The directory name the app's config and data live under.
const APP: &str = "borer";

/// The directory name earlier builds kept the app's config and data under ([`Env::legacy`]).
const LEGACY_APP: &str = "borer-app";

/// Most files and folders a migration copies ([`migrate`]); past it the copy stops.
const MIGRATE_MAX_ENTRIES: usize = 10_000;

/// Picks one directory of a [`Dirs`]: its config or its data directory.
type Pick = fn(&Dirs) -> &PathBuf;

/// What a migration copies from the old directories to the new: the settings file and the
/// themes folder of the config directory, and Zed's database of the data directory.
const MIGRATED: [(Pick, &str); 3] = [
    (|dirs| &dirs.config, "settings.json"),
    (|dirs| &dirs.config, "themes"),
    (|dirs| &dirs.data, "db"),
];

/// Copies what an earlier build kept in `old` into `new`, once: on the first run under `new`,
/// when neither of its directories exists yet; links inside a folder are skipped.
///
/// # Arguments
///
/// * `old` - Where the earlier build kept its files ([`Env::legacy`]).
/// * `new` - Where the app keeps them now ([`Env::borer`]).
///
/// # Returns
///
/// The paths copied to, empty when there was nothing to copy or `new` already exists.
///
/// # Errors
///
/// Returns an error naming the path when a stat, a read, a copy or a folder fails, or when
/// the old directories hold more than [`MIGRATE_MAX_ENTRIES`] entries.
pub fn migrate(old: &Dirs, new: &Dirs) -> anyhow::Result<Vec<PathBuf>> {
    if stat(&new.config)?.is_some() || stat(&new.data)?.is_some() {
        return Ok(Vec::new());
    }
    let mut budget = MIGRATE_MAX_ENTRIES;
    let mut copied = Vec::new();
    for (dir, name) in MIGRATED {
        let (from, to) = (dir(old).join(name), dir(new).join(name));
        let Some(meta) = stat(&from)? else {
            continue;
        };
        if let Some(parent) = to.parent() {
            std::fs::create_dir_all(parent)
                .with_context(|| format!("creating {}", parent.display()))?;
        }
        copy_tree(&from, &to, meta.is_dir(), &mut budget)?;
        copied.push(to);
    }
    Ok(copied)
}

/// Returns the metadata of `path`, `None` when nothing is there.
///
/// # Arguments
///
/// * `path` - A path under the app's own directories.
///
/// # Errors
///
/// Returns an error when the path is unusable, with the reason.
fn stat(path: &Path) -> anyhow::Result<Option<std::fs::Metadata>> {
    borer_engine::program::checked_metadata(path)
        .map_err(|why| anyhow::anyhow!("{}: {why}", path.display()))
}

/// Copies the file or folder `from` to `to`, folders whole, skipping the links in them.
///
/// # Arguments
///
/// * `from` - What to copy.
/// * `to` - Where it goes; its parent folder exists.
/// * `folder` - Whether `from` is a folder.
/// * `budget` - Entries left to copy, spent one per file or folder.
///
/// # Errors
///
/// Returns an error naming the path when a read, a copy or a folder fails, or when the
/// budget runs out.
fn copy_tree(from: &Path, to: &Path, folder: bool, budget: &mut usize) -> anyhow::Result<()> {
    *budget = budget
        .checked_sub(1)
        .with_context(|| format!("more than {MIGRATE_MAX_ENTRIES} entries to migrate"))?;
    if !folder {
        std::fs::copy(from, to).with_context(|| format!("copying {}", from.display()))?;
        return Ok(());
    }
    std::fs::create_dir_all(to).with_context(|| format!("creating {}", to.display()))?;
    #[expect(
        clippy::disallowed_methods,
        reason = "a folder of the app's own directories, which the app names itself"
    )]
    let entries = std::fs::read_dir(from).with_context(|| format!("reading {}", from.display()))?;
    for entry in entries {
        let entry = entry.with_context(|| format!("reading {}", from.display()))?;
        let kind = entry
            .file_type()
            .with_context(|| format!("reading {}", entry.path().display()))?;
        if kind.is_file() || kind.is_dir() {
            copy_tree(
                &entry.path(),
                &to.join(entry.file_name()),
                kind.is_dir(),
                budget,
            )?;
        }
    }
    Ok(())
}

/// The platform whose conventions place the directories.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Os {
    /// Linux and the other XDG desktops.
    Linux,
    /// macOS.
    MacOs,
    /// Windows.
    Windows,
}

impl Os {
    /// The platform the app runs on.
    pub const HOST: Self = if cfg!(target_os = "macos") {
        Self::MacOs
    } else if cfg!(windows) {
        Self::Windows
    } else {
        Self::Linux
    };
}

/// A program's config and data directories.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Dirs {
    /// Settings, keymap and themes.
    pub config: PathBuf,
    /// Database, logs and layout.
    pub data: PathBuf,
}

/// What the directories are resolved from: the platform, its environment and the home
/// directory.
pub struct Env<'a> {
    /// The platform.
    pub os: Os,
    /// Reads an environment variable.
    pub var: &'a dyn Fn(&str) -> Option<OsString>,
    /// The person's home directory.
    pub home: &'a Path,
}

impl std::fmt::Debug for Env<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Env")
            .field("os", &self.os)
            .field("home", &self.home)
            .finish_non_exhaustive()
    }
}

impl Env<'_> {
    /// Returns the variable `name` as a path when it is set to an absolute path; an empty
    /// or relative value counts as unset, as the XDG base directory spec says.
    ///
    /// # Arguments
    ///
    /// * `name` - The variable's name.
    fn dir(&self, name: &str) -> Option<PathBuf> {
        Some(PathBuf::from((self.var)(name)?)).filter(|dir| dir.is_absolute())
    }

    /// Returns the XDG directory `name` names, else `fallback` under the home directory.
    ///
    /// # Arguments
    ///
    /// * `name` - The XDG variable.
    /// * `fallback` - The default, relative to the home directory.
    fn xdg(&self, name: &str, fallback: &str) -> PathBuf {
        self.dir(name).unwrap_or_else(|| self.home.join(fallback))
    }

    /// Returns the Windows folder the variable `name` names.
    ///
    /// # Arguments
    ///
    /// * `name` - `APPDATA` or `LOCALAPPDATA`.
    ///
    /// # Errors
    ///
    /// Returns an error naming the variable when it is unset, empty or relative.
    fn windows(&self, name: &str) -> anyhow::Result<PathBuf> {
        self.dir(name)
            .with_context(|| format!("%{name}% is not set to an absolute path"))
    }

    /// Returns the macOS application support folder.
    fn support(&self) -> PathBuf {
        self.home.join("Library/Application Support")
    }

    /// Returns the app's directories: config in the platform's config directory and data in
    /// its local data directory, each under `borer`.
    ///
    /// # Errors
    ///
    /// Returns an error on Windows when `%APPDATA%` or `%LOCALAPPDATA%` is not set.
    pub fn borer(&self) -> anyhow::Result<Dirs> {
        let (config, data) = match self.os {
            Os::Linux => (
                self.xdg("XDG_CONFIG_HOME", ".config"),
                self.xdg("XDG_DATA_HOME", ".local/share"),
            ),
            Os::MacOs => (self.support(), self.support()),
            Os::Windows => (self.windows("APPDATA")?, self.windows("LOCALAPPDATA")?),
        };
        Ok(Dirs {
            config: config.join(APP),
            data: data.join(APP),
        })
    }

    /// Returns where builds before the move under `borer` kept the app's files: one
    /// `borer-app` directory in the platform's local data directory, its config in `config`
    /// under it.
    ///
    /// # Errors
    ///
    /// Returns an error on Windows when `%LOCALAPPDATA%` is not set.
    pub fn legacy(&self) -> anyhow::Result<Dirs> {
        let local = match self.os {
            Os::Linux => self.xdg("XDG_DATA_HOME", ".local/share"),
            Os::MacOs => self.support(),
            Os::Windows => self.windows("LOCALAPPDATA")?,
        };
        let data = local.join(LEGACY_APP);
        Ok(Dirs {
            config: data.join("config"),
            data,
        })
    }

    /// Returns where an installed Zed keeps its config and data, as Zed's `paths` crate
    /// places them when no data directory is given.
    ///
    /// # Errors
    ///
    /// Returns an error on Windows when `%APPDATA%` or `%LOCALAPPDATA%` is not set.
    pub fn zed(&self) -> anyhow::Result<Dirs> {
        Ok(match self.os {
            Os::Linux => Dirs {
                config: self.xdg("XDG_CONFIG_HOME", ".config").join("zed"),
                data: self.xdg("XDG_DATA_HOME", ".local/share").join("zed"),
            },
            Os::MacOs => Dirs {
                config: self.home.join(".config/zed"),
                data: self.support().join("Zed"),
            },
            Os::Windows => Dirs {
                config: self.windows("APPDATA")?.join("Zed"),
                data: self.windows("LOCALAPPDATA")?.join("Zed"),
            },
        })
    }
}

/// Returns `f` of this process's [`Env`].
///
/// # Arguments
///
/// * `f` - What to resolve.
///
/// # Errors
///
/// Returns an error when the platform has no home directory, or `f`'s error.
pub fn with_host_env<T>(f: impl FnOnce(&Env<'_>) -> anyhow::Result<T>) -> anyhow::Result<T> {
    let home = dirs::home_dir().context("the platform has no home directory")?;
    f(&Env {
        os: Os::HOST,
        var: &|name| std::env::var_os(name),
        home: &home,
    })
}

/// The app's config directory, once a person's run sets it.
static CONFIG_DIR: OnceLock<PathBuf> = OnceLock::new();

/// Sets the app's config directory for this process; a later call changes nothing.
///
/// # Arguments
///
/// * `dir` - The config directory.
pub fn set_config_dir(dir: PathBuf) {
    CONFIG_DIR.get_or_init(|| dir);
}

/// Returns the app's config directory: the one [`set_config_dir`] set, else Zed's under the
/// data directory, which a run given `--data-dir` keeps its config in.
#[must_use]
pub fn config_dir() -> &'static Path {
    CONFIG_DIR.get().unwrap_or_else(|| paths::config_dir())
}

/// Returns the person's settings file.
#[must_use]
pub fn settings_file() -> PathBuf {
    config_dir().join("settings.json")
}

/// Returns the person's themes folder.
#[must_use]
pub fn themes_dir() -> PathBuf {
    config_dir().join("themes")
}

#[cfg(test)]
mod tests {
    use std::ffi::OsString;
    use std::path::PathBuf;

    use super::{Dirs, Env, Os};

    /// Returns `rel` under an absolute root of the host, so a path reads as absolute here.
    fn at(rel: &str) -> PathBuf {
        let root = if cfg!(windows) { r"C:\" } else { "/" };
        PathBuf::from(root).join(rel)
    }

    /// Returns the directories `resolve` gives on `os` with the variables `vars` set to
    /// paths under the host's root (an empty or relative value as written).
    ///
    /// # Errors
    ///
    /// As `resolve`.
    fn resolved(
        os: Os,
        vars: &[(&str, &str)],
        resolve: impl Fn(&Env<'_>) -> anyhow::Result<Dirs>,
    ) -> anyhow::Result<Dirs> {
        let var = |name: &str| {
            let (_, value) = vars.iter().find(|(key, _)| *key == name)?;
            let rooted = value.strip_prefix('/').map(at);
            Some(rooted.map_or_else(|| OsString::from(value), PathBuf::into_os_string))
        };
        let home = at("home/p");
        resolve(&Env {
            os,
            var: &var,
            home: &home,
        })
    }

    /// Returns config and data as paths under the host's root.
    fn dirs(config: &str, data: &str) -> Dirs {
        Dirs {
            config: at(config),
            data: at(data),
        }
    }

    /// On Linux the XDG variables place config and data under `borer`; unset, empty or
    /// relative, the defaults under the home directory do.
    ///
    /// # Panics
    ///
    /// Panics if a directory resolves elsewhere.
    #[test]
    fn linux_follows_xdg_and_treats_empty_as_unset() {
        let set = [("XDG_CONFIG_HOME", "/x/cfg"), ("XDG_DATA_HOME", "/x/data")];
        let got = resolved(Os::Linux, &set, |env| env.borer()).unwrap();
        assert_eq!(got, dirs("x/cfg/borer", "x/data/borer"));
        let defaults = dirs("home/p/.config/borer", "home/p/.local/share/borer");
        assert_eq!(
            resolved(Os::Linux, &[], |env| env.borer()).unwrap(),
            defaults
        );
        let empty = [("XDG_CONFIG_HOME", ""), ("XDG_DATA_HOME", "")];
        assert_eq!(
            resolved(Os::Linux, &empty, |env| env.borer()).unwrap(),
            defaults
        );
        let relative = [("XDG_CONFIG_HOME", "cfg"), ("XDG_DATA_HOME", "data")];
        assert_eq!(
            resolved(Os::Linux, &relative, |env| env.borer()).unwrap(),
            defaults
        );
        let zed = resolved(Os::Linux, &set, |env| env.zed()).unwrap();
        assert_eq!(zed, dirs("x/cfg/zed", "x/data/zed"));
    }

    /// On macOS config and data share Application Support, and XDG variables change
    /// nothing; Zed keeps its config in `~/.config/zed`.
    ///
    /// # Panics
    ///
    /// Panics if a directory resolves elsewhere.
    #[test]
    fn macos_keeps_both_in_application_support() {
        let set = [("XDG_CONFIG_HOME", "/x/cfg")];
        let support = "home/p/Library/Application Support/borer";
        let got = resolved(Os::MacOs, &set, |env| env.borer()).unwrap();
        assert_eq!(got, dirs(support, support));
        let zed = resolved(Os::MacOs, &set, |env| env.zed()).unwrap();
        let zed_data = "home/p/Library/Application Support/Zed";
        assert_eq!(zed, dirs("home/p/.config/zed", zed_data));
    }

    /// An earlier build kept everything in `borer-app` under the local data directory, its
    /// config in `config` there.
    ///
    /// # Panics
    ///
    /// Panics if the old place resolves elsewhere.
    #[test]
    fn the_legacy_place_is_borer_app_in_local_data() {
        let set = [("APPDATA", "/roaming"), ("LOCALAPPDATA", "/local")];
        let got = resolved(Os::Windows, &set, |env| env.legacy()).unwrap();
        assert_eq!(got, dirs("local/borer-app/config", "local/borer-app"));
        let got = resolved(Os::Linux, &[], |env| env.legacy()).unwrap();
        let old = "home/p/.local/share/borer-app";
        assert_eq!(got, dirs(&format!("{old}/config"), old));
    }

    /// The first run under the new place copies the settings file, the themes folder and
    /// the database of the old one; once the new place exists nothing is copied again.
    ///
    /// # Panics
    ///
    /// Panics if a file is not copied, or is copied over the new place.
    #[test]
    fn the_first_run_copies_an_earlier_builds_files_once() {
        let root = std::env::temp_dir().join(format!("borer-app-migrate-{}", std::process::id()));
        let old = Dirs {
            config: root.join("old/config"),
            data: root.join("old"),
        };
        let new = Dirs {
            config: root.join("new/config"),
            data: root.join("new/data"),
        };
        let theme = old.config.join("themes/mine.json");
        let db = old.data.join("db/0-stable/db.sqlite");
        for file in [&old.config.join("settings.json"), &theme, &db] {
            std::fs::create_dir_all(file.parent().unwrap()).unwrap();
            std::fs::write(file, file.display().to_string()).unwrap();
        }
        let copied = super::migrate(&old, &new).unwrap();
        assert_eq!(copied.len(), 3, "{copied:?}");
        let read = |path: PathBuf| {
            let bytes = borer_engine::program::read_regular(&path, 1 << 16).unwrap();
            String::from_utf8(bytes).unwrap()
        };
        assert_eq!(
            read(new.config.join("themes/mine.json")),
            theme.display().to_string()
        );
        assert_eq!(
            read(new.data.join("db/0-stable/db.sqlite")),
            db.display().to_string()
        );
        std::fs::write(new.config.join("settings.json"), "mine").unwrap();
        assert!(super::migrate(&old, &new).unwrap().is_empty());
        assert_eq!(read(new.config.join("settings.json")), "mine");
        std::fs::remove_dir_all(&root).unwrap();
    }

    /// On Windows config is under `%APPDATA%` and data under `%LOCALAPPDATA%`; an empty
    /// one is an error naming it.
    ///
    /// # Panics
    ///
    /// Panics if a directory resolves elsewhere or an empty variable is taken.
    #[test]
    fn windows_splits_roaming_config_from_local_data() {
        let set = [("APPDATA", "/roaming"), ("LOCALAPPDATA", "/local")];
        let got = resolved(Os::Windows, &set, |env| env.borer()).unwrap();
        assert_eq!(got, dirs("roaming/borer", "local/borer"));
        let zed = resolved(Os::Windows, &set, |env| env.zed()).unwrap();
        assert_eq!(zed, dirs("roaming/Zed", "local/Zed"));
        let empty = [("APPDATA", ""), ("LOCALAPPDATA", "/local")];
        let err = resolved(Os::Windows, &empty, |env| env.borer()).unwrap_err();
        assert!(err.to_string().contains("%APPDATA%"), "{err}");
    }
}
