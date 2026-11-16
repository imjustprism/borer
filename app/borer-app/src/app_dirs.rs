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
