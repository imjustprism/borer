//! Where a front end looks when its user names nothing else: the borer caches (the symbol
//! cache among them) and the pack directories, from the process's environment.
//!
//! A base directory variable (`APPDATA`, `LOCALAPPDATA`, `XDG_*`, `HOME`) or
//! `BORER_SYMCACHE` set to the empty string counts as unset: an empty `APPDATA` names no
//! directory, and joined with `borer` it would name one relative to the working directory.
//!
//! The pack directories are `BORER_PACK_DIRS` when it is set (set empty, it lists none,
//! which turns them off), else the user's
//! (`%APPDATA%\borer\packs`, `$XDG_CONFIG_HOME/borer/packs`, `~/.config/borer/packs`) and
//! the `packs` directory beside the executable or two levels above it (a `target/release`
//! build in the source tree). `BORER_AUTO_PACKS=0` turns them off.

use std::ffi::OsString;
use std::path::{Path, PathBuf};

use borer_engine::program::unusable_path;

/// The variable naming the pack directories.
pub const DIRS_ENV: &str = "BORER_PACK_DIRS";
/// The variable that turns the pack directories off when it is `0`.
pub const AUTO_ENV: &str = "BORER_AUTO_PACKS";
/// The variable naming the symbol cache directory.
pub const SYMCACHE_ENV: &str = "BORER_SYMCACHE";

/// Reads one environment variable: the process's, or a test's.
type Env<'a> = &'a dyn Fn(&str) -> Option<OsString>;

/// Returns the process's variable `name`, as it is set.
///
/// # Arguments
///
/// * `name` - The variable.
fn process(name: &str) -> Option<OsString> {
    std::env::var_os(name)
}

/// Returns variable `name` as `env` reads it, `None` when unset or empty.
///
/// # Arguments
///
/// * `env` - The environment.
/// * `name` - The variable.
fn var(env: Env<'_>, name: &str) -> Option<OsString> {
    env(name).filter(|value| !value.is_empty())
}

/// Returns the first of `vars` that is set, else `$HOME` joined with `home`.
///
/// # Arguments
///
/// * `env` - The environment.
/// * `vars` - Variables naming a base directory, in order.
/// * `home` - The base's path under `$HOME`.
fn base(env: Env<'_>, vars: &[&str], home: &[&str]) -> Option<PathBuf> {
    vars.iter()
        .find_map(|name| var(env, name))
        .map(PathBuf::from)
        .or_else(|| var(env, "HOME").map(|h| home.iter().fold(PathBuf::from(h), |p, d| p.join(d))))
}

/// Tells whether packs in the pack directories may load by themselves: unless
/// `BORER_AUTO_PACKS` is `0`.
#[must_use]
pub fn auto_enabled() -> bool {
    var(&process, AUTO_ENV).is_none_or(|v| v != "0")
}

/// Returns the paths an environment variable lists, as the platform writes a path list
/// (`;` on Windows, `:` elsewhere), empty entries dropped.
///
/// # Arguments
///
/// * `name` - The variable's name.
///
/// # Returns
///
/// The paths, or `None` when the variable is unset; set empty, it lists none.
#[must_use]
pub fn env_paths(name: &str) -> Option<Vec<PathBuf>> {
    paths_in(&process, name)
}

/// Returns the paths variable `name` of `env` lists ([`env_paths`]).
///
/// # Arguments
///
/// * `env` - The environment.
/// * `name` - The variable's name.
fn paths_in(env: Env<'_>, name: &str) -> Option<Vec<PathBuf>> {
    let list = env(name)?;
    Some(
        std::env::split_paths(&list)
            .filter(|p| !p.as_os_str().is_empty())
            .collect(),
    )
}

/// Returns the pack directories, in search order, each once.
///
/// One that names a share or a device ([`unusable_path`]) is listed as given and never
/// touched: [`borer_engine::session::read_dirs`] skips it with a note.
#[must_use]
pub fn dirs() -> Vec<PathBuf> {
    dirs_in(&process, std::env::current_exe().ok().as_deref())
}

/// Returns the pack directories `env` and the executable at `exe` give ([`dirs`]).
///
/// # Arguments
///
/// * `env` - The environment.
/// * `exe` - The running executable, `None` when unknown.
fn dirs_in(env: Env<'_>, exe: Option<&Path>) -> Vec<PathBuf> {
    let mut out: Vec<PathBuf> = Vec::new();
    if let Some(listed) = paths_in(env, DIRS_ENV) {
        out.extend(listed);
    } else {
        let config = base(env, &["APPDATA", "XDG_CONFIG_HOME"], &[".config"]);
        if let Some(base) = config {
            out.push(base.join("borer").join("packs"));
        }
        if let Some(dir) = exe.and_then(Path::parent) {
            out.push(dir.join("packs"));
            if let Some(tree) = dir.parent().and_then(Path::parent) {
                out.push(tree.join("packs"));
            }
        }
    }
    let mut seen: Vec<PathBuf> = Vec::new();
    out.retain(|d| {
        let key = if unusable_path(d).is_some() {
            d.clone()
        } else {
            #[expect(clippy::disallowed_methods, reason = "unusable_path just cleared d")]
            std::fs::canonicalize(d).unwrap_or_else(|_| d.clone())
        };
        let fresh = !seen.contains(&key);
        seen.push(key);
        fresh
    });
    out
}

/// Returns the pack directories to read: [`dirs`] when they may load by themselves, else
/// none.
///
/// # Arguments
///
/// * `auto` - Whether the pack directories are read.
#[must_use]
pub fn searched(auto: bool) -> Vec<PathBuf> {
    if auto { dirs() } else { Vec::new() }
}

/// Returns the platform cache directory every borer cache hangs from (`%LOCALAPPDATA%`,
/// `$XDG_CACHE_HOME`, else `~/.cache`).
///
/// # Returns
///
/// The directory, or `None` when no environment variable names a base.
#[must_use]
pub fn cache_base() -> Option<PathBuf> {
    base(&process, &["LOCALAPPDATA", "XDG_CACHE_HOME"], &[".cache"])
}

/// Returns the directory one borer cache lives in: `$<name>`, else `borer/<subdir>` under
/// [`cache_base`].
///
/// # Arguments
///
/// * `name` - The environment variable that names the directory.
/// * `subdir` - The cache's folder under the platform's `borer` folder.
/// * `label` - What a refusal of the default directory calls it.
///
/// # Returns
///
/// The directory, or `None` when no environment variable names a base.
///
/// # Errors
///
/// When the configured directory names a share or a device.
pub fn cache_dir_in(name: &str, subdir: &str, label: &str) -> Result<Option<PathBuf>, String> {
    cache_dir_with(&process, name, subdir, label)
}

/// Returns the directory one borer cache lives in as `env` gives it ([`cache_dir_in`]).
///
/// # Arguments
///
/// * `env` - The environment.
/// * `name` - The environment variable that names the directory.
/// * `subdir` - The cache's folder under the platform's `borer` folder.
/// * `label` - What a refusal of the default directory calls it.
///
/// # Errors
///
/// When the configured directory names a share or a device.
fn cache_dir_with(
    env: Env<'_>,
    name: &str,
    subdir: &str,
    label: &str,
) -> Result<Option<PathBuf>, String> {
    let found = match var(env, name) {
        Some(dir) => Some((PathBuf::from(dir), name)),
        None => base(env, &["LOCALAPPDATA", "XDG_CACHE_HOME"], &[".cache"])
            .map(|b| (b.join("borer").join(subdir), label)),
    };
    let Some((dir, from)) = found else {
        return Ok(None);
    };
    if let Some(why) = unusable_path(&dir) {
        return Err(format!("{from}: {why}"));
    }
    Ok(Some(dir))
}

/// Returns one borer cache's directory for a call that reads or writes there
/// ([`cache_dir_in`]).
///
/// # Arguments
///
/// * `name` - The environment variable that names the directory.
/// * `subdir` - The cache's folder under the platform's `borer` folder.
/// * `label` - What a refusal of the default directory calls it.
///
/// # Errors
///
/// When no environment variable names a base, or the configured directory names a share
/// or a device.
pub fn require_cache_dir_in(name: &str, subdir: &str, label: &str) -> Result<PathBuf, String> {
    cache_dir_in(name, subdir, label)?.ok_or_else(|| {
        format!("no cache directory: set {name}, LOCALAPPDATA, XDG_CACHE_HOME or HOME")
    })
}

/// Returns the symbol cache a binary's PDB is looked for in: `$BORER_SYMCACHE`, else
/// `borer/symsrv` under [`cache_base`].
///
/// # Returns
///
/// The directory, or `None` when no environment variable names a base.
///
/// # Errors
///
/// When the configured directory names a share or a device.
pub fn symbol_cache() -> Result<Option<PathBuf>, String> {
    cache_dir_in(SYMCACHE_ENV, "symsrv", "the symbol cache")
}

#[cfg(test)]
mod tests {
    use std::ffi::OsString;
    use std::path::{Path, PathBuf};

    use super::{cache_dir_with, dirs_in};

    /// Returns an environment holding `vars`, every other variable unset.
    fn env(vars: &[(&str, &str)]) -> impl Fn(&str) -> Option<OsString> {
        let vars: Vec<(String, OsString)> = vars
            .iter()
            .map(|(k, v)| ((*k).to_owned(), OsString::from(v)))
            .collect();
        move |name| vars.iter().find(|(k, _)| k == name).map(|(_, v)| v.clone())
    }

    /// An empty base variable counts as unset, so no directory comes out relative.
    ///
    /// An empty `APPDATA` falls through to `$HOME`, an empty `LOCALAPPDATA` and
    /// `BORER_SYMCACHE` to `$XDG_CACHE_HOME`; an empty `BORER_PACK_DIRS` still lists no
    /// directories.
    ///
    /// # Panics
    ///
    /// Panics if an empty base variable is read as a directory, or an empty
    /// `BORER_PACK_DIRS` lists any.
    #[test]
    fn empty_variables_count_as_unset() {
        let root = if cfg!(windows) { r"C:\h" } else { "/h" };
        let base = [
            ("APPDATA", ""),
            ("LOCALAPPDATA", ""),
            ("BORER_SYMCACHE", ""),
            ("XDG_CACHE_HOME", root),
            ("HOME", root),
        ];
        let env = env(&base);
        let dirs = dirs_in(&env, None);
        let home = Path::new(root).join(".config").join("borer").join("packs");
        assert_eq!(dirs, [home]);
        let unset = [base.as_slice(), &[("BORER_PACK_DIRS", "")]].concat();
        let off = self::env(&unset);
        assert!(dirs_in(&off, None).is_empty());
        let cache = cache_dir_with(&env, "BORER_SYMCACHE", "symsrv", "the symbol cache");
        let want: PathBuf = [root, "borer", "symsrv"].iter().collect();
        assert_eq!(cache, Ok(Some(want)));
        assert!(
            dirs.iter()
                .chain(cache.iter().flatten())
                .all(|d| d.is_absolute())
        );
    }
}
