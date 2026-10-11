//! The symbol-server client: the companion PDB a PE's debug record names,
//! fetched from a symbol server when it is not on disk, opt-in.
//!
//! Nothing here touches the network unless a caller asks: the `fetch_pdb`
//! tool and the `fetch-pdb` command are the only doors, and both say what
//! they would do before doing it. The protocol is one plain HTTPS GET,
//! `{server}/download/symbols/{name}/{guid+age}/{name}`, answered by the
//! public Microsoft store and by any store that speaks its layout.
//!
//! A download lands in the cache only after the engine's identity check
//! ([`borer_engine::pdb::identifies`]) confirms it states the loaded
//! image's GUID and age, so a wrong or hostile file is discarded, never
//! cached, never applied; the engine then finds the cached entry as the
//! last of its three candidate places on any later load that names the
//! cache root ([`borer_engine::program::Program`]).
//!
//! The fetch is `curl` run as a process, the one
//! `crates/borer-engine/examples/fnscore.rs` already shells out to: it
//! ships with Windows 10 1803 and later, and one bounded process beats a
//! TLS stack added to the dependency tree (rules: keep dependency surface
//! minimal). Its absence is a clean error, not a crash.
//!
//! The public store's PDBs are post-processed after linking and their
//! information stream carries an age past the one the image's `CodeView`
//! record states (an `ntdll` record age of 1 against a store file aged 4,
//! same GUID); the identity is the DBI stream's age, the one the linker
//! wrote, so they match the way a debugger matches them.

use borer_engine::pdb::{self, Record};
use std::path::{Path, PathBuf};

/// The symbol server fetched from when a call names no other.
pub(crate) const DEFAULT_SERVER: &str = "https://msdl.microsoft.com/download/symbols";

/// The environment variable naming the cache directory.
pub(crate) const CACHE_ENV: &str = "BORER_SYMCACHE";

/// A PDB file name longer than this is refused rather than fetched: the
/// widest a path component is on the filesystems the cache lives on.
const NAME_MAX: usize = 255;

/// Where fetched PDBs are cached.
///
/// `$BORER_SYMCACHE`, else the platform cache directory beside the
/// decompile index (`%LOCALAPPDATA%\borer\symsrv`,
/// `$XDG_CACHE_HOME/borer/symsrv`, `~/.cache/borer/symsrv`).
///
/// # Returns
///
/// The directory, or `None` when no environment variable names a base.
pub(crate) fn cache_dir() -> Option<PathBuf> {
    if let Ok(dir) = std::env::var(CACHE_ENV)
        && !dir.is_empty()
    {
        return Some(PathBuf::from(dir));
    }
    Some(borer::index::cache_base()?.join("borer").join("symsrv"))
}

/// The file name a record's PDB is cached and asked for.
///
/// The recorded path is bytes out of the image, so it can hold anything a
/// hostile linker wrote; only its final component is ever used, and a
/// component that is empty, `.` or `..`, longer than [`NAME_MAX`], or
/// holds a control character is refused outright: a refused name is told
/// to the caller, never guessed into a path or a URL.
///
/// # Arguments
///
/// * `recorded` - The path the debug record states.
///
/// # Returns
///
/// The final component, or `None` when there is none worth using.
fn sanitize_name(recorded: &str) -> Option<&str> {
    let name = recorded.rsplit(['/', '\\']).next().unwrap_or_default();
    (!name.is_empty()
        && !matches!(name, "." | "..")
        && name.len() <= NAME_MAX
        && !name.chars().any(char::is_control))
    .then_some(name)
}

/// The URL one PDB is fetched from.
///
/// # Arguments
///
/// * `server` - The store's base URL, `http(s)://host[:port][/path]`,
///   already holding the store's own path (`/download/symbols` for the
///   public one) the way a symbol-path entry is written.
/// * `name` - The PDB's file name, [`sanitize_name`]'s answer.
/// * `key` - The record's [`Record::symsrv_key`].
///
/// # Returns
///
/// `{server}/{name}/{key}/{name}`, or `None` when the server is not an
/// absolute `http` or `https` URL with a host (a bare word, a file path,
/// a scheme a store does not speak).
fn url(server: &str, name: &str, key: &str) -> Option<String> {
    let server = server.trim_end_matches('/');
    let rest = server
        .strip_prefix("https://")
        .or_else(|| server.strip_prefix("http://"))?;
    let host = rest.split('/').next().unwrap_or_default();
    (!host.is_empty() && !host.chars().any(char::is_whitespace))
        .then(|| format!("{server}/{name}/{key}/{name}"))
}

/// Where a record's PDB lands in the cache.
///
/// # Arguments
///
/// * `root` - The cache root.
/// * `name` - The PDB's file name, [`sanitize_name`]'s answer.
/// * `key` - The record's [`Record::symsrv_key`].
///
/// # Returns
///
/// `{root}/{name}/{key}/{name}`, the layout the store itself files under,
/// so a tool that shares the root agrees on what is where.
fn cache_path(root: &Path, name: &str, key: &str) -> PathBuf {
    root.join(name).join(key).join(name)
}

/// Fetches one URL into `dest` with `curl`, the process Windows ships.
///
/// `curl` is quiet but says why it failed (`-sS`), is bounded by a
/// connect and a total timeout, follows the store's redirects, and names
/// the store's own client so it is served the bytes the Microsoft tools
/// get.
///
/// # Arguments
///
/// * `address` - The URL.
/// * `dest` - The file to write.
///
/// # Errors
///
/// When `curl` does not start (most often: not installed) or exits
/// nonzero; the message carries `curl`'s own error line.
pub(crate) fn curl(address: &str, dest: &Path) -> Result<(), String> {
    let out = std::process::Command::new("curl")
        .args([
            "-sSfL",
            "--connect-timeout",
            "15",
            "--max-time",
            "600",
            "-A",
            "Microsoft-Symbol-Server/10.0.0.0",
            "-o",
        ])
        .arg(dest)
        .arg(address)
        .output()
        .map_err(|e| format!("curl does not run ({e}); Windows 10 1803+ ships it"))?;
    out.status.success().then_some(()).ok_or_else(|| {
        let said = String::from_utf8_lossy(&out.stderr);
        format!(
            "fetch failed: {}",
            said.lines()
                .find(|l| !l.trim().is_empty())
                .unwrap_or("no error text")
        )
    })
}

/// Fetches the companion PDB a record names into the cache, or says what
/// that would involve.
///
/// The order of events is the safety story: the cache is checked before
/// anything else (a hit never goes to the network), a download goes to a
/// `.download` sibling first, the engine's identity check reads that file,
/// and only one that names the loaded image's build is renamed into place;
/// anything else is deleted, so a wrong or hostile download never becomes
/// the cached PDB a later load would apply, and the directories made for it
/// go with it when they are left empty.
///
/// # Arguments
///
/// * `record` - The loaded image's debug record.
/// * `root` - The cache root ([`cache_dir`]).
/// * `server` - The symbol server's base URL.
/// * `dry_run` - Say what would happen, fetch nothing.
/// * `fetch` - The downloader ([`curl`] in production; a test hands in
///   bytes).
///
/// # Returns
///
/// The answer text: what a dry run would do, that the PDB is already
/// cached, or where a validated fetch landed and that loading applies it.
///
/// # Errors
///
/// When the record's path has no usable file name, the server is not an
/// URL, the fetch fails, or the download is not the image's build; each
/// message says what to change.
pub(crate) fn obtain(
    record: &Record,
    root: &Path,
    server: &str,
    dry_run: bool,
    fetch: impl FnOnce(&str, &Path) -> Result<(), String>,
) -> Result<String, String> {
    let name = sanitize_name(&record.path).ok_or_else(|| {
        format!(
            "the debug record's path '{}' names no usable pdb file",
            record.path
        )
    })?;
    let key = record.symsrv_key();
    let address = url(server, name, &key).ok_or_else(|| {
        format!(
            "server {} is not an absolute http(s) URL",
            borer_engine::text::quoted(server)
        )
    })?;
    let dest = cache_path(root, name, &key);
    if dest.is_file() {
        return Ok(format!(
            "already cached at {}; the next load applies it",
            dest.display()
        ));
    }
    if dry_run {
        return Ok(format!(
            "dry-run: would fetch {name} ({key}) from {address} into {}, kept only if its guid+age match this binary; pass dry_run=false to fetch",
            dest.display()
        ));
    }
    let dir = dest
        .parent()
        .ok_or_else(|| format!("the cache path {} names no directory", dest.display()))?;
    std::fs::create_dir_all(dir).map_err(|e| format!("making {}/: {e}", dir.display()))?;
    let mut partial = dest.as_os_str().to_os_string();
    partial.push(".download");
    let partial = PathBuf::from(partial);
    let discard = || {
        std::fs::remove_file(&partial).ok();
        std::fs::remove_dir(dir).ok();
        if let Some(up) = dir.parent() {
            std::fs::remove_dir(up).ok();
        }
    };
    if let Err(why) = fetch(&address, &partial) {
        discard();
        return Err(why);
    }
    let bytes = std::fs::read(&partial)
        .map_err(|e| format!("reading the download {}: {e}", partial.display()))?;
    let why = match pdb::identifies(&bytes, record) {
        Some(true) => None,
        Some(false) => Some("another build's pdb (its guid+age are not this binary's)"),
        None => Some("no pdb a parser reads"),
    };
    if let Some(why) = why {
        discard();
        return Err(format!("the downloaded {name} is {why}: discarded"));
    }
    std::fs::rename(&partial, &dest)
        .map_err(|e| format!("moving the download into {}: {e}", dest.display()))?;
    Ok(format!(
        "cached {name} ({} bytes) at {}; the next load applies it",
        bytes.len(),
        dest.display()
    ))
}

#[cfg(test)]
mod tests {
    use super::{DEFAULT_SERVER, cache_path, obtain, sanitize_name, url};
    use borer_engine::program::Program;
    use std::path::{Path, PathBuf};

    /// A directory of its own under the temporary directory, emptied.
    ///
    /// # Panics
    ///
    /// When the directory cannot be made.
    fn scratch(name: &str) -> PathBuf {
        let dir = std::env::temp_dir().join(format!("borer_symsrv_{name}_{}", std::process::id()));
        std::fs::remove_dir_all(&dir).ok();
        std::fs::create_dir_all(&dir).expect("a scratch directory");
        dir
    }

    /// The URL spells the store's own layout, and a server that is not an
    /// absolute http(s) URL with a host is refused.
    ///
    /// # Panics
    ///
    /// When the spelled URL differs or a nonsense server is accepted.
    #[test]
    fn the_url_is_the_stores_own_shape() {
        assert_eq!(
            url(DEFAULT_SERVER, "app.pdb", "KEY1").as_deref(),
            Some("https://msdl.microsoft.com/download/symbols/app.pdb/KEY1/app.pdb")
        );
        // A trailing slash is fine, and a plain-http local mirror spells
        // its own path, so a test against a local store works.
        assert_eq!(
            url("http://127.0.0.1:8000/symbols/", "a.pdb", "K").as_deref(),
            Some("http://127.0.0.1:8000/symbols/a.pdb/K/a.pdb")
        );
        for nonsense in ["msdl", "ftp://x", "https://", "//host", "https://a b/"] {
            assert!(url(nonsense, "a.pdb", "K").is_none(), "{nonsense}");
        }
    }

    /// A recorded path names only its final component, and a name that
    /// could travel is refused.
    ///
    /// # Panics
    ///
    /// When a traversal survives or a usable name is refused.
    #[test]
    fn a_recorded_path_names_only_its_final_component() {
        assert_eq!(sanitize_name(r"C:\b\app.pdb"), Some("app.pdb"));
        assert_eq!(sanitize_name("a/../../app.pdb"), Some("app.pdb"));
        assert_eq!(sanitize_name("..\\app.pdb"), Some("app.pdb"));
        assert_eq!(sanitize_name(""), None);
        assert_eq!(sanitize_name(".."), None);
        assert_eq!(sanitize_name("x/.."), None);
        assert_eq!(sanitize_name("x/."), None);
        assert_eq!(sanitize_name(&"n".repeat(256)), None);
        assert_eq!(sanitize_name("a\u{7}.pdb"), None);
        let root = Path::new("cache");
        assert_eq!(
            cache_path(root, "app.pdb", "K1"),
            PathBuf::from("cache")
                .join("app.pdb")
                .join("K1")
                .join("app.pdb")
        );
    }

    /// A dry run states the URL and the destination and never fetches.
    ///
    /// # Panics
    ///
    /// When the fetcher runs or the dry-run text misses its facts.
    #[test]
    fn a_dry_run_fetches_nothing_and_says_so() {
        let record = borer_engine::pdb::Record {
            path: r"C:\b\app.pdb".to_owned(),
            guid: [1; 16],
            age: 2,
        };
        let root = scratch("dry");
        let said = obtain(&record, &root, DEFAULT_SERVER, true, |_, _| {
            panic!("a dry run never fetches")
        })
        .expect("a dry run answers");
        assert!(said.starts_with("dry-run: would fetch app.pdb ("), "{said}");
        assert!(
            said.contains("https://msdl.microsoft.com/download/symbols/app.pdb/"),
            "{said}"
        );
        assert!(said.ends_with("pass dry_run=false to fetch"), "{said}");
        assert!(!root.join("app.pdb").exists(), "{said}");
        std::fs::remove_dir_all(&root).ok();
    }

    /// A nonsense server or a nameless record is refused before any
    /// fetch, and a cache hit never goes to the network.
    ///
    /// # Panics
    ///
    /// When a hostile input is accepted or a hit fetches.
    #[test]
    fn hostile_inputs_and_cache_hits_never_fetch() {
        let record = borer_engine::pdb::Record {
            path: r"C:\b\app.pdb".to_owned(),
            guid: [1; 16],
            age: 2,
        };
        let root = scratch("refuse");
        let no_server = obtain(&record, &root, "not a url", false, |_, _| {
            panic!("a refused server never fetches")
        })
        .expect_err("a nonsense server is refused");
        assert!(
            no_server.contains("not an absolute http(s) URL"),
            "{no_server}"
        );
        let mut hostile = record.clone();
        hostile.path = "..".to_owned();
        let no_name = obtain(&hostile, &root, DEFAULT_SERVER, false, |_, _| {
            panic!("a refused name never fetches")
        })
        .expect_err("a traversal path is refused");
        assert!(no_name.contains("names no usable pdb file"), "{no_name}");
        // The hit: a cached file answers without the fetcher ever running.
        let dest = root
            .join("app.pdb")
            .join(record.symsrv_key())
            .join("app.pdb");
        std::fs::create_dir_all(dest.parent().expect("a key directory")).expect("made");
        std::fs::write(&dest, b"an earlier fetch").expect("written");
        let hit = obtain(&record, &root, DEFAULT_SERVER, false, |_, _| {
            panic!("a cache hit never fetches")
        })
        .expect("a hit answers");
        assert!(hit.starts_with("already cached at "), "{hit}");
        std::fs::remove_dir_all(&root).ok();
    }

    /// A download that is not the image's build is discarded, and only a
    /// matching one lands in the cache and applies on the next load.
    ///
    /// The running test binary's own PDB is the one file guaranteed to
    /// both parse and match its record, so the full gate is exercised on
    /// real bytes: a wrong download is deleted before it can pose as the
    /// cached PDB, the matching one is renamed into place, a second
    /// obtains answers from the cache, and a load that names the cache
    /// root applies what the first load without it could not find. A
    /// build without a PDB on disk (a release profile) has nothing to
    /// fetch, and nothing is asserted.
    ///
    /// # Panics
    ///
    /// When a discarded download survives, or a matching one does not land
    /// and apply.
    #[test]
    fn a_download_lands_only_when_it_names_this_build() {
        let exe = std::env::current_exe().expect("the test binary has a path");
        let bare = Program::load_with(&exe, false).expect("the test binary loads");
        let Some(record) = bare.pdb_record.clone() else {
            return;
        };
        let Some(name) = Path::new(&record.path).file_name() else {
            return;
        };
        let Some(own) = exe
            .parent()
            .map(|d| d.join(name))
            .filter(|p| p.is_file())
            .and_then(|p| std::fs::read(p).ok())
        else {
            return;
        };
        assert!(bare.pdb.is_none(), "a pdb=false load applies nothing");
        let root = scratch("gate");
        // The wrong download: bytes that are no PDB are refused and
        // deleted, never renamed into the cache.
        let wrong = obtain(&record, &root, DEFAULT_SERVER, false, |_, dest| {
            std::fs::write(dest, b"not a pdb at all").map_err(|e| e.to_string())
        })
        .expect_err("a non-pdb download is refused");
        assert!(wrong.contains("discarded"), "{wrong}");
        assert!(wrong.contains("no pdb a parser reads"), "{wrong}");
        assert!(
            !root.join(name).exists(),
            "a discarded download left its directories"
        );
        let key = record.symsrv_key();
        let dest = root.join(name).join(&key).join(name);
        assert!(!dest.exists(), "a discarded download left {dest:?}");
        assert!(
            !root
                .join(name)
                .join(&key)
                .join(format!("{}.download", name.to_string_lossy()))
                .exists(),
            "the partial download survived"
        );
        // The matching download: the fake fetcher hands over the real
        // PDB's bytes, the gate accepts them, and the cache holds the
        // file a load then applies.
        let landed = obtain(&record, &root, DEFAULT_SERVER, false, |_, dest| {
            std::fs::write(dest, &own).map_err(|e| e.to_string())
        })
        .expect("the matching download lands");
        assert!(landed.starts_with("cached "), "{landed}");
        assert_eq!(std::fs::read(&dest).expect("the cached pdb"), own);
        let again = obtain(&record, &root, DEFAULT_SERVER, false, |_, _| {
            panic!("a cache hit never fetches")
        })
        .expect("the second call answers");
        assert!(again.starts_with("already cached at "), "{again}");
        let with = Program::load_with_symsrv(&exe, true, Some(&root)).expect("it loads again");
        assert!(
            matches!(with.pdb, Some(borer_engine::pdb::Outcome::Applied { .. })),
            "the cached pdb did not apply: {:?}",
            with.pdb
        );
        std::fs::remove_dir_all(&root).ok();
    }
}
