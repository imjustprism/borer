//! `borer doctor`: the local setup borer depends on, one line per item.
//!
//! This binary's version and the commit it was built from; the toolchain the
//! repository pins and the one that built the binary; the symbol-server
//! cache `fetch_pdb` lands PDBs in and whether the symbol server answers;
//! the cache the
//! decompilation indexes live in; and the `.mcp.json` that starts the
//! server. Nothing else is read, and the one network access is a connection
//! to the symbol server bounded by [`REACH_WAIT`], which `offline` skips.

use std::fmt::Write as _;
use std::net::{SocketAddr, TcpStream, ToSocketAddrs};
use std::path::{Path, PathBuf};
use std::sync::mpsc;
use std::time::Duration;

/// The symbol server's host, the one PDBs are fetched from.
const SYMBOL_HOST: &str = "msdl.microsoft.com";

/// The symbol server's port: HTTPS.
const SYMBOL_PORT: u16 = 443;

/// Longest the reachability check waits: for the name lookup, and again for
/// the connection.
const REACH_WAIT: Duration = Duration::from_secs(3);

/// The file an MCP host reads its servers from, in a project's directory.
const MCP_FILE: &str = ".mcp.json";

/// Most directories the search for [`MCP_FILE`] climbs from the working
/// directory.
const CLIMB_MAX: usize = 32;

/// Most entries of a cache directory counted.
const COUNT_MAX: usize = 100_000;

/// Whether the symbol server answered.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Reach {
    /// A connection was made.
    Reachable,
    /// The name did not resolve, or nothing answered within the wait.
    Unreachable,
    /// Not tried: the run was asked to stay offline.
    NotChecked,
}

/// Tries one connection to the symbol server, bounded by [`REACH_WAIT`] for
/// the name lookup and again for the connection.
///
/// The lookup runs on a thread of its own, since a resolver that hangs has
/// no timeout to give it; a lookup still running when the wait ends is left
/// to finish on its own.
///
/// # Returns
///
/// Whether a connection was made.
fn reach_symbol_server() -> Reach {
    let (tx, rx) = mpsc::channel::<Vec<SocketAddr>>();
    std::thread::spawn(move || {
        let found = (SYMBOL_HOST, SYMBOL_PORT)
            .to_socket_addrs()
            .map(Iterator::collect)
            .unwrap_or_default();
        tx.send(found).ok();
    });
    let addrs = rx.recv_timeout(REACH_WAIT).unwrap_or_default();
    if addrs
        .first()
        .is_some_and(|a| TcpStream::connect_timeout(a, REACH_WAIT).is_ok())
    {
        Reach::Reachable
    } else {
        Reach::Unreachable
    }
}

/// How many entries a directory holds, and the bytes the files among them
/// with an extension hold, counting at most [`COUNT_MAX`] entries.
///
/// # Arguments
///
/// * `dir` - The directory.
/// * `extension` - The extension of the files counted, `None` for every
///   entry.
///
/// # Returns
///
/// The count and the bytes, or `None` when the directory does not read.
fn tally(dir: &Path, extension: Option<&str>) -> Option<(usize, u64)> {
    let entries = std::fs::read_dir(dir).ok()?;
    let mut count = 0;
    let mut bytes = 0u64;
    for entry in entries.flatten().take(COUNT_MAX) {
        let path = entry.path();
        if extension.is_some_and(|x| path.extension().is_none_or(|e| e != x)) {
            continue;
        }
        count += 1;
        bytes = bytes.saturating_add(entry.metadata().map_or(0, |m| m.len()));
    }
    Some((count, bytes))
}

/// A byte count in the unit that reads best.
///
/// # Arguments
///
/// * `bytes` - The count.
fn size(bytes: u64) -> String {
    match bytes {
        0..1_024 => format!("{bytes} B"),
        1_024..1_048_576 => format!("{} KB", bytes / 1_024),
        _ => format!("{} MB", bytes / 1_048_576),
    }
}

/// The line naming this binary, its version and the commit it was built
/// from.
///
/// # Arguments
///
/// * `exe` - Where this binary is.
fn version_line(exe: &Path) -> String {
    format!(
        "version    borer {}, commit {} ({})",
        env!("CARGO_PKG_VERSION"),
        env!("BORER_COMMIT"),
        exe.display()
    )
}

/// The line naming the toolchain the repository pins and the compiler that
/// built this binary, and whether they differ.
///
/// # Arguments
///
/// * `pinned` - The channel `rust-toolchain.toml` names.
/// * `rustc` - The compiler's `rustc -V`.
fn toolchain_line(pinned: &str, rustc: &str) -> String {
    let agrees = rustc.split_whitespace().nth(1).is_some_and(|v| v == pinned);
    format!(
        "toolchain  the repository pins {pinned}; built by {rustc}{}",
        if agrees { "" } else { " (not the pinned one)" }
    )
}

/// The line naming the symbol-server cache and saying whether the symbol
/// server answered.
///
/// # Arguments
///
/// * `cache` - The cache directory a fetch lands in
///   ([`crate::symsrv::cache_dir`]), and whether the environment named
///   it; `None` when no variable names a base at all.
/// * `reach` - What the reachability check found.
fn symbols_line(cache: Option<(&Path, bool)>, reach: Reach) -> String {
    let Some((dir, named)) = cache else {
        return format!(
            "symbols    no cache directory: set {}, LOCALAPPDATA, XDG_CACHE_HOME or HOME",
            crate::symsrv::CACHE_ENV
        );
    };
    let source = if named {
        format!("from {}", crate::symsrv::CACHE_ENV)
    } else {
        format!("the default; {} sets it", crate::symsrv::CACHE_ENV)
    };
    let held = match tally(dir, None) {
        Some((n, _)) => format!("{n} PDB name{}", if n == 1 { "" } else { "s" }),
        None => "missing".to_owned(),
    };
    let server = match reach {
        Reach::Reachable => "reachable",
        Reach::Unreachable => "unreachable",
        Reach::NotChecked => "not checked (offline)",
    };
    format!(
        "symbols    cache {} ({source}): {held}; server {SYMBOL_HOST}:{SYMBOL_PORT} {server}",
        dir.display()
    )
}

/// The line naming the index cache and what it holds.
///
/// # Arguments
///
/// * `dir` - The cache directory, `None` when no environment variable
///   names a base for it.
fn index_line(dir: Option<&Path>) -> String {
    let Some(dir) = dir else {
        return "index      no cache directory: set BORER_CACHE_DIR, LOCALAPPDATA, XDG_CACHE_HOME or HOME".to_owned();
    };
    let held = match tally(dir, Some(borer::index::EXTENSION)) {
        Some((n, bytes)) => format!(
            "{n} index{}, {}",
            if n == 1 { "" } else { "es" },
            size(bytes)
        ),
        None => "missing; the first index made creates it".to_owned(),
    };
    format!("index      {}: {held}", dir.display())
}

/// Finds a program the way a host starts a command: a path as it stands,
/// relative to the configuration's directory, or a bare name on `PATH`,
/// with `.exe` added on Windows.
///
/// # Arguments
///
/// * `command` - The command as configured.
/// * `base` - The configuration's directory.
///
/// # Returns
///
/// The program, or `None` when nothing by that name exists.
fn find_program(command: &str, base: &Path) -> Option<PathBuf> {
    let with_exe = |p: PathBuf| {
        if p.is_file() {
            Some(p)
        } else if cfg!(windows) && p.extension().is_none() {
            Some(p.with_extension("exe")).filter(|q| q.is_file())
        } else {
            None
        }
    };
    let path = Path::new(command);
    if path.is_absolute() {
        return with_exe(path.to_path_buf());
    }
    if path.components().count() > 1 {
        return with_exe(base.join(path));
    }
    std::env::split_paths(&std::env::var_os("PATH")?).find_map(|d| with_exe(d.join(path)))
}

/// The line naming the `.mcp.json` above `start` and where its borer
/// servers point.
///
/// # Arguments
///
/// * `start` - Where the search starts: the working directory.
/// * `exe` - This binary, to say when a server is it.
fn mcp_line(start: &Path, exe: &Path) -> String {
    let Some(file) = start
        .ancestors()
        .take(CLIMB_MAX)
        .map(|d| d.join(MCP_FILE))
        .find(|f| f.is_file())
    else {
        return format!("mcp        no {MCP_FILE} in {} or above", start.display());
    };
    let config = std::fs::read_to_string(&file)
        .map_err(|e| e.to_string())
        .and_then(|t| serde_json::from_str::<serde_json::Value>(&t).map_err(|e| e.to_string()));
    let config = match config {
        Ok(c) => c,
        Err(why) => return format!("mcp        {} does not read: {why}", file.display()),
    };
    let base = file.parent().unwrap_or(start);
    let me = std::fs::canonicalize(exe).ok();
    let mut servers: Vec<String> = Vec::new();
    for (name, server) in config
        .get("mcpServers")
        .and_then(serde_json::Value::as_object)
        .into_iter()
        .flatten()
    {
        let Some(command) = server.get("command").and_then(serde_json::Value::as_str) else {
            continue;
        };
        let stem = Path::new(command)
            .file_stem()
            .map_or(String::new(), |s| s.to_string_lossy().to_lowercase());
        if !name.to_lowercase().contains("borer") && !stem.starts_with("borer") {
            continue;
        }
        let state = match find_program(command, base) {
            None => "missing".to_owned(),
            Some(p) if std::fs::canonicalize(&p).ok() == me && me.is_some() => {
                "exists, this binary".to_owned()
            }
            Some(_) => "exists".to_owned(),
        };
        servers.push(format!("{name} runs {command} ({state})"));
    }
    if servers.is_empty() {
        return format!("mcp        {} starts no borer server", file.display());
    }
    format!("mcp        {}: {}", file.display(), servers.join("; "))
}

/// The report: one line per item of the setup.
///
/// # Arguments
///
/// * `exe` - This binary.
/// * `cwd` - The working directory, where the search for `.mcp.json`
///   starts.
/// * `symcache` - The symbol-server cache and whether the environment
///   named it, `None` when no variable names a base.
/// * `index` - The index cache directory, if one is named.
/// * `reach` - Checks the symbol server.
pub(crate) fn report(
    exe: &Path,
    cwd: &Path,
    symcache: Option<(&Path, bool)>,
    index: Option<&Path>,
    reach: impl FnOnce() -> Reach,
) -> String {
    let mut out = String::new();
    for line in [
        version_line(exe),
        toolchain_line(env!("BORER_TOOLCHAIN"), env!("BORER_RUSTC")),
        symbols_line(symcache, reach()),
        index_line(index),
        mcp_line(cwd, exe),
    ] {
        let _ = writeln!(out, "{line}");
    }
    out
}

/// Checks the local setup and prints the report, the CLI's `doctor`.
///
/// # Arguments
///
/// * `offline` - Skip the symbol server's reachability check.
///
/// # Errors
///
/// When the working directory or this binary's path does not read.
pub(crate) fn doctor(offline: bool) -> anyhow::Result<String> {
    let exe = std::env::current_exe()?;
    let cwd = std::env::current_dir()?;
    let named = std::env::var_os(crate::symsrv::CACHE_ENV).is_some_and(|v| !v.is_empty());
    let symcache = crate::symsrv::cache_dir();
    let index = borer::index::cache_dir();
    Ok(report(
        &exe,
        &cwd,
        symcache.as_ref().map(|dir| (dir.as_path(), named)),
        index.as_deref(),
        || {
            if offline {
                Reach::NotChecked
            } else {
                reach_symbol_server()
            }
        },
    ))
}

#[cfg(test)]
mod tests {
    use std::path::Path;

    use super::{Reach, mcp_line, report, symbols_line, toolchain_line};

    /// A directory of its own under the temporary directory, emptied.
    ///
    /// # Panics
    ///
    /// When the directory cannot be made.
    fn scratch(name: &str) -> std::path::PathBuf {
        let dir = std::env::temp_dir().join(format!("borer_doctor_{name}_{}", std::process::id()));
        std::fs::remove_dir_all(&dir).ok();
        std::fs::create_dir_all(&dir).expect("a scratch directory");
        dir
    }

    /// The report has one line per item, in a fixed order, and runs the
    /// reachability check it is handed exactly once.
    ///
    /// # Panics
    ///
    /// When a line is missing, out of order, or the check runs otherwise.
    #[test]
    fn the_report_is_one_line_per_item() {
        let dir = scratch("report");
        let mut asked = 0;
        let cache = dir.join("symsrv");
        let out = report(
            Path::new("borer.exe"),
            &dir,
            Some((&cache, false)),
            Some(&dir),
            || {
                asked += 1;
                Reach::NotChecked
            },
        );
        assert_eq!(asked, 1);
        let labels: Vec<&str> = out
            .lines()
            .filter_map(|l| l.split_whitespace().next())
            .collect();
        assert_eq!(
            labels,
            ["version", "toolchain", "symbols", "index", "mcp"],
            "{out}"
        );
        assert!(out.contains("not checked (offline)"), "{out}");
        assert!(out.contains(": 0 indexes, 0 B"), "{out}");
        let no_cache = report(Path::new("borer.exe"), &dir, None, Some(&dir), || {
            Reach::NotChecked
        });
        assert!(
            no_cache.contains("symbols    no cache directory: set BORER_SYMCACHE"),
            "{no_cache}"
        );
        std::fs::remove_dir_all(&dir).ok();
    }

    /// The symbol cache says where it came from and whether it exists, and
    /// the toolchain line says when the compiler is not the pinned one.
    ///
    /// # Panics
    ///
    /// When a line says otherwise.
    #[test]
    fn the_cache_and_the_toolchain_say_what_they_are() {
        let dir = scratch("symbols");
        std::fs::create_dir_all(dir.join("kernel32.pdb")).expect("a cached name");
        let named = symbols_line(Some((&dir, true)), Reach::Reachable);
        assert!(
            named.contains("(from BORER_SYMCACHE): 1 PDB name;"),
            "{named}"
        );
        assert!(
            named.ends_with("msdl.microsoft.com:443 reachable"),
            "{named}"
        );
        let missing = symbols_line(Some((&dir.join("none"), false)), Reach::Unreachable);
        assert!(
            missing.contains("(the default; BORER_SYMCACHE sets it): missing;"),
            "{missing}"
        );
        assert!(
            !toolchain_line("1.96.1", "rustc 1.96.1 (abc 2026-01-01)").contains("not the pinned")
        );
        assert!(
            toolchain_line("1.96.1", "rustc 1.97.0 (abc 2026-01-01)")
                .ends_with("(not the pinned one)")
        );
        std::fs::remove_dir_all(&dir).ok();
    }

    /// The `.mcp.json` above the working directory is found, its borer
    /// server's program checked, and one that names a missing program said
    /// to be missing.
    ///
    /// # Panics
    ///
    /// When the file is not found or a program is misreported.
    #[test]
    fn the_mcp_file_above_is_found_and_its_program_checked() {
        let dir = scratch("mcp");
        let exe = std::env::current_exe().expect("the test binary");
        let config = serde_json::json!({
            "mcpServers": {
                "borer": { "command": exe.to_string_lossy() },
                "other": { "command": "node" },
                "borer-old": { "command": "gone/borer.exe" }
            }
        });
        std::fs::write(dir.join(".mcp.json"), config.to_string()).expect("written");
        let below = dir.join("a").join("b");
        std::fs::create_dir_all(&below).expect("made");
        let line = mcp_line(&below, &exe);
        assert!(line.contains("borer runs "), "{line}");
        assert!(line.contains("(exists, this binary)"), "{line}");
        assert!(
            line.contains("borer-old runs gone/borer.exe (missing)"),
            "{line}"
        );
        assert!(!line.contains("other"), "{line}");
        std::fs::remove_dir_all(&dir).ok();
        assert!(mcp_line(&below, &exe).starts_with("mcp        no .mcp.json in "));
    }
}
