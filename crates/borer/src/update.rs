//! `borer update` and the outdated-version notice.
//!
//! The latest release is the tag GitHub's `/releases/latest` redirects to.
//! `update` downloads that release's archive for this machine, checks it
//! against the release's `SHA256SUMS`, unpacks it with `tar` and puts the
//! new binary where this one runs: on Windows by moving the running file
//! aside first (Windows lets a running executable be renamed, not
//! overwritten), elsewhere by renaming the new file over it.
//!
//! The notice is a once-a-day check that a command line run makes in the
//! background: its answer is kept in the cache, and a newer release is
//! named on stderr after the command's own output. It never delays a
//! command and never runs for the MCP server. `BORER_NO_UPDATE_CHECK=1`
//! turns it off, and it is skipped where nobody reads the notice: with `CI`
//! set, or stderr not a terminal (a script, a pipe).
//!
//! Downloads are `curl` run as a process, as [`crate::symsrv`] fetches
//! PDBs, and unpacking is `tar`; Windows 10 1803 and later ship both.

use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::{Duration, SystemTime, UNIX_EPOCH};

use anyhow::{Context, bail};

/// The repository releases are published from.
const REPO: &str = "imjustprism/borer";

/// This build's version.
const VERSION: &str = env!("CARGO_PKG_VERSION");

/// The environment variable that turns the daily check off when set to `1`.
const OPT_OUT: &str = "BORER_NO_UPDATE_CHECK";

/// How long a checked answer is trusted before the next check.
const CHECK_EVERY: Duration = Duration::from_secs(24 * 60 * 60);

/// The release archive's target triple and extension for this machine, as
/// the release workflow names them.
///
/// # Returns
///
/// `None` on a machine no release is built for.
fn target() -> Option<(&'static str, &'static str)> {
    if cfg!(all(target_os = "windows", target_arch = "x86_64")) {
        Some(("x86_64-pc-windows-msvc", "zip"))
    } else if cfg!(all(target_os = "linux", target_arch = "x86_64")) {
        Some(("x86_64-unknown-linux-gnu", "tar.gz"))
    } else if cfg!(all(target_os = "macos", target_arch = "aarch64")) {
        Some(("aarch64-apple-darwin", "tar.gz"))
    } else if cfg!(all(target_os = "macos", target_arch = "x86_64")) {
        Some(("x86_64-apple-darwin", "tar.gz"))
    } else {
        None
    }
}

/// A version's three numbers, from `v0.1.0` or `0.1.0`.
///
/// # Arguments
///
/// * `text` - The version or tag.
///
/// # Returns
///
/// Major, minor and patch, or `None` when the text is not such a version.
fn parse_version(text: &str) -> Option<(u64, u64, u64)> {
    let core = text
        .trim()
        .trim_start_matches('v')
        .split(['-', '+'])
        .next()?;
    let mut parts = core.split('.');
    let major = parts.next()?.parse().ok()?;
    let minor = parts.next()?.parse().ok()?;
    let patch = parts.next()?.parse().ok()?;
    parts.next().is_none().then_some((major, minor, patch))
}

/// Whether `tag` names a release newer than this build.
///
/// # Arguments
///
/// * `tag` - The release's tag.
fn is_newer(tag: &str) -> bool {
    matches!((parse_version(tag), parse_version(VERSION)), (Some(theirs), Some(ours)) if theirs > ours)
}

/// The null device, where `curl` writes a body nobody reads.
const NULL: &str = if cfg!(windows) { "NUL" } else { "/dev/null" };

/// Runs `curl` with a user agent naming this build, bounded by `max_secs`.
///
/// # Arguments
///
/// * `max_secs` - The total time allowed, in seconds.
/// * `args` - What follows the common flags.
///
/// # Returns
///
/// What `curl` wrote to stdout.
///
/// # Errors
///
/// When `curl` does not start or exits nonzero; the message carries its
/// own error line.
fn curl(max_secs: u32, args: &[&str]) -> anyhow::Result<String> {
    let out = Command::new("curl")
        .args(["-sSfL", "--connect-timeout", "10", "--max-time"])
        .arg(max_secs.to_string())
        .args(["-A", &format!("borer/{VERSION}")])
        .args(args)
        .output()
        .context("curl does not run; Windows 10 1803 and later, macOS and Linux ship it")?;
    if !out.status.success() {
        let said = String::from_utf8_lossy(&out.stderr);
        bail!(
            "download failed: {}",
            said.lines()
                .find(|l| !l.trim().is_empty())
                .unwrap_or("no error text")
        );
    }
    Ok(String::from_utf8_lossy(&out.stdout).into_owned())
}

/// The latest release's tag: the last path component `/releases/latest`
/// redirects to.
///
/// # Arguments
///
/// * `max_secs` - The time allowed for the request, in seconds.
///
/// # Errors
///
/// When GitHub cannot be reached, or no release is published.
fn latest_tag(max_secs: u32) -> anyhow::Result<String> {
    let url = format!("https://github.com/{REPO}/releases/latest");
    let landed = curl(max_secs, &["-o", NULL, "-w", "%{url_effective}", &url])?;
    let tag = landed.trim().rsplit('/').next().unwrap_or_default();
    if tag.is_empty() || tag == "latest" || parse_version(tag).is_none() {
        bail!("no release is published yet");
    }
    Ok(tag.to_owned())
}

/// Lowercase hex of a SHA-256 digest.
///
/// # Arguments
///
/// * `bytes` - The data to hash.
fn sha256_hex(bytes: &[u8]) -> String {
    use std::fmt::Write as _;
    borer_engine::hashing::sha256(bytes)
        .iter()
        .fold(String::new(), |mut s, b| {
            let _ = write!(s, "{b:02x}");
            s
        })
}

/// The sum `SHA256SUMS` lists for `file`, in its `<hex>  <name>` or
/// `<hex> *<name>` form.
///
/// # Arguments
///
/// * `sums` - The `SHA256SUMS` text.
/// * `file` - The archive's file name.
fn listed_sum<'a>(sums: &'a str, file: &str) -> Option<&'a str> {
    sums.lines().find_map(|line| {
        let mut fields = line.split_whitespace();
        let hex = fields.next()?;
        let name = fields.next()?.trim_start_matches('*');
        (name == file).then_some(hex)
    })
}

/// Moves a freshly unpacked binary into the place of the running one.
///
/// # Arguments
///
/// * `new` - The new binary.
/// * `exe` - Where this binary runs from.
///
/// # Errors
///
/// When the folder cannot be written; the running binary is left as it
/// was.
fn replace(new: &Path, exe: &Path) -> anyhow::Result<()> {
    let dir = exe.parent().context("the running binary has no folder")?;
    let staged = dir.join(".borer.update");
    std::fs::copy(new, &staged).with_context(|| format!("writing {}", staged.display()))?;
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt as _;
        std::fs::set_permissions(&staged, std::fs::Permissions::from_mode(0o755))?;
    }
    if cfg!(windows) {
        let old = aside(exe);
        std::fs::rename(exe, &old).with_context(|| format!("moving {} aside", exe.display()))?;
        if let Err(e) = std::fs::rename(&staged, exe) {
            let _ = std::fs::rename(&old, exe);
            return Err(e).with_context(|| format!("writing {}", exe.display()));
        }
    } else {
        std::fs::rename(&staged, exe).with_context(|| format!("writing {}", exe.display()))?;
    }
    Ok(())
}

/// Where Windows keeps the binary an update replaced: the first of
/// `borer.old`, `borer.1.old`, `borer.2.old`, ... that is free or can be
/// removed.
///
/// A binary set aside by an earlier update may still run (an MCP client
/// keeps one open for its session), and Windows refuses to delete or
/// overwrite a running executable, so its name stays taken until that
/// process exits.
///
/// # Arguments
///
/// * `exe` - The running binary.
fn aside(exe: &Path) -> PathBuf {
    /// Set-aside names tried before giving up on finding a free one.
    const TRIES: u32 = 64;
    let free = |p: &Path| !p.exists() || std::fs::remove_file(p).is_ok();
    let first = exe.with_extension("old");
    if free(&first) {
        return first;
    }
    (1..TRIES)
        .map(|n| exe.with_extension(format!("{n}.old")))
        .find(|p| free(p))
        .unwrap_or(first)
}

/// `borer update [--check]`: says whether a newer release is out and,
/// without `--check`, installs it over this binary.
///
/// # Arguments
///
/// * `check_only` - Report only; change nothing.
///
/// # Returns
///
/// The report.
///
/// # Errors
///
/// When GitHub cannot be reached, the release has no build for this
/// machine, the download does not match its listed sum, or the binary's
/// folder cannot be written.
pub(crate) fn update(check_only: bool) -> anyhow::Result<String> {
    let exe = std::env::current_exe().context("cannot tell where this binary runs from")?;
    let _ = std::fs::remove_file(aside(&exe));
    let tag = latest_tag(30)?;
    remember(&tag);
    if !is_newer(&tag) {
        return Ok(format!("borer {VERSION} is the latest release\n"));
    }
    let shown = tag.trim_start_matches('v');
    if check_only {
        return Ok(format!(
            "borer {shown} is out (this is {VERSION}); `borer update` installs it\n"
        ));
    }
    let (triple, ext) =
        target().context("no release is built for this machine; build from source")?;
    let name = format!("borer-{tag}-{triple}");
    let base = format!("https://github.com/{REPO}/releases/download/{tag}");
    let work = std::env::temp_dir().join(format!("borer-update-{}", std::process::id()));
    std::fs::create_dir_all(&work)?;
    let result = (|| {
        let archive = work.join(format!("{name}.{ext}"));
        let path = archive.to_string_lossy().into_owned();
        curl(600, &["-o", &path, &format!("{base}/{name}.{ext}")])?;
        let sums = curl(60, &[&format!("{base}/SHA256SUMS")])?;
        let want = listed_sum(&sums, &format!("{name}.{ext}"))
            .with_context(|| format!("SHA256SUMS lists no {name}.{ext}"))?;
        let got = sha256_hex(&std::fs::read(&archive)?);
        if !got.eq_ignore_ascii_case(want) {
            bail!("{name}.{ext} does not match its listed SHA-256; nothing was changed");
        }
        let unpacked = Command::new("tar")
            .arg("-xf")
            .arg(&archive)
            .arg("-C")
            .arg(&work)
            .status()
            .context("tar does not run")?;
        if !unpacked.success() {
            bail!("tar could not unpack {name}.{ext}");
        }
        let new = work
            .join(&name)
            .join(if cfg!(windows) { "borer.exe" } else { "borer" });
        replace(&new, &exe)?;
        Ok(format!(
            "updated borer {VERSION} -> {shown} at {}\n",
            exe.display()
        ))
    })();
    let _ = std::fs::remove_dir_all(&work);
    result
}

/// Now, in seconds since the epoch: when the daily check ran.
///
/// The only reading of the clock here; no answer depends on it, only
/// whether the next run checks again.
fn now_secs() -> u64 {
    #[expect(
        clippy::disallowed_methods,
        reason = "the update check's age is about wall time; no analysis answer reads it"
    )]
    let now = SystemTime::now();
    now.duration_since(UNIX_EPOCH).map_or(0, |d| d.as_secs())
}

/// The file the daily check keeps its answer in: `<seconds> <tag>`.
fn check_file() -> Option<PathBuf> {
    Some(
        borer::index::cache_base()?
            .join("borer")
            .join("latest-release"),
    )
}

/// Keeps the latest tag, with now as the time it was checked.
///
/// # Arguments
///
/// * `tag` - The latest release's tag.
fn remember(tag: &str) {
    let Some(file) = check_file() else { return };
    let now = now_secs();
    if let Some(dir) = file.parent() {
        let _ = std::fs::create_dir_all(dir);
    }
    let _ = std::fs::write(file, format!("{now} {tag}\n"));
}

/// The last checked tag, and whether that check is still fresh.
fn recalled() -> Option<(String, bool)> {
    let text = std::fs::read_to_string(check_file()?).ok()?;
    let (when, tag) = text.trim().split_once(' ')?;
    let when: u64 = when.parse().ok()?;
    let age = Duration::from_secs(now_secs().saturating_sub(when));
    Some((tag.to_owned(), age < CHECK_EVERY))
}

/// Whether a command line run checks for a newer release.
///
/// # Arguments
///
/// * `opt_out` - The `BORER_NO_UPDATE_CHECK` value, `None` when unset.
/// * `ci` - Whether `CI` is set, as continuous integration sets it.
/// * `terminal` - Whether stderr, where the notice goes, is a terminal.
///
/// # Returns
///
/// True only for a person at a terminal who has not opted out.
fn check_wanted(opt_out: Option<&str>, ci: bool, terminal: bool) -> bool {
    opt_out != Some("1") && !ci && terminal
}

/// Starts the daily check for a command line run, in the background.
///
/// # Returns
///
/// A handle that [`notice`] reads once the command is done, or `None`
/// when the check is turned off or nobody would read it ([`check_wanted`]).
pub(crate) fn start_check() -> Option<std::thread::JoinHandle<Option<String>>> {
    let terminal = std::io::IsTerminal::is_terminal(&std::io::stderr());
    if !check_wanted(
        std::env::var(OPT_OUT).ok().as_deref(),
        std::env::var_os("CI").is_some(),
        terminal,
    ) {
        return None;
    }
    Some(std::thread::spawn(|| {
        if let Some((tag, true)) = recalled() {
            return Some(tag);
        }
        let tag = latest_tag(4).ok()?;
        remember(&tag);
        Some(tag)
    }))
}

/// The line to print after a command when a newer release is out.
///
/// It waits for nothing: a check still running is left to finish on its
/// own, and its answer is kept for the next run.
///
/// # Arguments
///
/// * `check` - The handle [`start_check`] returned.
///
/// # Returns
///
/// The notice, or `None` when this build is current or the answer is not in.
pub(crate) fn notice(check: std::thread::JoinHandle<Option<String>>) -> Option<String> {
    if !check.is_finished() {
        return None;
    }
    let tag = check.join().ok()??;
    is_newer(&tag).then(|| {
        let shown = tag.trim_start_matches('v');
        format!("borer {shown} is out (this is {VERSION}); run `borer update`")
    })
}

#[cfg(test)]
mod tests {
    /// The check runs for a person at a terminal, and not when opted out,
    /// under CI or with stderr redirected.
    ///
    /// # Panics
    ///
    /// When one of the four reads otherwise.
    #[test]
    fn the_check_runs_only_where_someone_reads_it() {
        assert!(check_wanted(None, false, true));
        assert!(check_wanted(Some("0"), false, true));
        assert!(!check_wanted(Some("1"), false, true));
        assert!(!check_wanted(None, true, true));
        assert!(!check_wanted(None, false, false));
    }

    use super::*;

    /// A set-aside name that cannot be removed, as a still-running earlier
    /// binary's cannot, is skipped for the next free one.
    ///
    /// # Panics
    ///
    /// When the name is not the next one.
    #[test]
    fn a_taken_aside_name_moves_to_the_next() {
        let dir = std::env::temp_dir().join(format!("borer-aside-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(dir.join("borer.old")).expect("dir");
        std::fs::write(dir.join("borer.1.old"), b"stale").expect("write");
        let exe = dir.join("borer.exe");
        assert_eq!(aside(&exe), dir.join("borer.1.old"));
        assert!(!dir.join("borer.1.old").exists());
        let _ = std::fs::remove_dir_all(&dir);
    }

    /// Tags parse to three numbers and order against this build.
    ///
    /// # Panics
    ///
    /// When it does not.
    #[test]
    fn versions_parse_and_compare() {
        assert_eq!(parse_version("v1.2.3"), Some((1, 2, 3)));
        assert_eq!(parse_version("0.10.0-beta.1"), Some((0, 10, 0)));
        assert_eq!(parse_version("latest"), None);
        assert_eq!(parse_version("1.2"), None);
        assert!(is_newer("v999.0.0"));
        assert!(!is_newer(&format!("v{VERSION}")));
        assert!(!is_newer("v0.0.1"));
    }

    /// `SHA256SUMS` lines are read with or without the binary-mode star.
    ///
    /// # Panics
    ///
    /// When it does not.
    #[test]
    fn sums_are_found_in_either_form() {
        let sums = "abc  borer-v1-x.zip\ndef *borer-v1-y.tar.gz\n";
        assert_eq!(listed_sum(sums, "borer-v1-x.zip"), Some("abc"));
        assert_eq!(listed_sum(sums, "borer-v1-y.tar.gz"), Some("def"));
        assert_eq!(listed_sum(sums, "borer-v1-z.zip"), None);
    }

    /// The digest of `abc` is the FIPS 180-2 one.
    ///
    /// # Panics
    ///
    /// When it does not.
    #[test]
    fn sha256_matches_a_known_digest() {
        assert_eq!(
            sha256_hex(b"abc"),
            "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
        );
    }
}
