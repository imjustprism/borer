//! `borer update` and the outdated-version notice.
//!
//! The latest release is the tag GitHub's `/releases/latest` redirects to.
//! `update` downloads that release's archive for this machine, checks it
//! against the release's `SHA256SUMS`, unpacks it with `tar` and puts the
//! new binary where this one runs: on Windows by moving the running file
//! aside first (Windows lets a running executable be renamed, not
//! overwritten), elsewhere by renaming the new file over it.
//!
//! The notice is a once-a-day check that a command line run starts as a
//! detached copy of this binary: its answer is kept in the cache, and a
//! newer release the cache names is printed on stderr after the command's
//! own output. It never delays a command and never runs for the MCP
//! server. `BORER_NO_UPDATE_CHECK=1`
//! turns it off, and it is skipped where nobody reads the notice: with `CI`
//! set, or stderr not a terminal (a script, a pipe).
//!
//! A binary a package manager installed (Homebrew, Scoop, npm, cargo, pipx,
//! uv or pip) is never replaced: `update` and the notice name that
//! manager's own command instead.
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
const CHECK_EVERY: Duration = Duration::from_hours(24);

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

/// The command that updates this binary when a package manager installed it.
///
/// It is read from where the binary lives: Homebrew's cellar, a Scoop app,
/// an npx cache or a global or project npm package, cargo's bin folder
/// (`CARGO_HOME`'s when set), a pipx or uv tool, or a wheel (a
/// `borer-*.dist-info` folder beside the scripts folder it was put in).
///
/// # Arguments
///
/// * `exe` - The running binary, its links resolved.
/// * `cargo_home` - `CARGO_HOME`, when set, its links resolved.
///
/// # Returns
///
/// The command, naming the project or Python environment that owns the
/// binary where the plain command could update another copy, or `None` for
/// a binary nothing manages, which `borer update` replaces itself.
fn manager(exe: &Path, cargo_home: Option<&Path>) -> Option<String> {
    let norm = |p: &Path| p.to_string_lossy().replace('\\', "/").to_ascii_lowercase();
    let path = norm(exe);
    let has = |part: &str| path.contains(part);
    let in_cargo = cargo_home.is_some_and(|home| path.starts_with(&format!("{}/bin/", norm(home))));
    let found = if has("/cellar/") || has("/linuxbrew/") {
        "brew upgrade borer"
    } else if has("/scoop/apps/") {
        "scoop update borer"
    } else if has("/_npx/") {
        "npx -y @imjustprism/borer@latest"
    } else if has("/npm/node_modules/") || has("/lib/node_modules/") {
        "npm install -g @imjustprism/borer@latest"
    } else if has("/node_modules/") {
        let project = exe
            .ancestors()
            .find(|a| a.file_name().is_some_and(|n| n == "node_modules"))
            .and_then(Path::parent)?;
        return Some(format!(
            "npm install @imjustprism/borer@latest --prefix \"{}\"",
            shown(project)
        ));
    } else if in_cargo || has("/.cargo/bin/") {
        "cargo install borer"
    } else if has("/pipx/") {
        "pipx upgrade borer"
    } else if has("/uv/tools/") {
        "uv tool upgrade borer"
    } else if from_wheel(exe) {
        let python = exe.with_file_name(if cfg!(windows) {
            "python.exe"
        } else {
            "python"
        });
        if python.exists() {
            return Some(format!("{} -m pip install -U borer", program(&python)));
        }
        "pip install -U borer"
    } else {
        return None;
    };
    Some(found.to_owned())
}

/// A program's path as the first word of a command a person pastes.
///
/// It is bare when it has no space, so any shell runs it, else quoted, and
/// on Windows behind PowerShell's `&`, which a quoted program needs there.
///
/// # Arguments
///
/// * `path` - The program.
fn program(path: &Path) -> String {
    let text = shown(path);
    match (text.contains(' '), cfg!(windows)) {
        (false, _) => text,
        (true, true) => format!("& \"{text}\""),
        (true, false) => format!("\"{text}\""),
    }
}

/// A path as a person types it, without the `\\?\` prefix Windows puts on
/// a resolved one.
///
/// # Arguments
///
/// * `path` - The path.
fn shown(path: &Path) -> String {
    let text = path.display().to_string();
    text.strip_prefix(r"\\?\")
        .map_or_else(|| text.clone(), str::to_owned)
}

/// Whether a wheel put this binary where it runs: its scripts folder sits
/// beside a `site-packages` holding a `borer-*.dist-info`.
///
/// # Arguments
///
/// * `exe` - The running binary.
fn from_wheel(exe: &Path) -> bool {
    let Some(root) = exe.parent().and_then(Path::parent) else {
        return false;
    };
    let lib = |name: &str| root.join(name).read_dir().into_iter().flatten().flatten();
    let mut sites = vec![
        root.join("site-packages"),
        root.join("Lib").join("site-packages"),
    ];
    sites.extend(lib("lib").map(|d| d.path().join("site-packages")));
    sites.iter().any(|site| {
        site.read_dir().into_iter().flatten().flatten().any(|e| {
            let name = e.file_name();
            let name = name.to_string_lossy();
            name.starts_with("borer-") && name.ends_with(".dist-info")
        })
    })
}

/// `CARGO_HOME`, where cargo installs binaries when it is set, with its
/// links resolved as the running binary's are.
fn cargo_home() -> Option<PathBuf> {
    let home = PathBuf::from(std::env::var_os("CARGO_HOME")?);
    Some(std::fs::canonicalize(&home).unwrap_or(home))
}

/// The running binary with its links resolved, so a package manager's
/// link (`/opt/homebrew/bin/borer`) reads as the file it points at.
fn running_exe() -> Option<PathBuf> {
    let exe = std::env::current_exe().ok()?;
    Some(std::fs::canonicalize(&exe).unwrap_or(exe))
}

/// `borer update [--check]`: says whether a newer release is out.
///
/// Without `--check` it installs the release over this binary; a binary a
/// package manager installed is left to it, and the report names its
/// command.
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
    if let Some(cmd) = running_exe().and_then(|exe| manager(&exe, cargo_home().as_deref())) {
        return Ok(format!(
            "borer {shown} is out (this is {VERSION}); a package manager installed this one, so `{cmd}` updates it\n"
        ));
    }
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

/// The environment variable that starts this binary as the daily check
/// ([`refresh`]) instead of a command.
pub(crate) const REFRESH: &str = "BORER_UPDATE_REFRESH";

/// The daily check for a command line run.
///
/// The last kept answer is read now, so the notice costs a file read. When
/// that answer is older than a day, or there is none, a detached copy of
/// this binary ([`REFRESH`]) asks GitHub and keeps the answer for the next
/// run: a thread would die with a quick command before the answer came
/// back, and the command never waits for it. The day's check is claimed
/// in the cache before the copy starts, so commands run while it is out
/// read the answer as fresh and start no second one.
///
/// # Returns
///
/// The line to print after the command when a newer release is out, or
/// `None` when this build is current, nothing is known yet, or the check
/// is turned off or nobody would read it ([`check_wanted`]).
pub(crate) fn check() -> Option<String> {
    let terminal = std::io::IsTerminal::is_terminal(&std::io::stderr());
    if !check_wanted(
        std::env::var(OPT_OUT).ok().as_deref(),
        std::env::var_os("CI").is_some(),
        terminal,
    ) {
        return None;
    }
    let kept = recalled();
    if !kept.as_ref().is_some_and(|(_, fresh)| *fresh) && claim_file().is_some_and(|f| claim(&f)) {
        remember(kept.as_ref().map_or("none", |(tag, _)| tag.as_str()));
        spawn_refresh();
    }
    let (tag, _) = kept?;
    is_newer(&tag).then(|| {
        let shown = tag.trim_start_matches('v');
        let cmd = running_exe()
            .and_then(|exe| manager(&exe, cargo_home().as_deref()))
            .unwrap_or_else(|| "borer update".to_owned());
        format!("borer {shown} is out (this is {VERSION}); run `{cmd}`")
    })
}

/// Starts this binary again as the daily check, detached from the command:
/// no standard handles shared, and on Windows no console window.
///
/// A thread waits on it, so a command that outlives it reaps it; a quick command
/// just exits.
fn spawn_refresh() {
    let Ok(exe) = std::env::current_exe() else {
        return;
    };
    let mut cmd = Command::new(exe);
    cmd.env(REFRESH, "1")
        .stdin(std::process::Stdio::null())
        .stdout(std::process::Stdio::null())
        .stderr(std::process::Stdio::null());
    #[cfg(windows)]
    {
        use std::os::windows::process::CommandExt as _;
        /// `CREATE_NO_WINDOW`: a console of its own that never shows.
        const NO_WINDOW: u32 = 0x0800_0000;
        cmd.creation_flags(NO_WINDOW);
    }
    if let Ok(mut child) = cmd.spawn() {
        std::thread::spawn(move || child.wait());
    }
}

/// The file a command makes to start the daily check of the current
/// window of [`CHECK_EVERY`]: one name per window, so a check that never
/// finished holds its window alone and the next window tries again.
fn claim_file() -> Option<PathBuf> {
    let window = now_secs() / CHECK_EVERY.as_secs();
    Some(check_file()?.with_file_name(format!("latest-release.{window}.claim")))
}

/// Claims starting the daily check, across every process at once.
///
/// The file is made only if it is not there, which the system does for one
/// caller alone, so commands started together start one check between them.
///
/// # Arguments
///
/// * `file` - The claim's file ([`claim_file`]).
///
/// # Returns
///
/// True for the one caller that made the file.
fn claim(file: &Path) -> bool {
    if let Some(dir) = file.parent() {
        let _ = std::fs::create_dir_all(dir);
    }
    std::fs::OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(file)
        .is_ok()
}

/// The daily check itself, run by the detached copy [`spawn_refresh`]
/// starts: asks GitHub for the latest tag and keeps it.
///
/// A failed check keeps the last known tag with the new time, so an
/// offline machine asks once a day, not on every command. The claims that
/// started checks ([`claim_file`]) go once the answer is kept.
pub(crate) fn refresh() {
    let tag = latest_tag(15)
        .ok()
        .or_else(|| recalled().map(|(tag, _)| tag))
        .unwrap_or_else(|| "none".to_owned());
    remember(&tag);
    let claims = check_file().and_then(|f| Some(f.parent()?.read_dir().ok()?.flatten()));
    for found in claims.into_iter().flatten() {
        let name = found.file_name();
        let name = name.to_string_lossy();
        if name.starts_with("latest-release.") && name.ends_with(".claim") {
            let _ = std::fs::remove_file(found.path());
        }
    }
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

    /// Commands racing to start the daily check start it once: of eight
    /// claims made together, one holds.
    ///
    /// # Panics
    ///
    /// When no claim or more than one holds.
    #[test]
    fn one_of_many_racing_commands_claims_the_check() {
        let dir = std::env::temp_dir().join(format!("borer-claim-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        let file = dir.join("latest-release.claim");
        let held = std::thread::scope(|s| {
            let racers: Vec<_> = (0..8).map(|_| s.spawn(|| claim(&file))).collect();
            racers
                .into_iter()
                .map(|r| r.join().unwrap_or(false))
                .filter(|&held| held)
                .count()
        });
        assert_eq!(held, 1);
        assert!(!claim(&file), "a held claim stays held");
        let _ = std::fs::remove_dir_all(&dir);
    }

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

    /// A binary under a package manager's folder names that manager's
    /// update command, a wheel's binary is told by the `dist-info` beside
    /// its scripts folder, and a binary anywhere else names none.
    ///
    /// # Panics
    ///
    /// When a path is read as the wrong manager.
    #[test]
    fn a_package_managers_binary_names_its_update_command() {
        let cases = [
            (
                "/opt/homebrew/Cellar/borer/0.2.5/bin/borer",
                Some("brew upgrade borer"),
            ),
            ("/opt/homebrew/opt/other/borer", None),
            (
                r"C:\Users\a\scoop\apps\borer\current\borer.exe",
                Some("scoop update borer"),
            ),
            (
                "/home/a/.npm/_npx/1f2e/node_modules/@imjustprism/borer-linux-x64/bin/borer",
                Some("npx -y @imjustprism/borer@latest"),
            ),
            (
                "/usr/lib/node_modules/@imjustprism/borer-linux-x64/bin/borer",
                Some("npm install -g @imjustprism/borer@latest"),
            ),
            (
                r"C:\Users\a\AppData\Roaming\npm\node_modules\@imjustprism\borer-win32-x64\bin\borer.exe",
                Some("npm install -g @imjustprism/borer@latest"),
            ),
            (
                "/home/a/proj/node_modules/@imjustprism/borer-linux-x64/bin/borer",
                Some("npm install @imjustprism/borer@latest --prefix \"/home/a/proj\""),
            ),
            ("/home/a/.cargo/bin/borer", Some("cargo install borer")),
            (
                "/home/a/.local/pipx/venvs/borer/bin/borer",
                Some("pipx upgrade borer"),
            ),
            (
                "/home/a/.local/share/uv/tools/borer/bin/borer",
                Some("uv tool upgrade borer"),
            ),
            ("/home/a/bin/borer", None),
        ];
        for (path, want) in cases {
            assert_eq!(manager(Path::new(path), None).as_deref(), want, "{path}");
        }
        let home = Path::new("/opt/cargo");
        assert_eq!(
            manager(Path::new("/opt/cargo/bin/borer"), Some(home)).as_deref(),
            Some("cargo install borer")
        );
        assert_eq!(manager(Path::new("/opt/cargo/bin/borer"), None), None);
        let venv = std::env::temp_dir().join(format!("borer-wheel-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&venv);
        let site = venv.join("Lib").join("site-packages");
        std::fs::create_dir_all(site.join("borer-0.2.5.dist-info")).expect("dist-info");
        std::fs::create_dir_all(venv.join("Scripts")).expect("scripts");
        let exe = venv.join("Scripts").join("borer.exe");
        assert_eq!(manager(&exe, None).as_deref(), Some("pip install -U borer"));
        let python = exe.with_file_name(if cfg!(windows) {
            "python.exe"
        } else {
            "python"
        });
        std::fs::write(&python, b"").expect("python");
        assert_eq!(
            manager(&exe, None),
            Some(format!("{} -m pip install -U borer", program(&python)))
        );
        std::fs::remove_dir_all(site.join("borer-0.2.5.dist-info")).expect("removed");
        assert_eq!(manager(&exe, None), None);
        let _ = std::fs::remove_dir_all(&venv);
    }

    /// A program path is bare without spaces and quoted with them, behind
    /// PowerShell's `&` on Windows.
    ///
    /// # Panics
    ///
    /// When a path is written another way.
    #[test]
    fn a_program_path_is_quoted_only_when_it_must_be() {
        assert_eq!(program(Path::new("/v/bin/python")), "/v/bin/python");
        let spaced = program(Path::new("/my env/bin/python"));
        let want = if cfg!(windows) {
            "& \"/my env/bin/python\""
        } else {
            "\"/my env/bin/python\""
        };
        assert_eq!(spaced, want);
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
