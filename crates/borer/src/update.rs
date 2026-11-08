//! `borer update` and the outdated-version notice.
//!
//! The latest release is the tag GitHub's `/releases/latest` redirects to,
//! read from the redirect itself. `update` downloads that release's
//! archive for this machine, checks it against the release's `SHA256SUMS`,
//! unpacks it with `tar` and puts the new binary where this one runs: on
//! Windows by moving the running file aside first (Windows lets a running
//! executable be renamed, not overwritten), elsewhere by renaming the new
//! file over it.
//!
//! Every request retries a timeout or a transient answer within a bounded
//! time, and a timeout or a failed connection says what happened and what
//! to do. With a token in `GH_TOKEN` or `GITHUB_TOKEN`, `update` reads and
//! downloads the release through GitHub's API as that token's user, so
//! trouble that slows only unauthenticated requests does not stop an
//! update; github.com's own pages do not count a token. The token goes
//! only to the API's host, on `curl`'s stdin, never on its command line,
//! and the daily check below never sends it.
//!
//! On a terminal each step runs under a loading line ([`crate::term`]),
//! the download's showing how much of the archive has arrived, and leaves
//! a line saying how it ended; elsewhere nothing more is printed.
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

use std::io::Write as _;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
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

/// How long a request may wait to connect and for anything to arrive, in
/// seconds; also all a small request's try may take.
const ANSWER_SECS: u32 = 15;

/// All one try of the archive's download may take, in seconds.
const ARCHIVE_SECS: u32 = 600;

/// The retries `curl --retry` makes of a request that timed out or that
/// GitHub answered with a transient status (408, 429 or a 5xx).
const RETRIES: u32 = 2;

/// The seconds after a request's first try in which a retry may still
/// start (`curl --retry-max-time`).
const RETRY_WINDOW: u32 = 60;

/// The redirects [`fetch`] follows itself, where a request carrying the
/// token follows none.
const REDIRECTS: usize = 4;

/// The variables a GitHub token is read from, in the order `gh` reads them.
const TOKEN_VARS: [&str; 2] = ["GH_TOKEN", "GITHUB_TOKEN"];

/// The one host a token is sent to: github.com's own pages do not count
/// one.
const TOKEN_HOST: &str = "api.github.com";

/// A GitHub token from the environment.
struct Token {
    /// The variable it was read from.
    var: &'static str,
    /// The token itself: never an argument, never printed.
    value: String,
}

/// The token in `GH_TOKEN`, else in `GITHUB_TOKEN`.
fn token() -> Option<Token> {
    token_in(|var| std::env::var(var).ok())
}

/// The token in the first of [`TOKEN_VARS`] that holds one.
///
/// # Arguments
///
/// * `var` - Reads a variable; `None` when it is unset.
///
/// # Returns
///
/// `None` when none holds one: unset, empty, or holding a character no
/// token has, which as a header line could add a header of its own.
fn token_in(var: impl Fn(&str) -> Option<String>) -> Option<Token> {
    TOKEN_VARS.into_iter().find_map(|name| {
        let value = var(name)?.trim().to_owned();
        (!value.is_empty() && value.bytes().all(|b| b.is_ascii_graphic()))
            .then_some(Token { var: name, value })
    })
}

/// Whether `url` is an `https` URL on [`TOKEN_HOST`], the only requests a
/// token goes with.
///
/// # Arguments
///
/// * `url` - The URL.
fn to_api(url: &str) -> bool {
    url.strip_prefix("https://")
        .and_then(|rest| rest.split(['/', '?', '#']).next())
        .is_some_and(|host| host == TOKEN_HOST)
}

/// One run of `curl`.
struct Request<'a> {
    /// The URL.
    url: &'a str,
    /// The file the body goes to, with the URL a redirect names written to
    /// stdout; `None` sends the body to stdout.
    out: Option<&'a Path>,
    /// Whether `curl` follows redirects itself.
    follow: bool,
    /// All one try may take, in seconds.
    secs: u32,
    /// The `Accept` header, when `curl`'s own is not the one wanted.
    accept: Option<&'static str>,
    /// The file `curl` writes the response headers to as they arrive, for
    /// a download whose progress the loading line shows ([`watch`]).
    meter: Option<&'a Path>,
}

/// The `curl` command for a request and, when the token goes with it, the
/// header `curl` reads from its stdin.
///
/// Every request is quiet but says why it failed, fails on an HTTP error
/// status, and names this build as its client. It waits at most
/// [`ANSWER_SECS`] to connect and for anything to arrive, and `curl`
/// retries a timeout or a transient status [`RETRIES`] times while within
/// [`RETRY_WINDOW`]. The token goes only to [`TOKEN_HOST`] ([`to_api`]),
/// as an `Authorization` header read from stdin (`-H @-`), never as an
/// argument another user of the machine could read in its process list;
/// such a request follows no redirect itself, so the token never rides one
/// to another host. A request that follows none says so (`--no-location`),
/// so a `location` line in the user's curlrc cannot make it follow.
///
/// # Arguments
///
/// * `req` - The request.
/// * `token` - The token, when one is set.
///
/// # Returns
///
/// The command, its standard handles piped, and the header line to write
/// to its stdin.
fn curl_command(req: &Request<'_>, token: Option<&Token>) -> (Command, Option<String>) {
    let header = token
        .filter(|_| to_api(req.url))
        .map(|t| format!("Authorization: Bearer {}\n", t.value));
    let answer = ANSWER_SECS.to_string();
    let mut cmd = Command::new("curl");
    cmd.args(["-sSf", "--connect-timeout", &answer])
        .args(["--speed-limit", "1", "--speed-time", &answer])
        .args(["--max-time", &req.secs.to_string()])
        .args(["--retry", &RETRIES.to_string()])
        .args(["--retry-max-time", &RETRY_WINDOW.to_string()])
        .args(["-A", &format!("borer/{VERSION}")]);
    cmd.arg(if req.follow && header.is_none() {
        "-L"
    } else {
        "--no-location"
    });
    if let Some(accept) = req.accept {
        cmd.arg("-H").arg(format!("Accept: {accept}"));
    }
    if header.is_some() {
        cmd.args(["-H", "@-"]);
    }
    if let Some(out) = req.out {
        cmd.arg("-o").arg(out).args(["-w", "%{redirect_url}"]);
    }
    if let Some(headers) = req.meter {
        cmd.arg("-D").arg(headers);
    }
    cmd.arg(req.url)
        .stdin(if header.is_some() {
            Stdio::piped()
        } else {
            Stdio::null()
        })
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());
    (cmd, header)
}

/// Runs `curl` for one request.
///
/// # Arguments
///
/// * `req` - The request.
/// * `token` - The token, when one is set.
///
/// # Returns
///
/// What `curl` wrote to stdout: the body, or with [`Request::out`] the URL
/// a redirect named (empty when there was none).
///
/// # Errors
///
/// When `curl` does not start or exits nonzero; the message says what
/// happened ([`failure`]) with `curl`'s own error line.
fn curl(req: &Request<'_>, token: Option<&Token>) -> anyhow::Result<String> {
    let (mut cmd, header) = curl_command(req, token);
    let mut child = cmd
        .spawn()
        .context("curl does not run; Windows 10 1803 and later, macOS and Linux ship it")?;
    let handed = match (&header, child.stdin.take()) {
        (Some(header), Some(mut stdin)) => stdin.write_all(header.as_bytes()),
        _ => Ok(()),
    };
    if let (Some(file), Some(headers)) = (req.out, req.meter) {
        watch(&mut child, file, headers);
    }
    let out = child.wait_with_output().context("waiting for curl")?;
    if !out.status.success() {
        let said = String::from_utf8_lossy(&out.stderr);
        let line = said
            .lines()
            .find(|l| !l.trim().is_empty())
            .unwrap_or("no error text");
        bail!(
            "{}",
            failure(
                out.status.code(),
                line,
                req.secs,
                token.map(|t| t.var),
                header.is_some()
            )
        );
    }
    handed.context("handing curl the token")?;
    Ok(String::from_utf8_lossy(&out.stdout).into_owned())
}

/// Shows a download's progress on the loading line until its `curl`
/// exits: how much of `file` has arrived, of the size the response's
/// headers give, with the newest bytes streaming past.
///
/// It reads the growing file, not `curl`'s own progress bar.
///
/// # Arguments
///
/// * `child` - The running `curl`.
/// * `file` - The file it writes.
/// * `headers` - The file it writes the response headers to.
fn watch(child: &mut std::process::Child, file: &Path, headers: &Path) {
    /// The newest bytes the line streams.
    const NEWEST: u64 = 64;
    while matches!(child.try_wait(), Ok(None)) {
        let done = std::fs::metadata(file).map_or(0, |m| m.len());
        let total = std::fs::read_to_string(headers)
            .ok()
            .and_then(|h| content_length(&h));
        crate::term::progress(done, total, &newest(file, done, NEWEST));
        std::thread::sleep(Duration::from_millis(100));
    }
}

/// The size the last response in a header dump gives its body, when that
/// response is a success: a redirect's own headers say nothing of the file
/// it points to.
///
/// # Arguments
///
/// * `headers` - The headers `curl -D` wrote, one response after another.
fn content_length(headers: &str) -> Option<u64> {
    let last = headers.rfind("\nHTTP/").map_or(0, |at| at + 1);
    let mut lines = headers.get(last..)?.lines();
    let status = lines.next()?.split_whitespace().nth(1)?;
    if !status.starts_with('2') {
        return None;
    }
    lines.find_map(|line| {
        line.split_once(':')
            .filter(|(name, _)| name.trim().eq_ignore_ascii_case("content-length"))
            .and_then(|(_, value)| value.trim().parse().ok())
    })
}

/// The last `n` bytes of the first `len` of `file`; none when it cannot be
/// read.
///
/// # Arguments
///
/// * `file` - The file.
/// * `len` - How much of it to look at.
/// * `n` - How many bytes to read, at most.
fn newest(file: &Path, len: u64, n: u64) -> Vec<u8> {
    use std::io::{Read as _, Seek as _, SeekFrom};
    let mut bytes = Vec::new();
    if let Ok(mut f) = std::fs::File::open(file)
        && f.seek(SeekFrom::Start(len.saturating_sub(n))).is_ok()
    {
        let _ = f.take(n).read_to_end(&mut bytes);
    }
    bytes
}

/// What a failed request says: what happened and what to do, with
/// `curl`'s own line.
///
/// A timeout says which limit it ran into: a small request's whole try is
/// [`ANSWER_SECS`], while the archive's may stall that long or run past
/// its own longer limit.
///
/// # Arguments
///
/// * `code` - `curl`'s exit status; `None` when a signal ended it.
/// * `said` - `curl`'s error line.
/// * `secs` - All one try of the request may take, in seconds.
/// * `token` - The variable the token was read from, when one is set.
/// * `carried` - Whether this request carried the token.
fn failure(code: Option<i32>, said: &str, secs: u32, token: Option<&str>, carried: bool) -> String {
    let what = match (code, token) {
        (Some(22), Some(var)) if carried && said.contains("error: 401") => {
            return format!(
                "GitHub refused the token in {var} ({said}); renew it, or unset {var} to update without it"
            );
        }
        (Some(28), _) if secs > ANSWER_SECS => format!(
            "the download from GitHub stalled for {ANSWER_SECS} seconds or ran past {secs} ({said}); GitHub may be having trouble"
        ),
        (Some(28), _) => format!(
            "GitHub did not answer within {secs} seconds ({said}); it may be having trouble"
        ),
        (Some(5 | 6 | 7 | 35 | 52 | 55 | 56), _) => format!(
            "the connection to GitHub failed ({said}); check the network and any proxy, or GitHub may be having trouble"
        ),
        _ => return format!("download failed: {said}"),
    };
    let hint = if token.is_some() {
        ""
    } else {
        ", and if GitHub is slowing requests made without a token, set GH_TOKEN to a GitHub token so borer asks as you"
    };
    format!("{what} (https://www.githubstatus.com): try again later{hint}")
}

/// Fetches `url` into the file `out`, following its redirects.
///
/// A request carrying the token follows none itself ([`curl_command`]), so
/// each redirect it is answered with is fetched as a request of its own,
/// which carries the token only while it stays on [`TOKEN_HOST`].
///
/// # Arguments
///
/// * `url` - The URL.
/// * `out` - The file to write.
/// * `secs` - All one try may take, in seconds.
/// * `accept` - The `Accept` header, when `curl`'s own is not the one wanted.
/// * `token` - The token, when one is set.
/// * `meter` - Where `curl` writes the response headers, when the loading
///   line shows the download's progress ([`watch`]).
///
/// # Errors
///
/// When a request fails ([`curl`]), a redirect leaves `https`, or there are
/// more than [`REDIRECTS`].
fn fetch(
    url: &str,
    out: &Path,
    secs: u32,
    accept: Option<&'static str>,
    token: Option<&Token>,
    meter: Option<&Path>,
) -> anyhow::Result<()> {
    let mut url = url.to_owned();
    for _ in 0..=REDIRECTS {
        if !url.starts_with("https://") {
            bail!("refusing to download {url}: not an https URL");
        }
        let req = Request {
            url: &url,
            out: Some(out),
            follow: true,
            secs,
            accept,
            meter,
        };
        let next = curl(&req, token)?;
        if next.trim().is_empty() {
            return Ok(());
        }
        url = next.trim().to_owned();
    }
    bail!("downloading {url} took more than {REDIRECTS} redirects")
}

/// A release file as GitHub's API lists it.
#[derive(Debug, serde::Deserialize)]
struct Asset {
    /// The file name.
    name: String,
    /// Its API URL, which answers with the file when asked for
    /// `application/octet-stream`.
    url: String,
}

/// The latest release: its tag and, when read through GitHub's API, its
/// files.
#[derive(Debug, serde::Deserialize)]
struct Release {
    /// The tag, e.g. `v0.2.10`.
    #[serde(rename = "tag_name")]
    tag: String,
    /// The files; `None` when the tag was read from github.com's redirect,
    /// whose files download from `releases/download/<tag>/`.
    assets: Option<Vec<Asset>>,
}

impl Release {
    /// Where the release's file `name` downloads from, and the `Accept`
    /// header that asks for its bytes.
    ///
    /// # Arguments
    ///
    /// * `name` - The file name.
    ///
    /// # Errors
    ///
    /// When the API lists no such file.
    fn file(&self, name: &str) -> anyhow::Result<(String, Option<&'static str>)> {
        let Some(assets) = &self.assets else {
            let tag = &self.tag;
            return Ok((
                format!("https://github.com/{REPO}/releases/download/{tag}/{name}"),
                None,
            ));
        };
        let asset = assets
            .iter()
            .find(|a| a.name == name)
            .with_context(|| format!("release {} has no {name}", self.tag))?;
        Ok((asset.url.clone(), Some("application/octet-stream")))
    }
}

/// Whether `tag` reads as a version and holds only characters safe in a
/// URL and a file name.
///
/// # Arguments
///
/// * `tag` - The tag.
fn plain_tag(tag: &str) -> bool {
    parse_version(tag).is_some()
        && tag
            .chars()
            .all(|c| c.is_ascii_alphanumeric() || "._+-".contains(c))
}

/// The tag a `/releases/latest` redirect names: the last path component
/// of its `/releases/tag/<tag>` location.
///
/// # Arguments
///
/// * `location` - The URL the redirect names.
///
/// # Returns
///
/// `None` when the location names no release tag.
fn tag_of(location: &str) -> Option<String> {
    let path = location.trim().split(['?', '#']).next()?;
    let (_, tag) = path.rsplit_once("/releases/tag/")?;
    plain_tag(tag).then(|| tag.to_owned())
}

/// The release GitHub's API describes.
///
/// # Arguments
///
/// * `json` - The API's answer.
///
/// # Returns
///
/// `None` when it names no tag that reads as a version.
fn release_of(json: &str) -> Option<Release> {
    serde_json::from_str::<Release>(json)
        .ok()
        .filter(|r| plain_tag(&r.tag))
}

/// The latest release: read from the redirect github.com answers
/// `/releases/latest` with, or, with a token, from GitHub's API.
///
/// # Arguments
///
/// * `token` - The token, when one is set.
///
/// # Errors
///
/// When GitHub cannot be reached ([`curl`]), or names no release.
fn latest(token: Option<&Token>) -> anyhow::Result<Release> {
    if token.is_some() {
        let url = format!("https://api.github.com/repos/{REPO}/releases/latest");
        let req = Request {
            url: &url,
            out: None,
            follow: false,
            secs: ANSWER_SECS,
            accept: None,
            meter: None,
        };
        let json = curl(&req, token)?;
        return release_of(&json).context("GitHub's API named no tag for the latest release");
    }
    let url = format!("https://github.com/{REPO}/releases/latest");
    let req = Request {
        url: &url,
        out: Some(Path::new(NULL)),
        follow: false,
        secs: ANSWER_SECS,
        accept: None,
        meter: None,
    };
    let to = curl(&req, None)?;
    let tag = tag_of(&to).with_context(|| match to.trim() {
        "" => "no release is published yet".to_owned(),
        place => format!("GitHub's latest release points to {place}, which names no tag"),
    })?;
    Ok(Release { tag, assets: None })
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
    } else if has("/uv/cache/") || has("/.cache/uv/") {
        "uvx borer@latest"
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
/// It is bare when every character is one no shell reads specially, so any
/// shell runs it; else on Windows it is double-quoted behind PowerShell's
/// `&`, which a quoted program needs there, and elsewhere single-quoted, a
/// `'` inside written `'\''`.
///
/// # Arguments
///
/// * `path` - The program.
fn program(path: &Path) -> String {
    let text = shown(path);
    let plain = text
        .chars()
        .all(|c| c.is_ascii_alphanumeric() || "/\\._-:+@".contains(c));
    match (plain, cfg!(windows)) {
        (true, _) => text,
        (false, true) => format!("& \"{text}\""),
        (false, false) => format!("'{}'", text.replace('\'', r"'\''")),
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
/// beside a `site-packages` (Debian's `dist-packages`) holding a
/// `borer-*.dist-info`.
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
    for dir in lib("lib") {
        sites.extend(["site-packages", "dist-packages"].map(|s| dir.path().join(s)));
    }
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
    let token = token();
    let release = step(
        "finding the latest release",
        || latest(token.as_ref()),
        |r| format!("latest release {}", r.tag),
    )?;
    let tag = release.tag.as_str();
    remember(tag);
    if !is_newer(tag) {
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
    let work = std::env::temp_dir().join(format!("borer-update-{}", std::process::id()));
    std::fs::create_dir_all(&work)?;
    let result = install(&release, &name, ext, &work, &exe, token.as_ref());
    let _ = std::fs::remove_dir_all(&work);
    result?;
    Ok(format!(
        "updated borer {VERSION} -> {shown} at {}\n",
        exe.display()
    ))
}

/// Runs one step of an update under a loading line that says what it
/// does, then leaves a line that says how it ended; both only on a
/// terminal, where [`crate::term::busy`] draws.
///
/// # Arguments
///
/// * `doing` - What the step does, e.g. `finding the latest release`; also
///   what its line says when it fails.
/// * `work` - The step.
/// * `done` - What its line says when it succeeds.
///
/// # Errors
///
/// When the step fails, with its own error.
fn step<T>(
    doing: &str,
    work: impl FnOnce() -> anyhow::Result<T>,
    done: impl FnOnce(&T) -> String,
) -> anyhow::Result<T> {
    crate::term::busy(doing, &[]);
    let result = work();
    match &result {
        Ok(value) => crate::term::finish(true, &done(value)),
        Err(_) => crate::term::finish(false, doing),
    }
    result
}

/// Downloads the release's archive into `work`, checks it against the
/// release's `SHA256SUMS`, unpacks it there and puts its binary where
/// `exe` runs, each a [`step`] of its own.
///
/// # Arguments
///
/// * `release` - The release.
/// * `name` - The archive's name without its extension: also the folder it
///   unpacks to.
/// * `ext` - The archive's extension.
/// * `work` - The folder the download and unpacking go to.
/// * `exe` - Where this binary runs from.
/// * `token` - The token, when one is set.
///
/// # Errors
///
/// When a download fails, the archive does not match its listed sum, `tar`
/// cannot unpack it, or the binary's folder cannot be written.
fn install(
    release: &Release,
    name: &str,
    ext: &str,
    work: &Path,
    exe: &Path,
    token: Option<&Token>,
) -> anyhow::Result<()> {
    let file = format!("{name}.{ext}");
    let archive = work.join(&file);
    let downloading = format!("downloading {}", release.tag);
    let download = || {
        let (url, accept) = release.file(&file)?;
        let headers = work.join("headers");
        fetch(&url, &archive, ARCHIVE_SECS, accept, token, Some(&headers))
    };
    step(&downloading, download, |()| {
        let size = std::fs::metadata(&archive).map_or(0, |m| m.len());
        format!("downloaded {file}, {}", crate::term::megabytes(size))
    })?;
    let verify = || {
        let listed = work.join("SHA256SUMS");
        let (url, accept) = release.file("SHA256SUMS")?;
        fetch(&url, &listed, ANSWER_SECS, accept, token, None)?;
        let sums = std::fs::read_to_string(&listed).context("reading SHA256SUMS")?;
        let want =
            listed_sum(&sums, &file).with_context(|| format!("SHA256SUMS lists no {file}"))?;
        let got = sha256_hex(&std::fs::read(&archive)?);
        if !got.eq_ignore_ascii_case(want) {
            bail!("{file} does not match its listed SHA-256; nothing was changed");
        }
        Ok(())
    };
    step("verifying its SHA-256", verify, |()| {
        "SHA-256 matches SHA256SUMS".to_owned()
    })?;
    let unpack = || {
        let unpacked = Command::new("tar")
            .arg("-xf")
            .arg(&archive)
            .arg("-C")
            .arg(work)
            .status()
            .context("tar does not run")?;
        if !unpacked.success() {
            bail!("tar could not unpack {file}");
        }
        Ok(())
    };
    step("unpacking", unpack, |()| format!("unpacked {name}"))?;
    let new = work
        .join(name)
        .join(if cfg!(windows) { "borer.exe" } else { "borer" });
    step(
        "installing",
        || replace(&new, exe),
        |()| "installed".to_owned(),
    )
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
        .stdin(Stdio::null())
        .stdout(Stdio::null())
        .stderr(Stdio::null());
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
/// It sends no token: it runs unasked, in the background, where a token
/// GitHub refuses would fail it unseen. A failed check keeps the last
/// known tag with the new time, so an offline machine asks once a day, not
/// on every command. The claims that started checks ([`claim_file`]) go
/// once the answer is kept.
pub(crate) fn refresh() {
    let tag = latest(None)
        .ok()
        .map(|release| release.tag)
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
            (
                "/home/a/.cache/uv/archive-v0/x1/bin/borer",
                Some("uvx borer@latest"),
            ),
            (
                r"C:\Users\a\AppData\Local\uv\cache\archive-v0\x1\Scripts\borer.exe",
                Some("uvx borer@latest"),
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
        let debian = venv.join("lib").join("python3.11").join("dist-packages");
        std::fs::create_dir_all(debian.join("borer-0.2.5.dist-info")).expect("dist-packages");
        assert!(manager(&exe, None).is_some_and(|c| c.ends_with("-m pip install -U borer")));
        let _ = std::fs::remove_dir_all(&venv);
    }

    /// A program path is bare when plain and quoted when not, behind
    /// PowerShell's `&` on Windows.
    ///
    /// # Panics
    ///
    /// When a path is written another way.
    #[test]
    fn a_program_path_is_quoted_only_when_it_must_be() {
        assert_eq!(program(Path::new("/v/bin/python")), "/v/bin/python");
        for odd in ["/my env/bin/python", "/env(test)/bin/python", "/a$b/python"] {
            let want = if cfg!(windows) {
                format!("& \"{odd}\"")
            } else {
                format!("'{odd}'")
            };
            assert_eq!(program(Path::new(odd)), want);
        }
        if !cfg!(windows) {
            assert_eq!(program(Path::new("/it's/python")), r"'/it'\''s/python'");
        }
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

    /// A command's arguments as text.
    ///
    /// # Arguments
    ///
    /// * `cmd` - The command.
    fn argv(cmd: &Command) -> Vec<String> {
        cmd.get_args()
            .map(|a| a.to_string_lossy().into_owned())
            .collect()
    }

    /// The token goes to GitHub's API alone, as a header on stdin and
    /// never as an argument, and such a request follows no redirect; every
    /// request retries within its bounds.
    ///
    /// # Panics
    ///
    /// When the token is an argument, goes to another host, or rides a
    /// redirect, or the retry bounds are missing.
    #[test]
    fn a_token_goes_on_stdin_to_the_api_alone() {
        let token = Token {
            var: "GH_TOKEN",
            value: "ghp_s3cret".to_owned(),
        };
        let req = |url| Request {
            url,
            out: Some(Path::new("out.zip")),
            follow: true,
            secs: 9,
            accept: None,
            meter: None,
        };
        for url in [
            "https://api.github.com/repos/a/b/releases/latest",
            "https://api.github.com/repos/a/b/releases/assets/7",
        ] {
            let (cmd, header) = curl_command(&req(url), Some(&token));
            let args = argv(&cmd);
            assert_eq!(
                header.as_deref(),
                Some("Authorization: Bearer ghp_s3cret\n"),
                "{url}"
            );
            assert!(args.windows(2).any(|w| w == ["-H", "@-"]), "{url}");
            assert!(
                !args.iter().any(|a| a.contains("s3cret")),
                "{url}: {args:?}"
            );
            assert!(
                !args.iter().any(|a| a == "-L") && args.iter().any(|a| a == "--no-location"),
                "{url} follows with the token"
            );
        }
        assert!(to_api("https://api.github.com?x=1"));
        assert!(to_api("https://api.github.com#x"));
        for url in [
            "https://github.com/a/b/releases/latest",
            "https://release-assets.githubusercontent.com/x?sig=1",
            "http://api.github.com/x",
            "https://api.github.com.evil.example/x",
            "https://api.github.com@evil.example/x",
            "https://evil.example/?api.github.com",
            "https://github.com:8443/x",
        ] {
            let (cmd, header) = curl_command(&req(url), Some(&token));
            let args = argv(&cmd);
            assert_eq!(header, None, "{url}");
            assert!(
                !args.iter().any(|a| a == "@-" || a.contains("s3cret")),
                "{url}"
            );
            assert!(args.iter().any(|a| a == "-L"), "{url}");
        }
        let lookup = Request {
            follow: false,
            ..req("https://github.com/a/b/releases/latest")
        };
        let held = argv(&curl_command(&lookup, None).0);
        assert!(
            held.iter().any(|a| a == "--no-location") && !held.iter().any(|a| a == "-L"),
            "{held:?}"
        );
        let (cmd, header) = curl_command(&req("https://github.com/a/b/releases/latest"), None);
        let args = argv(&cmd);
        assert_eq!(header, None);
        assert!(!args.iter().any(|a| a == "--no-location"), "{args:?}");
        for pair in [
            ["--max-time", "9"],
            ["--retry", "2"],
            ["--retry-max-time", "60"],
            ["--speed-time", "15"],
            ["--connect-timeout", "15"],
        ] {
            assert!(args.windows(2).any(|w| w == pair), "{pair:?} in {args:?}");
        }
    }

    /// A token is read from `GH_TOKEN` first, trimmed, and one holding a
    /// character no token has is no token.
    ///
    /// # Panics
    ///
    /// When another variable or value is read.
    #[test]
    fn a_token_is_read_from_gh_token_first() {
        let read = |gh: Option<&str>, github: Option<&str>| {
            token_in(|var| match var {
                "GH_TOKEN" => gh.map(str::to_owned),
                "GITHUB_TOKEN" => github.map(str::to_owned),
                _ => None,
            })
            .map(|t| (t.var, t.value))
        };
        assert_eq!(
            read(Some("a\n"), Some("b")),
            Some(("GH_TOKEN", "a".to_owned()))
        );
        assert_eq!(
            read(Some(" "), Some("b")),
            Some(("GITHUB_TOKEN", "b".to_owned()))
        );
        assert_eq!(read(Some("a\nX-Other: 1"), None), None);
        assert_eq!(read(Some("a b"), None), None);
        assert_eq!(read(None, None), None);
    }

    /// A timeout and a failed connection say what happened and what to
    /// do, with curl's own line; a refused token names its variable.
    ///
    /// # Panics
    ///
    /// When a message reads otherwise.
    #[test]
    fn a_timeout_says_what_happened_and_what_to_do() {
        let line = "curl: (28) Operation timed out after 15002 milliseconds with 0 bytes received";
        assert_eq!(
            failure(Some(28), line, ANSWER_SECS, None, false),
            format!(
                "GitHub did not answer within 15 seconds ({line}); it may be having trouble \
                 (https://www.githubstatus.com): try again later, and if GitHub is slowing \
                 requests made without a token, set GH_TOKEN to a GitHub token so borer asks as you"
            )
        );
        let stalled =
            "curl: (28) Operation too slow. Less than 1 bytes/sec transferred the last 15 seconds";
        let download = failure(Some(28), stalled, ARCHIVE_SECS, None, false);
        assert!(
            download.starts_with(&format!(
                "the download from GitHub stalled for 15 seconds or ran past 600 ({stalled}); \
                 GitHub may be having trouble (https://www.githubstatus.com): try again later"
            )),
            "{download}"
        );
        let carried = failure(Some(28), line, ANSWER_SECS, Some("GITHUB_TOKEN"), true);
        assert!(carried.contains(line) && carried.contains("try again later"));
        assert!(!carried.contains("set GH_TOKEN"), "{carried}");
        let refused = "curl: (7) Failed to connect to github.com port 443";
        let said = failure(Some(7), refused, ANSWER_SECS, None, false);
        assert!(
            said.starts_with("the connection to GitHub failed"),
            "{said}"
        );
        assert!(said.contains(refused) && said.contains("https://www.githubstatus.com"));
        let stale = "curl: (22) The requested URL returned error: 401";
        assert_eq!(
            failure(Some(22), stale, ANSWER_SECS, Some("GITHUB_TOKEN"), true),
            format!(
                "GitHub refused the token in GITHUB_TOKEN ({stale}); renew it, or unset \
                 GITHUB_TOKEN to update without it"
            )
        );
        let missing = "curl: (22) The requested URL returned error: 404";
        assert_eq!(
            failure(Some(22), missing, ANSWER_SECS, Some("GH_TOKEN"), true),
            format!("download failed: {missing}")
        );
        assert_eq!(
            failure(Some(22), stale, ANSWER_SECS, Some("GH_TOKEN"), false),
            format!("download failed: {stale}")
        );
    }

    /// The latest tag is the last path component of a `/releases/tag/`
    /// location, and nothing else is a tag.
    ///
    /// # Panics
    ///
    /// When a location reads otherwise.
    #[test]
    fn the_latest_tag_is_read_from_the_redirect() {
        let at = "https://github.com/imjustprism/borer/releases/tag/";
        assert_eq!(tag_of(&format!("{at}v0.2.10")).as_deref(), Some("v0.2.10"));
        assert_eq!(
            tag_of(&format!("{at}v0.2.10\r\n")).as_deref(),
            Some("v0.2.10")
        );
        assert_eq!(
            tag_of(&format!("{at}v1.2.3?x=1#y")).as_deref(),
            Some("v1.2.3")
        );
        for not in [
            String::new(),
            "https://github.com/imjustprism/borer/releases".to_owned(),
            format!("{at}latest"),
            format!("{at}v1.2.3/x"),
            format!("{at}v1.2.3-..%2F..%2Fx"),
            format!("{at}v1.2.3-a\\b"),
        ] {
            assert_eq!(tag_of(&not), None, "{not}");
        }
    }

    /// The API's release names each file's API URL, asked for its bytes;
    /// a release read from the redirect downloads from the tag's folder.
    ///
    /// # Panics
    ///
    /// When a file is found elsewhere or a bad tag is taken.
    #[test]
    fn a_release_names_where_each_file_downloads_from() {
        let json = r#"{"tag_name":"v9.0.0","body":"notes","assets":[{"name":"SHA256SUMS",
            "url":"https://api.github.com/repos/imjustprism/borer/releases/assets/7","size":90}]}"#;
        let release = release_of(json).expect("a release");
        assert_eq!(
            release.file("SHA256SUMS").expect("listed"),
            (
                "https://api.github.com/repos/imjustprism/borer/releases/assets/7".to_owned(),
                Some("application/octet-stream")
            )
        );
        assert!(release.file("borer-v9.0.0-x.zip").is_err());
        assert!(release_of(r#"{"tag_name":"v9.0.0/../x","assets":[]}"#).is_none());
        assert!(release_of("<html>").is_none());
        let web = Release {
            tag: "v9.0.0".to_owned(),
            assets: None,
        };
        assert_eq!(
            web.file("SHA256SUMS").expect("a url"),
            (
                "https://github.com/imjustprism/borer/releases/download/v9.0.0/SHA256SUMS"
                    .to_owned(),
                None
            )
        );
    }

    /// A download refuses a URL that is not `https` before it runs
    /// anything.
    ///
    /// # Panics
    ///
    /// When it is fetched.
    #[test]
    fn a_download_refuses_plain_http() {
        let refused = fetch("http://github.com/x", Path::new(NULL), 1, None, None, None)
            .expect_err("refused")
            .to_string();
        assert!(refused.contains("not an https URL"), "{refused}");
    }

    /// A download's size is the last response's `Content-Length`, read
    /// while its headers are still arriving, and none while that response
    /// is a redirect or is not yet a success.
    ///
    /// # Panics
    ///
    /// When another size is read.
    #[test]
    fn a_downloads_size_is_its_last_responses_length() {
        let redirect = "HTTP/1.1 302 Found\r\nContent-Length: 0\r\nLocation: https://x/y\r\n\r\n";
        let landed =
            "HTTP/1.1 200 OK\r\nContent-Type: application/zip\r\ncontent-length: 8123456\r\n\r\n";
        assert_eq!(
            content_length(&format!("{redirect}{landed}")),
            Some(8_123_456)
        );
        assert_eq!(content_length(landed), Some(8_123_456));
        assert_eq!(
            content_length("HTTP/2 200\r\ncontent-length: 7\r\n"),
            Some(7)
        );
        assert_eq!(content_length(redirect), None);
        assert_eq!(
            content_length(&format!("{redirect}HTTP/1.1 200 OK\r\n")),
            None
        );
        assert_eq!(
            content_length("HTTP/1.1 503 Busy\r\nContent-Length: 19\r\n\r\n"),
            None
        );
        assert_eq!(content_length(""), None);
        let req = |meter| Request {
            url: "https://github.com/a/b/releases/download/v1.0.0/x.zip",
            out: Some(Path::new("x.zip")),
            follow: true,
            secs: 600,
            accept: None,
            meter,
        };
        let watched = argv(&curl_command(&req(Some(Path::new("headers"))), None).0);
        assert!(
            watched.windows(2).any(|w| w == ["-D", "headers"]),
            "{watched:?}"
        );
        let quiet = argv(&curl_command(&req(None), None).0);
        assert!(!quiet.iter().any(|a| a == "-D"), "{quiet:?}");
    }
}
