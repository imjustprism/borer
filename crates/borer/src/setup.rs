//! `borer setup`: registers this binary as the MCP server `borer` with the
//! agent clients installed on the machine.
//!
//! A client counts as installed when its configuration directory exists.
//! Claude Code is registered through its own `claude mcp add` when
//! `claude` is on `PATH`; every other client, and Claude Code without its
//! CLI, gets an entry added to its configuration file. The run is dry by
//! default: it says, per client, which file it would change and the entry
//! it would add, or that the entry is already there. With `--apply` it
//! writes, first copying each file it changes to `<file>.bak`.
//!
//! An edit only ever inserts: the entry goes into the file's text, so the
//! rest of the file, comments, trailing commas and key order included,
//! stays byte for byte. A file that already names a server `borer` is left
//! as it is, and one that does not parse even as JSONC is not touched; the
//! report then gives the entry to add by hand.

use std::fmt::Write as _;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

/// The name borer is registered under in every client.
const NAME: &str = "borer";

/// Width of the client column in the report.
const CLIENT_WIDTH: usize = 15;

/// The three operating systems whose configuration paths differ.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Os {
    /// Windows: `%APPDATA%` and `%LOCALAPPDATA%`.
    Windows,
    /// macOS: `~/Library/Application Support` beside `~/.config`.
    Mac,
    /// Linux and the other Unix systems: `$XDG_CONFIG_HOME`.
    Linux,
}

impl Os {
    /// The operating system this binary runs on.
    const HOST: Os = if cfg!(windows) {
        Os::Windows
    } else if cfg!(target_os = "macos") {
        Os::Mac
    } else {
        Os::Linux
    };
}

/// The directories client configurations hang from, read from the
/// environment once so a test can point them at a scratch directory.
#[derive(Debug, Clone, Default)]
struct Env {
    /// The user's home directory.
    home: Option<PathBuf>,
    /// Windows' roaming application data, `%APPDATA%`.
    appdata: Option<PathBuf>,
    /// Windows' local application data, `%LOCALAPPDATA%`.
    local: Option<PathBuf>,
    /// The configuration directory off Windows: `$XDG_CONFIG_HOME`, else
    /// `~/.config`.
    config: Option<PathBuf>,
    /// Codex's home, `$CODEX_HOME`, else `~/.codex`.
    codex: Option<PathBuf>,
}

impl Env {
    /// Reads the directories from the environment.
    ///
    /// # Returns
    ///
    /// The directories; a variable that is unset or empty is `None`.
    fn read() -> Env {
        let var = |name: &str| {
            std::env::var_os(name)
                .filter(|v| !v.is_empty())
                .map(PathBuf::from)
        };
        let home = std::env::home_dir();
        Env {
            config: var("XDG_CONFIG_HOME").or_else(|| home.as_ref().map(|h| h.join(".config"))),
            codex: var("CODEX_HOME").or_else(|| home.as_ref().map(|h| h.join(".codex"))),
            appdata: var("APPDATA"),
            local: var("LOCALAPPDATA"),
            home,
        }
    }
}

/// How a client's file holds its servers.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Format {
    /// A JSON object of servers under a top-level key.
    Json {
        /// The top-level key: `mcpServers`, `servers` or `context_servers`.
        key: &'static str,
        /// Whether an entry states `"type": "stdio"`.
        typed: bool,
    },
    /// Codex's TOML: a `[mcp_servers.borer]` table.
    Toml,
}

/// A client's configuration file.
#[derive(Debug, Clone, PartialEq, Eq)]
struct Target {
    /// The client, as the report names it.
    client: &'static str,
    /// The directory whose existence means the client is installed.
    dir: PathBuf,
    /// The file the entry goes in.
    file: PathBuf,
    /// How the file holds its servers.
    format: Format,
}

/// What adding the entry to a file's text comes to.
#[derive(Debug, Clone, PartialEq, Eq)]
enum Change {
    /// The file already names a server `borer`, running this command when
    /// the file says.
    Present(Option<String>),
    /// The file's text with the entry added.
    Text(String),
}

/// Finds Claude Desktop's directory on Windows.
///
/// The Store (MSIX) build reads a redirected copy under
/// `%LOCALAPPDATA%\Packages\Claude_*` instead of `%APPDATA%\Claude`, so
/// that one wins when it exists.
///
/// # Arguments
///
/// * `env` - The directories.
///
/// # Returns
///
/// The directory, or `None` when neither base is known.
fn claude_desktop_windows(env: &Env) -> Option<PathBuf> {
    let packaged = env.local.as_ref().and_then(|local| {
        let mut dirs: Vec<PathBuf> = std::fs::read_dir(local.join("Packages"))
            .ok()?
            .flatten()
            .filter(|e| e.file_name().to_string_lossy().starts_with("Claude_"))
            .map(|e| e.path().join("LocalCache").join("Roaming").join("Claude"))
            .filter(|d| d.is_dir())
            .collect();
        dirs.sort();
        dirs.into_iter().next()
    });
    packaged.or_else(|| env.appdata.as_ref().map(|a| a.join("Claude")))
}

/// Lists every client borer knows with the file its entry goes in.
///
/// # Arguments
///
/// * `os` - Whose paths to use.
/// * `env` - The directories.
///
/// # Returns
///
/// One row per client file, in report order: the client and its target,
/// `None` when the directory it would be in has no known base.
fn candidates(os: Os, env: &Env) -> Vec<(&'static str, Option<Target>)> {
    let row = |client: &'static str, dir: Option<PathBuf>, file: &str, format: Format| {
        let target = dir.map(|dir| {
            let file = dir.join(file);
            Target {
                client,
                dir,
                file,
                format,
            }
        });
        (client, target)
    };
    let home = |rest: &str| env.home.as_ref().map(|h| h.join(rest));
    let app_support = |rest: &str| home("Library/Application Support").map(|d| d.join(rest));
    let config = |rest: &str| match os {
        Os::Windows => env.appdata.as_ref().map(|a| a.join(rest)),
        Os::Mac | Os::Linux => env.config.as_ref().map(|c| c.join(rest)),
    };
    let roaming = |rest: &str| match os {
        Os::Mac => app_support(rest),
        Os::Windows | Os::Linux => config(rest),
    };
    let desktop = match os {
        Os::Windows => claude_desktop_windows(env),
        Os::Mac => app_support("Claude"),
        Os::Linux => config("Claude"),
    };
    let plain = Format::Json {
        key: "mcpServers",
        typed: false,
    };
    let typed = Format::Json {
        key: "mcpServers",
        typed: true,
    };
    let vscode = Format::Json {
        key: "servers",
        typed: true,
    };
    let zed = Format::Json {
        key: "context_servers",
        typed: false,
    };
    let claude_code = env.home.as_ref().map(|h| Target {
        client: "claude code",
        dir: h.join(".claude"),
        file: h.join(".claude.json"),
        format: typed,
    });
    let zed_dir = config(if os == Os::Windows { "Zed" } else { "zed" });
    vec![
        ("claude code", claude_code),
        row(
            "claude desktop",
            desktop,
            "claude_desktop_config.json",
            plain,
        ),
        row("cursor", home(".cursor"), "mcp.json", typed),
        row(
            "windsurf",
            home(".codeium/windsurf"),
            "mcp_config.json",
            plain,
        ),
        row("devin desktop", config("devin"), "mcp_config.json", plain),
        row("vs code", roaming("Code/User"), "mcp.json", vscode),
        row(
            "vs code insiders",
            roaming("Code - Insiders/User"),
            "mcp.json",
            vscode,
        ),
        row("gemini cli", home(".gemini"), "settings.json", plain),
        row("codex cli", env.codex.clone(), "config.toml", Format::Toml),
        row("zed", zed_dir, "settings.json", zed),
    ]
}

/// Splits the clients into the installed ones, with their files, and the
/// names of the rest.
///
/// # Arguments
///
/// * `os` - Whose paths to use.
/// * `env` - The directories.
///
/// # Returns
///
/// The installed clients' targets and the other clients' names, both in
/// report order.
fn targets(os: Os, env: &Env) -> (Vec<Target>, Vec<&'static str>) {
    let mut found = Vec::new();
    let mut missing = Vec::new();
    for (client, target) in candidates(os, env) {
        match target.filter(|t| t.dir.is_dir()) {
            Some(target) => found.push(target),
            None => missing.push(client),
        }
    }
    (found, missing)
}

/// Blanks what a JSON file may hold that strict JSON does not.
///
/// That is `//` and `/* */` comments and trailing commas (JSONC, as VS
/// Code and Zed read it) and a leading byte order mark. Each blanked byte
/// becomes a space, newlines excepted, so a position in the result is the
/// same position in the text.
///
/// # Arguments
///
/// * `text` - The file's text.
///
/// # Returns
///
/// The text as strict JSON, if the rest of it is.
fn plain_json(text: &str) -> String {
    let bytes = text.as_bytes();
    let mut out = bytes.to_vec();
    if let Some(bom) = out.get_mut(..3).filter(|b| *b == b"\xef\xbb\xbf") {
        bom.fill(b' ');
    }
    let mut blank = |from: usize, to: usize| {
        for b in out.iter_mut().take(to).skip(from) {
            if *b != b'\n' {
                *b = b' ';
            }
        }
    };
    let mut i = 0;
    let mut in_string = false;
    while let Some(&c) = bytes.get(i) {
        let next = bytes.get(i + 1).copied();
        if in_string {
            match c {
                b'\\' => i += 1,
                b'"' => in_string = false,
                _ => {}
            }
            i += 1;
        } else if c == b'"' {
            in_string = true;
            i += 1;
        } else if c == b'/' && next == Some(b'/') {
            let end = text[i..].find('\n').map_or(bytes.len(), |n| i + n);
            blank(i, end);
            i = end;
        } else if c == b'/' && next == Some(b'*') {
            let end = text[i + 2..]
                .find("*/")
                .map_or(bytes.len(), |n| i + 2 + n + 2);
            blank(i, end);
            i = end;
        } else {
            i += 1;
        }
    }
    let mut in_string = false;
    let mut i = 0;
    while let Some(&c) = out.get(i) {
        if in_string {
            match c {
                b'\\' => i += 1,
                b'"' => in_string = false,
                _ => {}
            }
        } else if c == b'"' {
            in_string = true;
        } else if c == b','
            && out
                .get(i + 1..)
                .and_then(|rest| rest.iter().find(|b| !b.is_ascii_whitespace()))
                .is_some_and(|b| matches!(b, b'}' | b']'))
            && let Some(comma) = out.get_mut(i)
        {
            *comma = b' ';
        }
        i += 1;
    }
    String::from_utf8_lossy(&out).into_owned()
}

/// Finds where the object a top-level member holds opens.
///
/// # Arguments
///
/// * `plain` - The file's text with comments and trailing commas blanked, already checked to
///   parse as a JSON object.
/// * `key` - The member's name, which holds no escapes.
///
/// # Returns
///
/// The position of the member's `{`, the last when the key repeats (as a
/// parser reads it), or `None` when no such member holds an object.
fn member_open(plain: &str, key: &str) -> Option<usize> {
    let bytes = plain.as_bytes();
    let after_space = |from: usize| {
        (from..bytes.len()).find(|&j| bytes.get(j).is_some_and(|b| !b.is_ascii_whitespace()))
    };
    let mut depth = 0usize;
    let mut found = None;
    let mut i = 0;
    while let Some(&c) = bytes.get(i) {
        match c {
            b'"' => {
                let start = i + 1;
                let mut j = start;
                while let Some(&s) = bytes.get(j) {
                    match s {
                        b'\\' => j += 2,
                        b'"' => break,
                        _ => j += 1,
                    }
                }
                if depth == 1
                    && plain.get(start..j) == Some(key)
                    && let Some(colon) = after_space(j + 1).filter(|&k| bytes.get(k) == Some(&b':'))
                    && let Some(open) =
                        after_space(colon + 1).filter(|&k| bytes.get(k) == Some(&b'{'))
                {
                    found = Some(open);
                }
                i = j + 1;
            }
            b'{' | b'[' => {
                depth += 1;
                i += 1;
            }
            b'}' | b']' => {
                depth = depth.saturating_sub(1);
                i += 1;
            }
            _ => i += 1,
        }
    }
    found
}

/// The leading whitespace of the line a position is on.
///
/// # Arguments
///
/// * `text` - The text.
/// * `at` - The position.
fn indent_at(text: &str, at: usize) -> &str {
    let line = text[..at].rfind('\n').map_or(0, |n| n + 1);
    let rest = &text[line..];
    &rest[..rest.len() - rest.trim_start_matches([' ', '\t']).len()]
}

/// Adds a server entry to a JSON configuration's text.
///
/// The entry is inserted as the first member of the servers object, which
/// is made as the first member of the file when it is missing; nothing
/// else in the text changes. An empty text becomes a new file.
///
/// # Arguments
///
/// * `text` - The file's text, possibly with comments.
/// * `key` - The top-level key holding the servers.
/// * `entry` - The entry's value, as JSON.
///
/// # Returns
///
/// The new text, or that a server named `borer` is already there.
///
/// # Errors
///
/// When the text is not a JSON object once comments and trailing commas
/// are blanked, or its servers member is not an object; the message says
/// which.
fn add_json(text: &str, key: &str, entry: &str) -> Result<Change, String> {
    let nl = if text.contains("\r\n") { "\r\n" } else { "\n" };
    let member = format!("\"{NAME}\": {entry}");
    if text.trim().is_empty() {
        return Ok(Change::Text(format!(
            "{{{nl}  \"{key}\": {{{nl}    {member}{nl}  }}{nl}}}{nl}"
        )));
    }
    let plain = plain_json(text);
    let root: serde_json::Value =
        serde_json::from_str(&plain).map_err(|e| format!("it is not plain JSON ({e})"))?;
    let root = root
        .as_object()
        .ok_or_else(|| "its top level is not an object".to_owned())?;
    let unit = text
        .lines()
        .find_map(|l| {
            let rest = l.trim_start_matches([' ', '\t']);
            (rest.starts_with('"') && rest.len() < l.len()).then(|| &l[..l.len() - rest.len()])
        })
        .unwrap_or("  ");
    let is_empty_after = |open: usize| plain[open + 1..].trim_start().starts_with('}');
    let (at, insert) = match root.get(key) {
        Some(serde_json::Value::Object(servers)) => {
            if let Some(present) = servers.get(NAME) {
                let command = present.get("command").and_then(serde_json::Value::as_str);
                return Ok(Change::Present(command.map(str::to_owned)));
            }
            let open = member_open(&plain, key)
                .ok_or_else(|| format!("cannot find where its {key} object opens"))?;
            let outer = indent_at(text, open);
            let tail = if is_empty_after(open) {
                format!("{nl}{outer}")
            } else {
                ",".to_owned()
            };
            (open, format!("{nl}{outer}{unit}{member}{tail}"))
        }
        Some(_) => return Err(format!("its {key} member is not an object")),
        None => {
            let open = plain.len() - plain.trim_start().len();
            let outer = indent_at(text, open);
            let tail = if is_empty_after(open) {
                format!("{nl}{outer}")
            } else {
                ",".to_owned()
            };
            (
                open,
                format!(
                    "{nl}{outer}{unit}\"{key}\": {{{nl}{outer}{unit}{unit}{member}{nl}{outer}{unit}}}{tail}"
                ),
            )
        }
    };
    let mut out = String::with_capacity(text.len() + insert.len());
    out.push_str(&text[..=at]);
    out.push_str(&insert);
    out.push_str(&text[at + 1..]);
    let added = serde_json::from_str::<serde_json::Value>(&plain_json(&out))
        .ok()
        .is_some_and(|v| v.get(key).and_then(|s| s.get(NAME)).is_some());
    if !added {
        return Err(format!("adding the entry under {key} did not give JSON"));
    }
    Ok(Change::Text(out))
}

/// A string as a TOML value: literal (`'...'`, no escapes, the readable
/// form of a Windows path) when it can be, else basic with escapes.
///
/// # Arguments
///
/// * `s` - The string.
fn toml_string(s: &str) -> String {
    if s.contains('\'') || s.chars().any(char::is_control) {
        serde_json::Value::String(s.to_owned()).to_string()
    } else {
        format!("'{s}'")
    }
}

/// Adds the `[mcp_servers.borer]` table to a Codex `config.toml`'s text by
/// appending it, without a TOML parser.
///
/// A line is read as a table header when it starts with `[`; a server
/// named `borer` is present when a header names `mcp_servers.borer` (or a
/// table below it), or a `borer` key sits in `[mcp_servers]` or as a
/// dotted key at the top.
///
/// # Arguments
///
/// * `text` - The file's text.
/// * `command` - The program the entry runs.
///
/// # Returns
///
/// The new text, or that a server named `borer` is already there.
///
/// # Errors
///
/// When `mcp_servers` is an inline table at the top, which a table appended
/// after it cannot extend.
fn add_toml(text: &str, command: &str) -> Result<Change, String> {
    let squash = |s: &str| {
        s.chars()
            .filter(|c| !matches!(c, ' ' | '\t' | '"' | '\''))
            .collect::<String>()
    };
    let own = format!("mcp_servers.{NAME}");
    let mut table: Option<String> = None;
    for line in text.lines() {
        let line = line.trim();
        if let Some(header) = line.strip_prefix('[') {
            let name = squash(
                header
                    .trim_start_matches('[')
                    .split(']')
                    .next()
                    .unwrap_or_default(),
            );
            if name == own || name.starts_with(&format!("{own}.")) {
                return Ok(Change::Present(None));
            }
            table = Some(name);
            continue;
        }
        let Some((key, _)) = line.split_once('=') else {
            continue;
        };
        let key = squash(key);
        let present = match table.as_deref() {
            None => {
                if key == "mcp_servers" {
                    return Err(
                        "its mcp_servers is an inline table, which an appended table cannot extend"
                            .to_owned(),
                    );
                }
                key == own || key.starts_with(&format!("{own}."))
            }
            Some("mcp_servers") => key == NAME || key.starts_with(&format!("{NAME}.")),
            Some(_) => false,
        };
        if present {
            return Ok(Change::Present(None));
        }
    }
    let nl = if text.contains("\r\n") { "\r\n" } else { "\n" };
    let mut out = text.to_owned();
    if !out.is_empty() {
        if !out.ends_with('\n') {
            out.push_str(nl);
        }
        out.push_str(nl);
    }
    let _ = write!(
        out,
        "[{own}]{nl}command = {}{nl}args = []{nl}",
        toml_string(command)
    );
    Ok(Change::Text(out))
}

/// The entry a target's file gets, as its format writes it.
///
/// # Arguments
///
/// * `format` - The file's format.
/// * `command` - The program the entry runs.
fn entry(format: Format, command: &str) -> String {
    let quoted = serde_json::Value::String(command.to_owned()).to_string();
    match format {
        Format::Json { typed: true, .. } => {
            format!("{{\"type\": \"stdio\", \"command\": {quoted}, \"args\": []}}")
        }
        Format::Json { typed: false, .. } => format!("{{\"command\": {quoted}, \"args\": []}}"),
        Format::Toml => format!("[mcp_servers.{NAME}] command = {}", toml_string(command)),
    }
}

/// The path a changed file's copy is kept at: the file's name with `.bak`
/// added.
///
/// # Arguments
///
/// * `file` - The file.
fn backup_path(file: &Path) -> PathBuf {
    let mut name = file.as_os_str().to_owned();
    name.push(".bak");
    PathBuf::from(name)
}

/// Adds the entry to one client's file, or says what adding it would do.
///
/// # Arguments
///
/// * `target` - The client's file.
/// * `command` - The program the entry runs.
/// * `apply` - Write the change; otherwise only describe it.
///
/// # Returns
///
/// The report's text for the client, after its name, and whether the
/// client failed: a file that could not be read, edited or written.
fn register_file(target: &Target, command: &str, apply: bool) -> (String, bool) {
    let file = target.file.display();
    let existed = target.file.is_file();
    let text = if existed {
        match std::fs::read_to_string(&target.file) {
            Ok(text) => text,
            Err(e) => return (format!("{file}: cannot read it: {e}"), true),
        }
    } else {
        String::new()
    };
    let entry = entry(target.format, command);
    let (change, place) = match target.format {
        Format::Json { key, .. } => (add_json(&text, key, &entry), format!("under {key}")),
        Format::Toml => (add_toml(&text, command), "as a table".to_owned()),
    };
    let new = match change {
        Ok(Change::Text(new)) => new,
        Ok(Change::Present(Some(other))) if other != command => {
            return (
                format!("{file}: already registers {NAME}, running {other}; left as it is"),
                false,
            );
        }
        Ok(Change::Present(_)) => return (format!("{file}: already registers {NAME}"), false),
        Err(why) => {
            return (
                format!("{file}: cannot edit it: {why}; add {entry} {place} by hand"),
                true,
            );
        }
    };
    let added = match target.format {
        Format::Json { .. } => format!("\"{NAME}\": {entry}"),
        Format::Toml => entry,
    };
    if !apply {
        let verb = if existed {
            "would add"
        } else {
            "would create it with"
        };
        return (format!("{file}: {verb} {added} {place}"), false);
    }
    let backup = backup_path(&target.file);
    if existed && let Err(e) = std::fs::copy(&target.file, &backup) {
        return (
            format!(
                "{file}: cannot keep a copy at {}: {e}; not changed",
                backup.display()
            ),
            true,
        );
    }
    if let Err(e) = std::fs::write(&target.file, new) {
        return (format!("{file}: cannot write it: {e}"), true);
    }
    if existed {
        (
            format!(
                "{file}: added {added} {place}; the old file is {}",
                backup.display()
            ),
            false,
        )
    } else {
        (format!("{file}: created with {added} {place}"), false)
    }
}

/// Finds the `claude` command on `PATH`: `claude.exe` or the npm shim
/// `claude.cmd` on Windows, `claude` elsewhere.
///
/// # Returns
///
/// The program, or `None` when `PATH` has none.
fn claude_cli() -> Option<PathBuf> {
    let names: &[&str] = if cfg!(windows) {
        &["claude.exe", "claude.cmd"]
    } else {
        &["claude"]
    };
    std::env::split_paths(&std::env::var_os("PATH")?)
        .find_map(|dir| names.iter().map(|n| dir.join(n)).find(|p| p.is_file()))
}

/// Registers borer with Claude Code through its CLI, or says what that
/// would run.
///
/// `claude mcp get borer` succeeds when a server by that name is already
/// configured; `claude mcp add --scope user` adds it for every project.
///
/// # Arguments
///
/// * `claude` - The `claude` program.
/// * `command` - The program the server runs.
/// * `apply` - Run the add; otherwise only describe it.
///
/// # Returns
///
/// The report's text for Claude Code, after its name, and whether it
/// failed.
fn register_claude_cli(claude: &Path, command: &str, apply: bool) -> (String, bool) {
    let shown = format!("claude mcp add --scope user {NAME} -- {command}");
    let present = Command::new(claude)
        .args(["mcp", "get", NAME])
        .stdin(Stdio::null())
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .status();
    match present {
        Ok(s) if s.success() => {
            return (format!("claude mcp get {NAME}: already registered"), false);
        }
        Ok(_) => {}
        Err(e) => return (format!("cannot run {}: {e}", claude.display()), true),
    }
    if !apply {
        return (format!("would run: {shown}"), false);
    }
    let added = Command::new(claude)
        .args(["mcp", "add", "--scope", "user", NAME, "--", command])
        .stdin(Stdio::null())
        .output();
    match added {
        Ok(out) if out.status.success() => (format!("ran: {shown}"), false),
        Ok(out) => {
            let why = String::from_utf8_lossy(&out.stderr);
            let why = why
                .lines()
                .find(|l| !l.trim().is_empty())
                .unwrap_or("no message");
            (
                format!("{shown} failed ({}): {}", out.status, why.trim()),
                true,
            )
        }
        Err(e) => (format!("cannot run {}: {e}", claude.display()), true),
    }
}

/// Registers this binary with every installed client, or says what that
/// would do: the CLI's `setup`.
///
/// # Arguments
///
/// * `apply` - Make the changes; otherwise report them only.
///
/// # Returns
///
/// The report, one line per installed client after a header and with the
/// clients not found last, and how many clients failed.
///
/// # Errors
///
/// When this binary's path does not read or is not UTF-8, which a
/// configuration file cannot hold.
pub(crate) fn setup(apply: bool) -> anyhow::Result<(String, usize)> {
    let exe = std::env::current_exe()?;
    let command = exe
        .to_str()
        .ok_or_else(|| anyhow::anyhow!("{} is not a UTF-8 path", exe.display()))?;
    let (found, mut missing) = targets(Os::HOST, &Env::read());
    let claude = claude_cli();
    let mut out = if apply {
        format!("# setup: registering {command} as the MCP server {NAME}\n")
    } else {
        format!(
            "# setup: dry run; `borer setup --apply` registers {command} as the MCP server {NAME}\n"
        )
    };
    let mut failed = 0;
    let mut line = |client: &str, (text, bad): (String, bool)| {
        failed += usize::from(bad);
        let _ = writeln!(out, "{client:<CLIENT_WIDTH$} {text}");
    };
    if let Some(claude) = &claude {
        missing.retain(|c| *c != "claude code");
        line("claude code", register_claude_cli(claude, command, apply));
    }
    for target in &found {
        if claude.is_some() && target.client == "claude code" {
            continue;
        }
        line(target.client, register_file(target, command, apply));
    }
    if found.is_empty() && claude.is_none() {
        out.push_str("# no agent client found; add the server by hand: see README.md\n");
    }
    if !missing.is_empty() {
        let _ = writeln!(out, "# not found: {}", missing.join(", "));
    }
    Ok((out, failed))
}

#[cfg(test)]
mod tests {
    use std::path::{Path, PathBuf};

    use super::{
        Change, Env, Format, Os, Target, add_json, add_toml, backup_path, plain_json,
        register_file, targets,
    };

    /// A directory of its own under the temporary directory, emptied.
    ///
    /// # Panics
    ///
    /// When the directory cannot be made.
    fn scratch(name: &str) -> PathBuf {
        let dir = std::env::temp_dir().join(format!("borer_setup_{name}_{}", std::process::id()));
        std::fs::remove_dir_all(&dir).ok();
        std::fs::create_dir_all(&dir).expect("a scratch directory");
        dir
    }

    /// The text of a changed file.
    ///
    /// # Panics
    ///
    /// When the change is not new text.
    fn text(change: Result<Change, String>) -> String {
        match change {
            Ok(Change::Text(t)) => t,
            other => panic!("expected new text, got {other:?}"),
        }
    }

    /// The entry the tests add.
    const ENTRY: &str = r#"{"command": "/opt/borer", "args": []}"#;

    /// An entry goes into an existing servers object as its first member,
    /// every other byte of the file (comments, other servers, other keys,
    /// their order) stays, and a second add finds it present.
    ///
    /// # Panics
    ///
    /// When a byte of the old file is lost, the result does not parse, or
    /// the second add adds again.
    #[test]
    fn an_entry_joins_the_servers_and_keeps_everything_else() {
        let old = "{\n  // keep me\n  \"zeta\": 1,\n  \"mcpServers\": {\n    \"other\": {\"command\": \"node\"}\n  },\n  \"alpha\": [1, 2] /* and me */\n}\n";
        let new = text(add_json(old, "mcpServers", ENTRY));
        assert_eq!(
            new,
            "{\n  // keep me\n  \"zeta\": 1,\n  \"mcpServers\": {\n    \"borer\": {\"command\": \"/opt/borer\", \"args\": []},\n    \"other\": {\"command\": \"node\"}\n  },\n  \"alpha\": [1, 2] /* and me */\n}\n"
        );
        let parsed: serde_json::Value =
            serde_json::from_str(&plain_json(&new)).expect("the result parses");
        assert_eq!(parsed["mcpServers"]["other"]["command"], "node");
        assert_eq!(parsed["zeta"], 1);
        assert_eq!(
            add_json(&new, "mcpServers", ENTRY),
            Ok(Change::Present(Some("/opt/borer".to_owned())))
        );
    }

    /// A missing servers key is made, an empty object filled, and an empty
    /// file written whole; a `/` inside a string is not a comment.
    ///
    /// # Panics
    ///
    /// When a result differs or does not parse.
    #[test]
    fn a_missing_key_an_empty_object_and_an_empty_file_take_the_entry() {
        let made = text(add_json("{\"url\": \"http://x//y\"}", "servers", ENTRY));
        assert_eq!(
            made,
            "{\n  \"servers\": {\n    \"borer\": {\"command\": \"/opt/borer\", \"args\": []}\n  },\"url\": \"http://x//y\"}"
        );
        let filled = text(add_json(
            "{\r\n  \"context_servers\": {}\r\n}\r\n",
            "context_servers",
            ENTRY,
        ));
        assert_eq!(
            filled,
            "{\r\n  \"context_servers\": {\r\n    \"borer\": {\"command\": \"/opt/borer\", \"args\": []}\r\n  }\r\n}\r\n"
        );
        let fresh = text(add_json("", "mcpServers", ENTRY));
        let parsed: serde_json::Value = serde_json::from_str(&fresh).expect("parses");
        assert_eq!(parsed["mcpServers"]["borer"]["command"], "/opt/borer");
        let empty_root = text(add_json("{}", "mcpServers", ENTRY));
        assert!(
            serde_json::from_str::<serde_json::Value>(&empty_root).is_ok(),
            "{empty_root}"
        );
    }

    /// A file that is not a JSON object, has a servers member that is not
    /// an object, or does not parse even as JSONC is refused with the
    /// reason.
    ///
    /// # Panics
    ///
    /// When one is edited, or the reason is missing.
    #[test]
    fn what_is_not_a_json_object_is_refused() {
        let refused = |t: &str| add_json(t, "mcpServers", ENTRY).expect_err("refused");
        assert!(refused("[1]").contains("top level is not an object"));
        assert!(refused("{\"mcpServers\": []}").contains("mcpServers member is not an object"));
        assert!(refused("{a: 1}").contains("not plain JSON"));
    }

    /// Trailing commas, as Zed's settings carry them, are read past and
    /// kept; a comma inside a string is not one.
    ///
    /// # Panics
    ///
    /// When the entry is not added, or a byte of the old file is lost.
    #[test]
    fn trailing_commas_are_read_past_and_kept() {
        let old = "{\n  \"theme\": \"One, Dark\",\n  \"context_servers\": {\n    \"x\": {\"command\": \"y\",},\n  },\n  \"tabs\": [1, 2,],\n}\n";
        let new = text(add_json(old, "context_servers", ENTRY));
        assert_eq!(
            new,
            "{\n  \"theme\": \"One, Dark\",\n  \"context_servers\": {\n    \"borer\": {\"command\": \"/opt/borer\", \"args\": []},\n    \"x\": {\"command\": \"y\",},\n  },\n  \"tabs\": [1, 2,],\n}\n"
        );
        let parsed: serde_json::Value = serde_json::from_str(&plain_json(&new)).expect("parses");
        assert_eq!(parsed["theme"], "One, Dark");
    }

    /// The Codex table is appended after what is there, with a literal
    /// string for a path a literal can hold; a table already there, in any
    /// of its spellings, is found; an inline `mcp_servers` is refused.
    ///
    /// # Panics
    ///
    /// When the appended text differs, a present table is added again, or
    /// the inline table is not refused.
    #[test]
    fn the_codex_table_is_appended_once() {
        let old = "model = \"o4\"\n\n[mcp_servers.other]\ncommand = \"node\"";
        let new = text(add_toml(old, r"C:\bin\borer.exe"));
        assert_eq!(
            new,
            "model = \"o4\"\n\n[mcp_servers.other]\ncommand = \"node\"\n\n[mcp_servers.borer]\ncommand = 'C:\\bin\\borer.exe'\nargs = []\n"
        );
        assert_eq!(add_toml(&new, "x"), Ok(Change::Present(None)));
        assert_eq!(
            text(add_toml("", "/it's/borer")),
            "[mcp_servers.borer]\ncommand = \"/it's/borer\"\nargs = []\n"
        );
        for present in [
            "[mcp_servers.\"borer\"]\ncommand = 'x'\n",
            "[mcp_servers.borer.env]\nA = '1'\n",
            "[mcp_servers]\nborer = { command = 'x' }\n",
            "mcp_servers.borer.command = 'x'\n",
        ] {
            assert_eq!(
                add_toml(present, "y"),
                Ok(Change::Present(None)),
                "{present}"
            );
        }
        assert!(
            add_toml("mcp_servers = { a = { command = 'x' } }\n", "y")
                .expect_err("refused")
                .contains("inline table")
        );
        assert_eq!(
            text(add_toml("[other]\nborer = 1\n", "/b")),
            "[other]\nborer = 1\n\n[mcp_servers.borer]\ncommand = '/b'\nargs = []\n"
        );
    }

    /// A dry run writes nothing; an applied change keeps the old file as
    /// `.bak` byte for byte; a second run finds the entry and writes
    /// nothing more; a file that did not exist is created without a copy.
    ///
    /// # Panics
    ///
    /// When a dry run writes, the copy differs from the old file, or a
    /// second run changes anything.
    #[test]
    fn apply_keeps_a_copy_and_runs_once() {
        let dir = scratch("apply");
        let file = dir.join("mcp.json");
        let old = "{\"mcpServers\": {}, \"keep\": true}";
        std::fs::write(&file, old).expect("written");
        let target = Target {
            client: "cursor",
            dir: dir.clone(),
            file: file.clone(),
            format: Format::Json {
                key: "mcpServers",
                typed: true,
            },
        };
        let (said, failed) = register_file(&target, "/opt/borer", false);
        assert!(
            !failed && said.contains("would add \"borer\": {\"type\": \"stdio\""),
            "{said}"
        );
        assert_eq!(std::fs::read_to_string(&file).expect("read"), old);
        assert!(!backup_path(&file).exists());

        let (said, failed) = register_file(&target, "/opt/borer", true);
        assert!(!failed && said.contains("added"), "{said}");
        assert_eq!(
            std::fs::read_to_string(backup_path(&file)).expect("the copy"),
            old
        );
        let new = std::fs::read_to_string(&file).expect("read");
        let parsed: serde_json::Value = serde_json::from_str(&new).expect("parses");
        assert_eq!(parsed["mcpServers"]["borer"]["type"], "stdio");
        assert_eq!(parsed["keep"], true);

        let (said, failed) = register_file(&target, "/opt/borer", true);
        assert!(
            !failed && said.ends_with("already registers borer"),
            "{said}"
        );
        assert_eq!(std::fs::read_to_string(&file).expect("read"), new);
        assert_eq!(
            std::fs::read_to_string(backup_path(&file)).expect("the copy"),
            old
        );
        let (said, _) = register_file(&target, "/elsewhere/borer", true);
        assert!(said.contains("running /opt/borer; left as it is"), "{said}");

        let toml = Target {
            client: "codex cli",
            dir: dir.clone(),
            file: dir.join("config.toml"),
            format: Format::Toml,
        };
        let (said, failed) = register_file(&toml, "/opt/borer", true);
        assert!(!failed && said.contains("created with"), "{said}");
        assert!(!backup_path(&toml.file).exists());
        std::fs::remove_dir_all(&dir).ok();
    }

    /// A client is installed when its directory exists, and its file is
    /// where that operating system keeps it; Claude Code's file sits
    /// beside its directory.
    ///
    /// # Panics
    ///
    /// When a client is found that is not there, or a file is misplaced.
    #[test]
    fn installed_clients_are_found_by_their_directories() {
        let home = scratch("targets");
        let env = Env {
            home: Some(home.clone()),
            appdata: Some(home.join("roaming")),
            local: Some(home.join("local")),
            config: Some(home.join(".config")),
            codex: Some(home.join(".codex")),
        };
        for dir in [
            ".claude",
            ".cursor",
            ".codex",
            ".config/zed",
            "roaming/Code/User",
        ] {
            std::fs::create_dir_all(home.join(dir)).expect("made");
        }
        let files = |os: Os| {
            let (found, missing) = targets(os, &env);
            let found: Vec<(&str, PathBuf)> =
                found.into_iter().map(|t| (t.client, t.file)).collect();
            (found, missing)
        };
        let (linux, missing) = files(Os::Linux);
        assert_eq!(
            linux,
            vec![
                ("claude code", home.join(".claude.json")),
                ("cursor", home.join(".cursor").join("mcp.json")),
                ("codex cli", home.join(".codex").join("config.toml")),
                ("zed", home.join(".config/zed").join("settings.json")),
            ]
        );
        assert!(
            missing.contains(&"vs code") && missing.contains(&"claude desktop"),
            "{missing:?}"
        );
        let (windows, _) = files(Os::Windows);
        assert!(
            windows.contains(&("vs code", home.join("roaming/Code/User").join("mcp.json"))),
            "{windows:?}"
        );
        assert!(!windows.iter().any(|(c, _)| *c == "zed"), "{windows:?}");
        std::fs::create_dir_all(home.join("local/Packages/Claude_abc/LocalCache/Roaming/Claude"))
            .expect("made");
        let (windows, _) = files(Os::Windows);
        assert!(
            windows.contains(&(
                "claude desktop",
                home.join("local/Packages/Claude_abc/LocalCache/Roaming/Claude")
                    .join("claude_desktop_config.json")
            )),
            "{windows:?}"
        );
        let mac = Path::new("Library/Application Support/Code/User");
        std::fs::create_dir_all(home.join(mac)).expect("made");
        let (mac_found, _) = files(Os::Mac);
        assert!(
            mac_found.contains(&("vs code", home.join(mac).join("mcp.json"))),
            "{mac_found:?}"
        );
        std::fs::remove_dir_all(&home).ok();
    }
}
