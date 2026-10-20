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
//! An edit only inserts or removes the `borer` entry in the file's text,
//! so the rest of the file, comments, trailing commas and key order
//! included, stays byte for byte. An entry that runs another program is
//! replaced when that program no longer exists or `--replace` asks, and
//! left as it is otherwise; `--remove` takes the entry out. A file that
//! does not parse even as JSONC is not touched; the report then gives the
//! entry to add by hand. An applied run ends by naming the clients to
//! restart, since none reads its configuration again while it runs.

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

/// What `setup` does with each client's `borer` entry.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Mode {
    /// Add the entry where there is none, and replace one whose program no
    /// longer exists.
    Add,
    /// Add the entry, and replace one that runs any other program.
    Replace,
    /// Take the entry out.
    Remove,
}

/// Seconds Codex waits for borer to start, written into its table.
const CODEX_STARTUP_SEC: u32 = 30;

/// Seconds Codex waits for one tool call, written into its table: its
/// default of 60 is less than the first analysis of a large binary takes.
const CODEX_TOOL_SEC: u32 = 600;

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

/// Finds a member of a JSON object by name.
///
/// # Arguments
///
/// * `plain` - The text as strict JSON ([`plain_json`]).
/// * `open` - The position of the object's `{`.
/// * `name` - The member's key.
///
/// # Returns
///
/// Where the member's key opens and where its value ends, or `None` when
/// the object has no such member.
fn member_span(plain: &str, open: usize, name: &str) -> Option<(usize, usize)> {
    let bytes = plain.as_bytes();
    let string_end = |from: usize| {
        let mut j = from + 1;
        while let Some(&c) = bytes.get(j) {
            match c {
                b'\\' => j += 2,
                b'"' => return Some(j),
                _ => j += 1,
            }
        }
        None
    };
    let mut depth = 0usize;
    let mut key: Option<(usize, bool)> = None;
    let mut i = open + 1;
    while let Some(&c) = bytes.get(i) {
        match c {
            b'"' => {
                let end = string_end(i)?;
                if depth == 0 && key.is_none() {
                    key = Some((i, plain.get(i + 1..end) == Some(name)));
                }
                i = end + 1;
            }
            b'{' | b'[' => {
                depth += 1;
                i += 1;
            }
            b'}' | b']' if depth > 0 => {
                depth -= 1;
                i += 1;
            }
            b',' | b'}' | b']' if depth == 0 => {
                if let Some((at, true)) = key {
                    return Some((at, plain[..i].trim_end().len()));
                }
                if c != b',' {
                    return None;
                }
                key = None;
                i += 1;
            }
            _ => i += 1,
        }
    }
    None
}

/// Takes the server entry out of a JSON configuration's text.
///
/// The member goes with the comma that joined it to its neighbour;
/// nothing else in the text changes.
///
/// # Arguments
///
/// * `text` - The file's text, possibly with comments.
/// * `key` - The top-level key holding the servers.
///
/// # Returns
///
/// The text without the entry.
///
/// # Errors
///
/// When the text has no servers object naming `borer`, or the text left
/// is not JSON.
fn remove_json(text: &str, key: &str) -> Result<String, String> {
    let plain = plain_json(text);
    let open = member_open(&plain, key).ok_or_else(|| format!("it has no {key} object"))?;
    let (start, end) =
        member_span(&plain, open, NAME).ok_or_else(|| format!("its {key} names no {NAME}"))?;
    let next = end + plain[end..].len() - plain[end..].trim_start().len();
    let before = plain[..start].trim_end().len();
    let (from, to) = if plain.as_bytes().get(next) == Some(&b',') {
        let after = next + 1;
        (
            start,
            after + plain[after..].len() - plain[after..].trim_start().len(),
        )
    } else if before > 0 && plain.as_bytes().get(before - 1) == Some(&b',') {
        (before - 1, end)
    } else {
        (open + 1, end)
    };
    let out = format!("{}{}", &text[..from], &text[to..]);
    let gone = serde_json::from_str::<serde_json::Value>(&plain_json(&out))
        .ok()
        .is_some_and(|v| v.get(key).is_some_and(|s| s.get(NAME).is_none()));
    if gone {
        Ok(out)
    } else {
        Err(format!("taking {NAME} out of {key} did not give JSON"))
    }
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
                return Ok(Change::Present(toml_command(text)));
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
        "[{own}]{nl}command = {}{nl}args = []{nl}startup_timeout_sec = {CODEX_STARTUP_SEC}{nl}tool_timeout_sec = {CODEX_TOOL_SEC}{nl}",
        toml_string(command)
    );
    Ok(Change::Text(out))
}

/// The squashed name of a TOML table header line, `None` for any other
/// line: quotes and spaces dropped, so `[mcp_servers."borer"]` reads
/// `mcp_servers.borer`.
///
/// # Arguments
///
/// * `line` - One line of the file.
fn toml_header(line: &str) -> Option<String> {
    let header = line.trim().strip_prefix('[')?;
    Some(
        header
            .trim_start_matches('[')
            .split(']')
            .next()
            .unwrap_or_default()
            .chars()
            .filter(|c| !matches!(c, ' ' | '\t' | '"' | '\''))
            .collect(),
    )
}

/// Reads the program the `[mcp_servers.borer]` table runs.
///
/// # Arguments
///
/// * `text` - A Codex `config.toml`'s text.
///
/// # Returns
///
/// The `command` value of the table, or `None` when there is no such
/// table or it states no command as a plain string.
fn toml_command(text: &str) -> Option<String> {
    let own = format!("mcp_servers.{NAME}");
    let mut inside = false;
    for line in text.lines() {
        if let Some(name) = toml_header(line) {
            inside = name == own;
            continue;
        }
        let Some((key, value)) = line.split_once('=') else {
            continue;
        };
        if inside && key.trim() == "command" {
            let value = value.trim();
            return match value.strip_prefix('\'') {
                Some(rest) => rest.strip_suffix('\'').map(str::to_owned),
                None => serde_json::from_str::<String>(value).ok(),
            };
        }
    }
    None
}

/// Takes the `[mcp_servers.borer]` table, and its sub-tables, out of a
/// Codex `config.toml`'s text, with the blank line `setup` put before it.
///
/// # Arguments
///
/// * `text` - The file's text.
///
/// # Returns
///
/// The text without the table.
///
/// # Errors
///
/// When the file has no such table: an entry spelled as a key inside
/// `[mcp_servers]` or as a dotted key is left to remove by hand.
fn remove_toml(text: &str) -> Result<String, String> {
    let own = format!("mcp_servers.{NAME}");
    let ours = |name: &str| name == own || name.starts_with(&format!("{own}."));
    let lines: Vec<&str> = text.split_inclusive('\n').collect();
    let start = lines
        .iter()
        .position(|l| toml_header(l).is_some_and(|n| ours(&n)))
        .ok_or_else(|| format!("it has no [{own}] table; remove the {NAME} entry by hand"))?;
    let end = lines
        .iter()
        .enumerate()
        .skip(start + 1)
        .find(|(_, l)| toml_header(l).is_some_and(|n| !ours(&n)))
        .map_or(lines.len(), |(i, _)| i);
    let from = if start > 0 && lines[start - 1].trim().is_empty() {
        start - 1
    } else {
        start
    };
    let mut out = lines[..from].concat();
    out.push_str(&lines[end..].concat());
    Ok(out)
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
        Format::Toml => format!(
            "[mcp_servers.{NAME}] command = {}, startup_timeout_sec = {CODEX_STARTUP_SEC}, tool_timeout_sec = {CODEX_TOOL_SEC}",
            toml_string(command)
        ),
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

/// Whether an entry's program is gone, so the entry can only fail.
///
/// # Arguments
///
/// * `command` - The program the entry runs.
fn stale(command: &str) -> bool {
    !Path::new(command).exists()
}

/// Adds, replaces or removes the entry in one client's file, or says what
/// that would do.
///
/// # Arguments
///
/// * `target` - The client's file.
/// * `command` - The program the entry runs.
/// * `mode` - What to do with the entry ([`Mode`]).
/// * `apply` - Write the change; otherwise only describe it.
///
/// # Returns
///
/// The report's text for the client, after its name; whether the client
/// failed (a file that could not be read, edited or written); and whether
/// the file changed, or would.
fn register_file(target: &Target, command: &str, mode: Mode, apply: bool) -> (String, bool, bool) {
    let file = target.file.display();
    let existed = target.file.is_file();
    let text = if existed {
        match std::fs::read_to_string(&target.file) {
            Ok(text) => text,
            Err(e) => return (format!("{file}: cannot read it: {e}"), true, false),
        }
    } else {
        String::new()
    };
    let entry = entry(target.format, command);
    let (change, place) = match target.format {
        Format::Json { key, .. } => (add_json(&text, key, &entry), format!("under {key}")),
        Format::Toml => (add_toml(&text, command), "as a table".to_owned()),
    };
    let added = match target.format {
        Format::Json { .. } => format!("\"{NAME}\": {entry}"),
        Format::Toml => entry.clone(),
    };
    let removed = || match target.format {
        Format::Json { key, .. } => remove_json(&text, key),
        Format::Toml => remove_toml(&text),
    };
    let (new, done, would) = match (change, mode) {
        (Ok(Change::Text(_)), Mode::Remove) => {
            return (format!("{file}: registers no {NAME}"), false, false);
        }
        (Ok(Change::Present(_)), Mode::Remove) => match removed() {
            Ok(new) => (
                new,
                format!("removed {NAME}"),
                format!("would remove {NAME}"),
            ),
            Err(why) => return (format!("{file}: cannot edit it: {why}"), true, false),
        },
        (Ok(Change::Text(new)), Mode::Add | Mode::Replace) => {
            let verb = if existed {
                "would add"
            } else {
                "would create it with"
            };
            let done = if existed { "added" } else { "created with" };
            (
                new,
                format!("{done} {added} {place}"),
                format!("{verb} {added} {place}"),
            )
        }
        (Ok(Change::Present(Some(other))), Mode::Add | Mode::Replace)
            if other != command && (mode == Mode::Replace || stale(&other)) =>
        {
            let why = if stale(&other) {
                "which no longer exists"
            } else {
                "as --replace asks"
            };
            let replaced = removed().and_then(|without| match target.format {
                Format::Json { key, .. } => add_json(&without, key, &entry),
                Format::Toml => add_toml(&without, command),
            });
            match replaced {
                Ok(Change::Text(new)) => (
                    new,
                    format!("replaced {other} ({why}) with {added}"),
                    format!("would replace {other} ({why}) with {added}"),
                ),
                Ok(Change::Present(_)) | Err(_) => {
                    return (
                        format!(
                            "{file}: cannot replace {other}; set it to {entry} {place} by hand"
                        ),
                        true,
                        false,
                    );
                }
            }
        }
        (Ok(Change::Present(Some(other))), Mode::Add | Mode::Replace) if other != command => {
            return (
                format!(
                    "{file}: already registers {NAME}, running {other}; left as it is (setup --apply --replace points it here)"
                ),
                false,
                false,
            );
        }
        (Ok(Change::Present(_)), Mode::Add | Mode::Replace) => {
            return (format!("{file}: already registers {NAME}"), false, false);
        }
        (Err(why), Mode::Add | Mode::Replace | Mode::Remove) => {
            return (
                format!("{file}: cannot edit it: {why}; add {entry} {place} by hand"),
                true,
                false,
            );
        }
    };
    if !apply {
        return (format!("{file}: {would}"), false, true);
    }
    let backup = backup_path(&target.file);
    if existed && let Err(e) = std::fs::copy(&target.file, &backup) {
        return (
            format!(
                "{file}: cannot keep a copy at {}: {e}; not changed",
                backup.display()
            ),
            true,
            false,
        );
    }
    if let Err(e) = std::fs::write(&target.file, new) {
        return (format!("{file}: cannot write it: {e}"), true, false);
    }
    if existed {
        (
            format!("{file}: {done}; the old file is {}", backup.display()),
            false,
            true,
        )
    } else {
        (format!("{file}: {done}"), false, true)
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

/// Reads the program a `claude mcp get` report says a server runs.
///
/// # Arguments
///
/// * `report` - The command's standard output.
///
/// # Returns
///
/// The `Command:` line's value, or `None` when the report has none.
fn claude_command(report: &str) -> Option<String> {
    report
        .lines()
        .find_map(|l| l.trim().strip_prefix("Command:"))
        .map(|c| c.trim().to_owned())
        .filter(|c| !c.is_empty())
}

/// Runs one `claude mcp` command for its status and first message line.
///
/// # Arguments
///
/// * `claude` - The `claude` program.
/// * `args` - The arguments after `claude`.
///
/// # Returns
///
/// Whether it succeeded, with its standard output on success and its
/// first error line otherwise.
///
/// # Errors
///
/// When the program cannot be run.
fn run_claude(claude: &Path, args: &[&str]) -> std::io::Result<(bool, String)> {
    let out = Command::new(claude)
        .args(args)
        .stdin(Stdio::null())
        .output()?;
    if out.status.success() {
        return Ok((true, String::from_utf8_lossy(&out.stdout).into_owned()));
    }
    let err = String::from_utf8_lossy(&out.stderr);
    let why = err
        .lines()
        .find(|l| !l.trim().is_empty())
        .unwrap_or("no message");
    Ok((false, format!("{} ({})", why.trim(), out.status)))
}

/// Registers borer with Claude Code through its CLI, replaces or removes
/// it, or says what that would run.
///
/// `claude mcp get borer` succeeds when a server by that name is already
/// configured and names its command; `claude mcp add --scope user` adds it
/// for every project and `claude mcp remove --scope user` takes it out.
///
/// # Arguments
///
/// * `claude` - The `claude` program.
/// * `command` - The program the server runs.
/// * `mode` - What to do with the entry ([`Mode`]).
/// * `apply` - Run the commands; otherwise only describe them.
///
/// # Returns
///
/// The report's text for Claude Code, after its name, whether it failed,
/// and whether its registration changed, or would.
fn register_claude_cli(
    claude: &Path,
    command: &str,
    mode: Mode,
    apply: bool,
) -> (String, bool, bool) {
    let add = ["mcp", "add", "--scope", "user", NAME, "--", command];
    let remove = ["mcp", "remove", "--scope", "user", NAME];
    let present = match run_claude(claude, &["mcp", "get", NAME]) {
        Ok((true, report)) => Some(claude_command(&report)),
        Ok((false, _)) => None,
        Err(e) => return (format!("cannot run {}: {e}", claude.display()), true, false),
    };
    let steps: Vec<&[&str]> = match (present, mode) {
        (None, Mode::Remove) => {
            return (
                format!("claude mcp get {NAME}: not registered"),
                false,
                false,
            );
        }
        (Some(_), Mode::Remove) => vec![&remove],
        (None, Mode::Add | Mode::Replace) => vec![&add],
        (Some(Some(other)), Mode::Add | Mode::Replace)
            if other != command && (mode == Mode::Replace || stale(&other)) =>
        {
            vec![&remove, &add]
        }
        (Some(Some(other)), Mode::Add | Mode::Replace) if other != command => {
            return (
                format!(
                    "claude mcp get {NAME}: registered, running {other}; left as it is (setup --apply --replace points it here)"
                ),
                false,
                false,
            );
        }
        (Some(_), Mode::Add | Mode::Replace) => {
            return (
                format!("claude mcp get {NAME}: already registered"),
                false,
                false,
            );
        }
    };
    let shown = steps
        .iter()
        .map(|args| format!("claude {}", args.join(" ")))
        .collect::<Vec<_>>()
        .join(", then ");
    if !apply {
        return (format!("would run: {shown}"), false, true);
    }
    for args in &steps {
        match run_claude(claude, args) {
            Ok((true, _)) => {}
            Ok((false, why)) => {
                return (
                    format!("claude {} failed: {why}", args.join(" ")),
                    true,
                    false,
                );
            }
            Err(e) => return (format!("cannot run {}: {e}", claude.display()), true, false),
        }
    }
    (format!("ran: {shown}"), false, true)
}

/// What a client needs after its configuration changed, beyond a restart.
///
/// # Arguments
///
/// * `client` - The client, as the report names it.
fn restart_note(client: &str) -> &'static str {
    match client {
        "claude desktop" => " (quit it from the tray icon, not the window)",
        "cursor" => " (then turn borer on under Settings > MCP)",
        "vs code" | "vs code insiders" => " (or run MCP: List Servers and start borer)",
        _ => "",
    }
}

/// Registers this binary with every installed client, replaces a stale
/// registration, or removes it: the CLI's `setup`.
///
/// # Arguments
///
/// * `mode` - What to do with each client's entry ([`Mode`]).
/// * `apply` - Make the changes; otherwise report them only.
///
/// # Returns
///
/// The report, one line per installed client after a header and with the
/// clients not found and, after an applied change, the clients to restart
/// last, and how many clients failed.
///
/// # Errors
///
/// When this binary's path does not read or is not UTF-8, which a
/// configuration file cannot hold.
pub(crate) fn setup(mode: Mode, apply: bool) -> anyhow::Result<(String, usize)> {
    let exe = std::env::current_exe()?;
    let command = exe
        .to_str()
        .ok_or_else(|| anyhow::anyhow!("{} is not a UTF-8 path", exe.display()))?;
    let (found, mut missing) = targets(Os::HOST, &Env::read());
    let claude = claude_cli();
    let what = match mode {
        Mode::Add => format!("registering {command} as the MCP server {NAME}"),
        Mode::Replace => {
            format!("registering {command} as the MCP server {NAME}, replacing another")
        }
        Mode::Remove => format!("removing the MCP server {NAME}"),
    };
    let flag = match mode {
        Mode::Add => "--apply",
        Mode::Replace => "--apply --replace",
        Mode::Remove => "--apply --remove",
    };
    let mut out = if apply {
        format!("# setup: {what}\n")
    } else {
        format!("# setup: dry run; `borer setup {flag}` goes on {what}\n")
    };
    let mut failed = 0;
    let mut changed: Vec<String> = Vec::new();
    let mut line = |client: &str, (text, bad, did): (String, bool, bool)| {
        failed += usize::from(bad);
        if did {
            changed.push(format!("{client}{}", restart_note(client)));
        }
        let _ = writeln!(out, "{client:<CLIENT_WIDTH$} {text}");
    };
    if let Some(claude) = &claude {
        missing.retain(|c| *c != "claude code");
        line(
            "claude code",
            register_claude_cli(claude, command, mode, apply),
        );
    }
    for target in &found {
        if claude.is_some() && target.client == "claude code" {
            continue;
        }
        line(target.client, register_file(target, command, mode, apply));
    }
    if found.is_empty() && claude.is_none() {
        out.push_str("# no agent client found; add the server by hand: see README.md\n");
    }
    if !missing.is_empty() {
        let _ = writeln!(out, "# not found: {}", missing.join(", "));
    }
    if apply && !changed.is_empty() {
        let _ = writeln!(
            out,
            "# restart each changed client to load it: {}",
            changed.join("; ")
        );
    }
    Ok((out, failed))
}

#[cfg(test)]
mod tests {
    use std::path::{Path, PathBuf};

    use super::{
        Change, Env, Format, Mode, Os, Target, add_json, add_toml, backup_path, claude_command,
        plain_json, register_file, remove_json, remove_toml, targets, toml_command,
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
            "model = \"o4\"\n\n[mcp_servers.other]\ncommand = \"node\"\n\n[mcp_servers.borer]\ncommand = 'C:\\bin\\borer.exe'\nargs = []\nstartup_timeout_sec = 30\ntool_timeout_sec = 600\n"
        );
        assert_eq!(
            add_toml(&new, "x"),
            Ok(Change::Present(Some(r"C:\bin\borer.exe".to_owned())))
        );
        assert_eq!(
            text(add_toml("", "/it's/borer")),
            "[mcp_servers.borer]\ncommand = \"/it's/borer\"\nargs = []\nstartup_timeout_sec = 30\ntool_timeout_sec = 600\n"
        );
        assert_eq!(
            add_toml("[mcp_servers.\"borer\"]\ncommand = 'x'\n", "y"),
            Ok(Change::Present(Some("x".to_owned())))
        );
        for present in [
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
            "[other]\nborer = 1\n\n[mcp_servers.borer]\ncommand = '/b'\nargs = []\nstartup_timeout_sec = 30\ntool_timeout_sec = 600\n"
        );
    }

    /// The entry comes out of a servers object with the comma that joined
    /// it, wherever it sits, and every other byte stays; a file naming no
    /// `borer` is refused.
    ///
    /// # Panics
    ///
    /// When a removal leaves a byte it should not, or takes one it should
    /// keep.
    #[test]
    fn an_entry_comes_out_with_its_comma_and_nothing_else() {
        let first = "{\n  \"mcpServers\": {\n    \"borer\": {\"command\": \"/b\"},\n    \"other\": {}\n  }\n}\n";
        assert_eq!(
            remove_json(first, "mcpServers").expect("removed"),
            "{\n  \"mcpServers\": {\n    \"other\": {}\n  }\n}\n"
        );
        let last =
            "{\"mcpServers\": {\"other\": {}, // keep\n \"borer\": {\"args\": [1, {}]}}, \"x\": 1}";
        assert_eq!(
            remove_json(last, "mcpServers").expect("removed"),
            "{\"mcpServers\": {\"other\": {}}, \"x\": 1}"
        );
        let only = "{\"servers\": {\"borer\": {\"type\": \"stdio\"}}}";
        assert_eq!(
            remove_json(only, "servers").expect("removed"),
            "{\"servers\": {}}"
        );
        assert!(remove_json("{\"mcpServers\": {\"other\": {}}}", "mcpServers").is_err());
        let added = add_json(first, "mcpServers", "{}").map(|c| matches!(c, Change::Present(_)));
        assert_eq!(added, Ok(true));
    }

    /// The Codex table comes out with its sub-tables and the blank line
    /// before it, and the command it runs reads in either string form; an
    /// entry spelled as a key is left to remove by hand.
    ///
    /// # Panics
    ///
    /// When the table, a neighbour or the command reads otherwise.
    #[test]
    fn the_codex_table_comes_out_whole() {
        let text = "model = 'o4'\n\n[mcp_servers.borer]\ncommand = \"C:\\\\b.exe\"\nargs = []\n[mcp_servers.borer.env]\nA = '1'\n[other]\nx = 1\n";
        assert_eq!(toml_command(text).as_deref(), Some(r"C:\b.exe"));
        assert_eq!(
            remove_toml(text).expect("removed"),
            "model = 'o4'\n[other]\nx = 1\n"
        );
        assert_eq!(
            toml_command("[mcp_servers.borer]\ncommand = '/b'\n").as_deref(),
            Some("/b")
        );
        assert!(remove_toml("[mcp_servers]\nborer = { command = 'x' }\n").is_err());
    }

    /// A `claude mcp get` report names the program on its `Command:` line.
    ///
    /// # Panics
    ///
    /// When the program reads otherwise.
    #[test]
    fn the_claude_report_names_the_command() {
        let report = "borer:\n  Scope: User config\n  Type: stdio\n  Command: C:\\bin\\borer.exe\n  Args: \n";
        assert_eq!(claude_command(report).as_deref(), Some(r"C:\bin\borer.exe"));
        assert_eq!(claude_command("borer:\n  Type: http\n"), None);
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
        let (said, failed, _) = register_file(&target, "/opt/borer", Mode::Add, false);
        assert!(
            !failed && said.contains("would add \"borer\": {\"type\": \"stdio\""),
            "{said}"
        );
        assert_eq!(std::fs::read_to_string(&file).expect("read"), old);
        assert!(!backup_path(&file).exists());

        let (said, failed, changed) = register_file(&target, "/opt/borer", Mode::Add, true);
        assert!(!failed && changed && said.contains("added"), "{said}");
        assert_eq!(
            std::fs::read_to_string(backup_path(&file)).expect("the copy"),
            old
        );
        let new = std::fs::read_to_string(&file).expect("read");
        let parsed: serde_json::Value = serde_json::from_str(&new).expect("parses");
        assert_eq!(parsed["mcpServers"]["borer"]["type"], "stdio");
        assert_eq!(parsed["keep"], true);

        let (said, failed, changed) = register_file(&target, "/opt/borer", Mode::Add, true);
        assert!(
            !failed && !changed && said.ends_with("already registers borer"),
            "{said}"
        );
        assert_eq!(std::fs::read_to_string(&file).expect("read"), new);
        assert_eq!(
            std::fs::read_to_string(backup_path(&file)).expect("the copy"),
            old
        );
        let (said, _, _) = register_file(&target, "/elsewhere/borer", Mode::Add, true);
        assert!(
            said.contains("replaced /opt/borer (which no longer exists)"),
            "{said}"
        );
        let alive = std::env::current_exe().expect("the test binary");
        let alive = alive.to_str().expect("utf-8");
        let (said, _, _) = register_file(&target, alive, Mode::Add, true);
        assert!(
            said.contains("replaced /elsewhere/borer (which no longer exists)"),
            "{said}"
        );
        let (said, _, changed) = register_file(&target, "/third/borer", Mode::Add, true);
        assert!(
            !changed && said.contains(&format!("running {alive}; left as it is")),
            "{said}"
        );
        let other = dir.to_str().expect("utf-8");
        let (said, _, changed) = register_file(&target, other, Mode::Replace, true);
        assert!(changed && said.contains("as --replace asks"), "{said}");
        let (said, failed, changed) = register_file(&target, "/any", Mode::Remove, true);
        assert!(
            !failed && changed && said.contains("removed borer"),
            "{said}"
        );
        let left: serde_json::Value =
            serde_json::from_str(&std::fs::read_to_string(&file).expect("read")).expect("parses");
        assert!(left["mcpServers"].get("borer").is_none(), "{left}");
        assert_eq!(left["keep"], true);
        let (said, _, changed) = register_file(&target, "/any", Mode::Remove, true);
        assert!(!changed && said.ends_with("registers no borer"), "{said}");

        let toml = Target {
            client: "codex cli",
            dir: dir.clone(),
            file: dir.join("config.toml"),
            format: Format::Toml,
        };
        let (said, failed, _) = register_file(&toml, "/opt/borer", Mode::Add, true);
        assert!(!failed && said.contains("created with"), "{said}");
        assert!(
            std::fs::read_to_string(&toml.file)
                .expect("read")
                .contains("tool_timeout_sec = 600"),
            "{said}"
        );
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
