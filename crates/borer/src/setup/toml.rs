//! Editing an `[mcp_servers.borer]` table in a TOML configuration's text.
//!
//! Codex and Grok Build keep their servers so. Without a TOML parser, the
//! table is appended, found by its header and taken out whole.

use std::fmt::Write as _;

use super::{Change, NAME};

/// A string as a TOML value: literal (`'...'`, no escapes, the readable
/// form of a Windows path) when it can be, else basic with escapes.
///
/// # Arguments
///
/// * `s` - The string.
pub(super) fn toml_string(s: &str) -> String {
    if s.contains('\'') || s.chars().any(char::is_control) {
        serde_json::Value::String(s.to_owned()).to_string()
    } else {
        format!("'{s}'")
    }
}

/// Adds the `[mcp_servers.borer]` table to a `config.toml`'s text by
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
/// * `body` - The table's lines after its header, `\n`-separated
///   ([`super::client::Client::entry`]).
///
/// # Returns
///
/// The new text, or that a server named `borer` is already there.
///
/// # Errors
///
/// When `mcp_servers` is an inline table at the top, which a table appended
/// after it cannot extend.
pub(super) fn add_toml(text: &str, body: &str) -> Result<Change, String> {
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
    let _ = write!(out, "[{own}]{nl}");
    for line in body.lines() {
        let _ = write!(out, "{line}{nl}");
    }
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
/// * `text` - A `config.toml`'s text.
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
/// `config.toml`'s text, with the blank line `setup` put before it.
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
pub(super) fn remove_toml(text: &str) -> Result<String, String> {
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

#[cfg(test)]
mod tests {
    use super::super::client::Client as _;
    use super::super::codex::Codex;
    use super::super::{Change, changed_text};
    use super::{add_toml, remove_toml, toml_command};

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
        let new = changed_text(add_toml(old, &Codex.entry(r"C:\bin\borer.exe")));
        assert_eq!(
            new,
            "model = \"o4\"\n\n[mcp_servers.other]\ncommand = \"node\"\n\n[mcp_servers.borer]\ncommand = 'C:\\bin\\borer.exe'\nargs = []\nstartup_timeout_sec = 30\ntool_timeout_sec = 600\n"
        );
        assert_eq!(
            add_toml(&new, &Codex.entry("x")),
            Ok(Change::Present(Some(r"C:\bin\borer.exe".to_owned())))
        );
        assert_eq!(
            changed_text(add_toml("", &Codex.entry("/it's/borer"))),
            "[mcp_servers.borer]\ncommand = \"/it's/borer\"\nargs = []\nstartup_timeout_sec = 30\ntool_timeout_sec = 600\n"
        );
        assert_eq!(
            add_toml(
                "[mcp_servers.\"borer\"]\ncommand = 'x'\n",
                &Codex.entry("y")
            ),
            Ok(Change::Present(Some("x".to_owned())))
        );
        for present in [
            "[mcp_servers.borer.env]\nA = '1'\n",
            "[mcp_servers]\nborer = { command = 'x' }\n",
            "mcp_servers.borer.command = 'x'\n",
        ] {
            assert_eq!(
                add_toml(present, &Codex.entry("y")),
                Ok(Change::Present(None)),
                "{present}"
            );
        }
        assert!(
            add_toml(
                "mcp_servers = { a = { command = 'x' } }\n",
                &Codex.entry("y")
            )
            .expect_err("refused")
            .contains("inline table")
        );
        assert_eq!(
            changed_text(add_toml("[other]\nborer = 1\n", &Codex.entry("/b"))),
            "[other]\nborer = 1\n\n[mcp_servers.borer]\ncommand = '/b'\nargs = []\nstartup_timeout_sec = 30\ntool_timeout_sec = 600\n"
        );
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
}
