//! `OpenCode`.
//!
//! Its file is `opencode.json` (or an `opencode.jsonc` already there) in
//! `$OPENCODE_CONFIG_DIR`, else `opencode` in the configuration directory,
//! `~/.config` on Windows too. Servers sit under `mcp`, a local one with
//! its command as an array.

use std::path::PathBuf;

use serde::Serialize;

use super::client::{Client, Format, json_or_jsonc};
use super::env::{Env, Os};
use super::jsonc::inline;

/// `OpenCode`.
#[derive(Debug)]
pub(super) struct OpenCode;

/// How `OpenCode` reaches a server: `local` runs it.
#[derive(Debug, Clone, Copy, Serialize)]
#[serde(rename_all = "lowercase")]
enum Kind {
    /// A program `OpenCode` starts and talks to over stdio.
    Local,
}

/// An `OpenCode` server entry.
#[derive(Debug, Serialize)]
struct Entry<'a> {
    /// How it is reached.
    #[serde(rename = "type")]
    kind: Kind,
    /// The program and its arguments, as one array.
    command: [&'a str; 1],
    /// Whether it starts with `OpenCode`.
    enabled: bool,
}

impl Client for OpenCode {
    fn name(&self) -> &'static str {
        "opencode"
    }

    fn place(&self, _: Os, env: &Env) -> Option<(PathBuf, PathBuf)> {
        json_or_jsonc(env.opencode.clone(), "opencode")
    }

    fn format(&self) -> Format {
        Format::Json { key: "mcp" }
    }

    fn entry(&self, command: &str) -> String {
        inline(&Entry {
            kind: Kind::Local,
            command: [command],
            enabled: true,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::super::client::Client as _;
    use super::super::env::{Env, Os};
    use super::super::jsonc::add_json;
    use super::super::{Change, scratch};
    use super::OpenCode;

    /// The entry is a local server with its command as an array, and an
    /// entry already there is read back through that array.
    ///
    /// # Panics
    ///
    /// When the entry or the command read back differs.
    #[test]
    fn the_entry_is_local_with_an_array_command() {
        let entry = OpenCode.entry(r"C:\b\borer.exe");
        assert_eq!(
            entry,
            r#"{"type": "local", "command": ["C:\\b\\borer.exe"], "enabled": true}"#
        );
        let text = format!("{{\"mcp\": {{\"borer\": {entry}}}}}");
        assert_eq!(
            add_json(&text, "mcp", "{}"),
            Ok(Change::Present(Some(r"C:\b\borer.exe".to_owned())))
        );
    }

    /// An `opencode.jsonc` alone is the file; with none, or both, it is
    /// `opencode.json`.
    ///
    /// # Panics
    ///
    /// When another file is picked.
    #[test]
    fn an_existing_jsonc_is_kept() {
        let dir = scratch("opencode");
        let env = Env {
            opencode: Some(dir.clone()),
            ..Env::default()
        };
        let file = || OpenCode.place(Os::Linux, &env).map(|(_, f)| f);
        assert_eq!(file(), Some(dir.join("opencode.json")));
        std::fs::write(dir.join("opencode.jsonc"), "{}").expect("written");
        assert_eq!(file(), Some(dir.join("opencode.jsonc")));
        std::fs::write(dir.join("opencode.json"), "{}").expect("written");
        assert_eq!(file(), Some(dir.join("opencode.json")));
        std::fs::remove_dir_all(&dir).ok();
    }
}
