//! Cline: its VS Code extension, CLI and `JetBrains` plugin alike.
//!
//! The file is `~/.cline/data/settings/cline_mcp_settings.json` (or where
//! `$CLINE_MCP_SETTINGS_PATH`, `$CLINE_DATA_DIR` or `$CLINE_DIR` puts it),
//! servers under `mcpServers`.

use std::path::PathBuf;

use serde::Serialize;

use super::client::{Client, Format, Transport};
use super::env::{Env, Os};
use super::jsonc::inline;

/// Seconds Cline waits for one request, written into the entry: its default
/// of 60 is less than the first analysis of a large binary takes.
const TIMEOUT_SEC: u32 = 600;

/// A Cline server entry. The transport is stated: Cline reads an entry
/// without one as the old SSE kind.
#[derive(Debug, Serialize)]
struct Entry<'a> {
    /// How it is reached.
    #[serde(rename = "type")]
    transport: Transport,
    /// The program.
    command: &'a str,
    /// Its arguments: none.
    args: [&'a str; 0],
    /// Whether it is turned off.
    disabled: bool,
    /// Tools run without asking: none.
    #[serde(rename = "autoApprove")]
    auto_approve: [&'a str; 0],
    /// Seconds one request may take.
    timeout: u32,
}

/// Cline.
#[derive(Debug)]
pub(super) struct Cline;

impl Client for Cline {
    fn name(&self) -> &'static str {
        "cline"
    }

    fn place(&self, _: Os, env: &Env) -> Option<(PathBuf, PathBuf)> {
        if let Some(file) = env.var("CLINE_MCP_SETTINGS_PATH") {
            return Some((file.parent()?.to_path_buf(), file));
        }
        let (dir, data) = match env.var("CLINE_DATA_DIR") {
            Some(data) => (data.clone(), data),
            None => {
                let dir = env.var("CLINE_DIR").or_else(|| env.home(".cline"))?;
                let data = dir.join("data");
                (dir, data)
            }
        };
        Some((dir, data.join("settings").join("cline_mcp_settings.json")))
    }

    fn format(&self) -> Format {
        Format::Json { key: "mcpServers" }
    }

    fn entry(&self, command: &str) -> String {
        inline(&Entry {
            transport: Transport::Stdio,
            command,
            args: [],
            disabled: false,
            auto_approve: [],
            timeout: TIMEOUT_SEC,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::super::client::Client as _;
    use super::super::env::{Env, Os};
    use super::Cline;

    /// A settings file or data folder moved by its variable is where the
    /// entry goes, and its folder is what says Cline is there.
    ///
    /// # Panics
    ///
    /// When a place reads otherwise.
    #[test]
    fn moved_settings_are_followed() {
        let env = |name: &'static str, path: &str| Env {
            home: Some("/h".into()),
            vars: vec![(name, path.into())],
            ..Env::default()
        };
        let place = |e: &Env| Cline.place(Os::Linux, e).expect("a place");
        let (dir, file) = place(&env("CLINE_MCP_SETTINGS_PATH", "/s/m.json"));
        assert_eq!((dir, file), ("/s".into(), "/s/m.json".into()));
        let (dir, file) = place(&env("CLINE_DATA_DIR", "/d"));
        assert_eq!(
            (dir, file),
            (
                "/d".into(),
                std::path::Path::new("/d/settings/cline_mcp_settings.json").to_path_buf()
            )
        );
        let (dir, _) = place(&Env {
            home: Some("/h".into()),
            ..Env::default()
        });
        assert_eq!(dir, std::path::Path::new("/h/.cline").to_path_buf());
    }
}
