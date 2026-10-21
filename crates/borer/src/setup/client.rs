//! What every agent client `setup` knows has in common, and the list of
//! them.

use std::path::PathBuf;

use serde::Serialize;

use super::claude::{ClaudeCode, ClaudeDesktop};
use super::codex::Codex;
use super::cursor::Cursor;
use super::devin::Devin;
use super::env::{Env, Os};
use super::gemini::Gemini;
use super::opencode::OpenCode;
use super::pi::Pi;
use super::vscode::VsCode;
use super::windsurf::Windsurf;
use super::zed::Zed;

/// How a client's file holds its servers.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum Format {
    /// A JSON object of servers under a top-level key.
    Json {
        /// The top-level key: `mcpServers`, `servers`, `context_servers` or
        /// `mcp`.
        key: &'static str,
    },
    /// Codex's TOML: a `[mcp_servers.borer]` table.
    Toml,
}

/// An agent client borer registers with.
pub(super) trait Client: Sync + std::fmt::Debug {
    /// The client, as the report names it.
    fn name(&self) -> &'static str;

    /// The directory whose existence means the client is installed, and
    /// the file the entry goes in.
    ///
    /// # Arguments
    ///
    /// * `os` - Whose paths to use.
    /// * `env` - The directories.
    ///
    /// # Returns
    ///
    /// Both, or `None` when the directory has no known base.
    fn place(&self, os: Os, env: &Env) -> Option<(PathBuf, PathBuf)>;

    /// How the file holds its servers.
    fn format(&self) -> Format;

    /// The entry the file gets, as the file writes it.
    ///
    /// # Arguments
    ///
    /// * `command` - The program the entry runs.
    fn entry(&self, command: &str) -> String;

    /// What the client needs after its configuration changed, beyond a
    /// restart.
    fn restart_note(&self) -> &'static str {
        ""
    }
}

/// Every client, in report order.
const CLIENTS: [&'static dyn Client; 12] = [
    &ClaudeCode,
    &ClaudeDesktop,
    &Cursor,
    &Windsurf,
    &Devin,
    &VsCode { insiders: false },
    &VsCode { insiders: true },
    &Gemini,
    &Codex,
    &Zed,
    &OpenCode,
    &Pi,
];

/// An installed client's configuration file.
#[derive(Debug, Clone)]
pub(super) struct Target {
    /// The client.
    pub(super) client: &'static dyn Client,
    /// The file the entry goes in.
    pub(super) file: PathBuf,
}

/// A directory and a file in it, for [`Client::place`].
///
/// # Arguments
///
/// * `dir` - The directory, `None` when it has no known base.
/// * `file` - The file's name.
pub(super) fn at(dir: Option<PathBuf>, file: &str) -> Option<(PathBuf, PathBuf)> {
    dir.map(|dir| {
        let file = dir.join(file);
        (dir, file)
    })
}

/// How a server is reached, where a client's entry states it.
#[derive(Debug, Clone, Copy, Serialize)]
#[serde(rename_all = "lowercase")]
pub(super) enum Transport {
    /// A program the client starts and talks to over stdin and stdout.
    Stdio,
}

/// The entry most clients read: the program and no arguments.
#[derive(Debug, Serialize)]
pub(super) struct Stdio<'a> {
    /// The program.
    command: &'a str,
    /// Its arguments: none.
    args: [&'a str; 0],
}

impl<'a> Stdio<'a> {
    /// The entry running `command`.
    ///
    /// # Arguments
    ///
    /// * `command` - The program.
    pub(super) fn new(command: &'a str) -> Self {
        Stdio { command, args: [] }
    }
}

/// The same entry with its transport stated, as Claude Code, Cursor and
/// VS Code write it.
#[derive(Debug, Serialize)]
pub(super) struct TypedStdio<'a> {
    /// How it is reached.
    #[serde(rename = "type")]
    transport: Transport,
    /// The program.
    command: &'a str,
    /// Its arguments: none.
    args: [&'a str; 0],
}

impl<'a> TypedStdio<'a> {
    /// The entry running `command`.
    ///
    /// # Arguments
    ///
    /// * `command` - The program.
    pub(super) fn new(command: &'a str) -> Self {
        TypedStdio {
            transport: Transport::Stdio,
            command,
            args: [],
        }
    }
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
pub(super) fn targets(os: Os, env: &Env) -> (Vec<Target>, Vec<&'static str>) {
    let mut found = Vec::new();
    let mut missing = Vec::new();
    for client in CLIENTS {
        match client.place(os, env).filter(|(dir, _)| dir.is_dir()) {
            Some((_, file)) => found.push(Target { client, file }),
            None => missing.push(client.name()),
        }
    }
    (found, missing)
}

#[cfg(test)]
mod tests {
    use std::path::{Path, PathBuf};

    use super::super::env::{Env, Os};
    use super::super::scratch;
    use super::targets;

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
            pi: Some(home.join(".pi/agent")),
            opencode: Some(home.join(".config/opencode")),
        };
        for dir in [
            ".claude",
            ".cursor",
            ".codex",
            ".config/zed",
            ".config/opencode",
            ".pi/agent",
            "roaming/Code/User",
        ] {
            std::fs::create_dir_all(home.join(dir)).expect("made");
        }
        let files = |os: Os| {
            let (found, missing) = targets(os, &env);
            let found: Vec<(&str, PathBuf)> = found
                .into_iter()
                .map(|t| (t.client.name(), t.file))
                .collect();
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
                (
                    "opencode",
                    home.join(".config/opencode").join("opencode.json")
                ),
                ("pi", home.join(".pi/agent").join("mcp.json")),
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
