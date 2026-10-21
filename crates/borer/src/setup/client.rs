//! What every agent client `setup` knows has in common, and the list of
//! them.

use std::path::PathBuf;

use serde::Serialize;

use super::amp::Amp;
use super::antigravity::Antigravity;
use super::auggie::Auggie;
use super::claude::{ClaudeCode, ClaudeDesktop};
use super::cline::Cline;
use super::codex::Codex;
use super::continuedev::Continue;
use super::copilot::Copilot;
use super::cursor::Cursor;
use super::devin::Devin;
use super::droid::Droid;
use super::env::{Env, Os};
use super::gemini::Gemini;
use super::grok::Grok;
use super::junie::Junie;
use super::kilo::Kilo;
use super::kimi::Kimi;
use super::kiro::Kiro;
use super::lmstudio::LmStudio;
use super::opencode::OpenCode;
use super::pi::Pi;
use super::qwen::Qwen;
use super::roo::Roo;
use super::vscode::VsCode;
use super::warp::Warp;
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
const CLIENTS: [&'static dyn Client; 28] = [
    &ClaudeCode,
    &ClaudeDesktop,
    &Cursor,
    &Windsurf,
    &Devin,
    &VsCode { insiders: false },
    &VsCode { insiders: true },
    &Gemini,
    &Antigravity,
    &Codex,
    &Zed,
    &OpenCode,
    &Pi,
    &Copilot,
    &Grok,
    &Cline,
    &Roo,
    &Kilo,
    &Continue,
    &Amp,
    &Qwen,
    &Kiro,
    &Droid,
    &Kimi,
    &Junie,
    &Auggie,
    &Warp,
    &LmStudio,
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

/// Picks a client's file where it may be written as JSON or JSONC: the
/// `.jsonc` when only it is there, else the `.json`.
///
/// # Arguments
///
/// * `dir` - The client's directory, `None` when it has no known base.
/// * `stem` - The file's name without its extension.
pub(super) fn json_or_jsonc(dir: Option<PathBuf>, stem: &str) -> Option<(PathBuf, PathBuf)> {
    let dir = dir?;
    let jsonc = dir.join(format!("{stem}.jsonc"));
    let json = dir.join(format!("{stem}.json"));
    let file = if jsonc.is_file() && !json.is_file() {
        jsonc
    } else {
        json
    };
    Some((dir, file))
}

#[cfg(test)]
mod tests {
    use std::path::{Path, PathBuf};

    use super::super::env::{Env, Os};
    use super::super::jsonc::add_json;
    use super::super::toml::add_toml;
    use super::super::{Change, scratch};
    use super::{CLIENTS, Format, targets};

    /// Every client's entry is JSON (or a TOML table) that reads back the
    /// command it was written for, as an applied `setup` finds it again.
    ///
    /// # Panics
    ///
    /// When an entry does not read back.
    #[test]
    fn every_entry_reads_back_its_command() {
        let command = r"C:\it's here\borer.exe";
        for client in CLIENTS {
            let entry = client.entry(command);
            let again = match client.format() {
                Format::Json { key } => {
                    let text = format!("{{\"{key}\": {{\"borer\": {entry}}}}}");
                    add_json(&text, key, "{}")
                }
                Format::Toml => {
                    let Ok(Change::Text(text)) = add_toml("", &entry) else {
                        panic!("{}: no table", client.name());
                    };
                    add_toml(&text, &entry)
                }
            };
            assert_eq!(
                again,
                Ok(Change::Present(Some(command.to_owned()))),
                "{}: {entry}",
                client.name()
            );
        }
    }

    /// Each client added for the other agents is found by its folder, its
    /// file where that agent reads it.
    ///
    /// # Panics
    ///
    /// When one is missed or its file is misplaced.
    #[test]
    fn the_other_agents_are_found_where_they_live() {
        let home = scratch("agents");
        let env = Env {
            home: Some(home.clone()),
            config: Some(home.join(".config")),
            local: Some(home.join("local")),
            ..Env::default()
        };
        for dir in [
            ".copilot",
            ".cline",
            ".continue",
            ".qwen",
            ".kiro",
            ".factory",
            ".kimi-code",
            ".junie",
            ".augment",
            ".warp",
            ".grok",
            ".lmstudio",
            ".gemini/antigravity",
            ".config/kilo",
            ".config/amp",
        ] {
            std::fs::create_dir_all(home.join(dir)).expect("made");
        }
        std::fs::write(home.join(".lmstudio-home-pointer"), "").expect("written");
        let (found, _) = targets(Os::Windows, &env);
        let found: Vec<(&str, PathBuf)> = found
            .into_iter()
            .map(|t| (t.client.name(), t.file))
            .collect();
        for want in [
            ("copilot cli", home.join(".copilot/mcp-config.json")),
            (
                "cline",
                home.join(".cline/data/settings/cline_mcp_settings.json"),
            ),
            ("continue", home.join(".continue/mcpServers/borer.json")),
            ("qwen code", home.join(".qwen/settings.json")),
            ("kiro", home.join(".kiro/settings/mcp.json")),
            ("factory droid", home.join(".factory/mcp.json")),
            ("kimi code", home.join(".kimi-code/mcp.json")),
            ("junie", home.join(".junie/mcp/mcp.json")),
            ("augment", home.join(".augment/settings.json")),
            ("warp", home.join(".warp/.mcp.json")),
            ("grok build", home.join(".grok/config.toml")),
            ("lm studio", home.join(".lmstudio/mcp.json")),
            ("antigravity", home.join(".gemini/config/mcp_config.json")),
            ("kilo code", home.join(".config/kilo/kilo.json")),
            ("amp", home.join(".config/amp/settings.json")),
        ] {
            assert!(found.contains(&want), "{want:?} in {found:?}");
        }
        assert!(!found.iter().any(|(c, _)| *c == "gemini cli"), "{found:?}");
        std::fs::write(home.join(".grok/user-settings.json"), "{}").expect("written");
        let (found, _) = targets(Os::Windows, &env);
        assert!(!found.iter().any(|t| t.client.name() == "grok build"));
        std::fs::remove_dir_all(&home).ok();
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
            pi: Some(home.join(".pi/agent")),
            opencode: Some(home.join(".config/opencode")),
            vars: Vec::new(),
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
