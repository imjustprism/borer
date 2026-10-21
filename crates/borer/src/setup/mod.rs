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
//!
//! Each client is a module of its own implementing [`client::Client`]:
//! where its file is, how the file holds its servers and the entry it
//! gets, built from typed structs ([`jsonc::inline`]).

use std::fmt::Write as _;
use std::path::{Path, PathBuf};

use client::{Format, Target};
use env::{Env, Os};
use jsonc::{add_json, remove_json};

mod amp;
mod antigravity;
mod auggie;
mod claude;
mod client;
mod cline;
mod codex;
mod continuedev;
mod copilot;
mod cursor;
mod devin;
mod droid;
mod env;
mod gemini;
mod grok;
mod jsonc;
mod junie;
mod kilo;
mod kimi;
mod kiro;
mod lmstudio;
mod opencode;
mod pi;
mod qwen;
mod roo;
mod toml;
mod vscode;
mod warp;
mod windsurf;
mod zed;

/// The name borer is registered under in every client.
const NAME: &str = "borer";

/// Width of the client column in the report.
const CLIENT_WIDTH: usize = 15;

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

/// What adding the entry to a file's text comes to.
#[derive(Debug, Clone, PartialEq, Eq)]
enum Change {
    /// The file already names a server `borer`, running this command when
    /// the file says.
    Present(Option<String>),
    /// The file's text with the entry added.
    Text(String),
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
/// A bare name (`npx`, `env`) is looked up on `PATH` as the client would
/// run it, with Windows' `PATHEXT` endings; a path is checked as it is.
///
/// # Arguments
///
/// * `command` - The program the entry runs.
fn stale(command: &str) -> bool {
    let path = Path::new(command);
    if path.is_absolute() || path.components().count() > 1 {
        return !path.exists();
    }
    let endings: Vec<String> = if cfg!(windows) {
        let pathext = std::env::var("PATHEXT").unwrap_or_else(|_| ".EXE;.CMD;.BAT".to_owned());
        std::iter::once(String::new())
            .chain(
                pathext
                    .split(';')
                    .filter(|e| !e.is_empty())
                    .map(str::to_owned),
            )
            .collect()
    } else {
        vec![String::new()]
    };
    let found = std::env::var_os("PATH").is_some_and(|dirs| {
        std::env::split_paths(&dirs).any(|dir| {
            endings
                .iter()
                .any(|end| dir.join(format!("{command}{end}")).is_file())
        })
    });
    !found
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
    let format = target.client.format();
    let entry = target.client.entry(command);
    let (change, place) = match format {
        Format::Json { key } => (add_json(&text, key, &entry), format!("under {key}")),
        Format::Toml => (toml::add_toml(&text, &entry), "as a table".to_owned()),
    };
    let added = match format {
        Format::Json { .. } => format!("\"{NAME}\": {entry}"),
        Format::Toml => format!("[mcp_servers.{NAME}] {}", entry.replace('\n', ", ")),
    };
    let removed = || match format {
        Format::Json { key } => remove_json(&text, key),
        Format::Toml => toml::remove_toml(&text),
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
            let replaced = removed().and_then(|without| match format {
                Format::Json { key } => add_json(&without, key, &entry),
                Format::Toml => toml::add_toml(&without, &entry),
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
    write_file(&target.file, existed, &new, &done)
}

/// Writes a client's changed file, first keeping the old one as `.bak`.
///
/// # Arguments
///
/// * `file_path` - The file.
/// * `existed` - Whether it was there before, so has a copy to keep.
/// * `new` - Its new text.
/// * `done` - What changed, for the report.
///
/// # Returns
///
/// The report's text, whether it failed and whether the file changed.
fn write_file(file_path: &Path, existed: bool, new: &str, done: &str) -> (String, bool, bool) {
    let file = file_path.display();
    let backup = backup_path(file_path);
    if existed && let Err(e) = std::fs::copy(file_path, &backup) {
        return (
            format!(
                "{file}: cannot keep a copy at {}: {e}; not changed",
                backup.display()
            ),
            true,
            false,
        );
    }
    if let Some(dir) = file_path.parent()
        && let Err(e) = std::fs::create_dir_all(dir)
    {
        return (format!("{file}: cannot make its folder: {e}"), true, false);
    }
    if let Err(e) = std::fs::write(file_path, new) {
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
    let (found, mut missing) = client::targets(Os::HOST, &Env::read());
    let claude = claude::cli();
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
    let mut line = |client: &str, note: &str, (text, bad, did): (String, bool, bool)| {
        failed += usize::from(bad);
        if did {
            changed.push(format!("{client}{note}"));
        }
        let _ = writeln!(out, "{client:<CLIENT_WIDTH$} {text}");
    };
    if let Some(claude) = &claude {
        missing.retain(|c| *c != "claude code");
        line(
            "claude code",
            "",
            claude::register_cli(claude, command, mode, apply),
        );
    }
    for target in &found {
        let client = target.client;
        if claude.is_some() && client.name() == "claude code" {
            continue;
        }
        line(
            client.name(),
            client.restart_note(),
            register_file(target, command, mode, apply),
        );
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

/// A directory of its own under the temporary directory, emptied.
///
/// # Panics
///
/// When the directory cannot be made.
#[cfg(test)]
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
#[cfg(test)]
fn changed_text(change: Result<Change, String>) -> String {
    match change {
        Ok(Change::Text(t)) => t,
        other => panic!("expected new text, got {other:?}"),
    }
}

#[cfg(test)]
mod tests {
    use super::codex::Codex;
    use super::cursor::Cursor;
    use super::{Mode, Target, backup_path, register_file, scratch, stale};

    /// A bare program name is found on `PATH`, as the client runs it; a
    /// path, or a name nothing on `PATH` holds, is gone.
    ///
    /// # Panics
    ///
    /// When one reads otherwise.
    #[test]
    fn a_bare_command_is_looked_up_on_the_path() {
        assert!(!stale("cargo"));
        assert!(stale("borer-no-such-program-anywhere"));
        assert!(stale("/no/such/dir/borer"));
        let this = std::env::current_exe().expect("the test binary");
        assert!(!stale(this.to_str().expect("utf-8")));
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
            client: &Cursor,
            file: file.clone(),
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
            client: &Codex,
            file: dir.join("config.toml"),
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
}
