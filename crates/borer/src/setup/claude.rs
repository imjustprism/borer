//! Claude Code and Claude Desktop. Claude Code is registered through its
//! own `claude mcp` when `claude` is on `PATH`, else in `~/.claude.json`.

use std::path::{Path, PathBuf};
use std::process::{Command, Stdio as Piped};

use super::client::{Client, Format, Stdio, TypedStdio, at};
use super::env::{Env, Os};
use super::jsonc::inline;
use super::{Mode, NAME, stale};

/// Claude Code.
#[derive(Debug)]
pub(super) struct ClaudeCode;

impl Client for ClaudeCode {
    fn name(&self) -> &'static str {
        "claude code"
    }

    fn place(&self, _: Os, env: &Env) -> Option<(PathBuf, PathBuf)> {
        Some((env.home(".claude")?, env.home(".claude.json")?))
    }

    fn format(&self) -> Format {
        Format::Json { key: "mcpServers" }
    }

    fn entry(&self, command: &str) -> String {
        inline(&TypedStdio::new(command))
    }
}

/// Claude Desktop.
#[derive(Debug)]
pub(super) struct ClaudeDesktop;

impl Client for ClaudeDesktop {
    fn name(&self) -> &'static str {
        "claude desktop"
    }

    fn place(&self, os: Os, env: &Env) -> Option<(PathBuf, PathBuf)> {
        let dir = match os {
            Os::Windows => claude_desktop_windows(env),
            Os::Mac => env.roaming(os, "Claude"),
            Os::Linux => env.config(os, "Claude"),
        };
        at(dir, "claude_desktop_config.json")
    }

    fn format(&self) -> Format {
        Format::Json { key: "mcpServers" }
    }

    fn entry(&self, command: &str) -> String {
        inline(&Stdio::new(command))
    }

    fn restart_note(&self) -> &'static str {
        " (quit it from the tray icon, not the window)"
    }
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

/// Finds the `claude` command on `PATH`: `claude.exe` or the npm shim
/// `claude.cmd` on Windows, `claude` elsewhere.
///
/// # Returns
///
/// The program, or `None` when `PATH` has none.
pub(super) fn cli() -> Option<PathBuf> {
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
        .stdin(Piped::null())
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
pub(super) fn register_cli(
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

#[cfg(test)]
mod tests {
    use super::claude_command;

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
}
