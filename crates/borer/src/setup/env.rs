//! The operating system and the directories client configurations hang
//! from.

use std::path::PathBuf;

/// The three operating systems whose configuration paths differ.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum Os {
    /// Windows: `%APPDATA%` and `%LOCALAPPDATA%`.
    Windows,
    /// macOS: `~/Library/Application Support` beside `~/.config`.
    Mac,
    /// Linux and the other Unix systems: `$XDG_CONFIG_HOME`.
    Linux,
}

impl Os {
    /// The operating system this binary runs on.
    pub(super) const HOST: Os = if cfg!(windows) {
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
pub(super) struct Env {
    /// The user's home directory.
    pub(super) home: Option<PathBuf>,
    /// Windows' roaming application data, `%APPDATA%`.
    pub(super) appdata: Option<PathBuf>,
    /// Windows' local application data, `%LOCALAPPDATA%`.
    pub(super) local: Option<PathBuf>,
    /// The configuration directory off Windows: `$XDG_CONFIG_HOME`, else
    /// `~/.config`.
    pub(super) config: Option<PathBuf>,
    /// Codex's home, `$CODEX_HOME`, else `~/.codex`.
    pub(super) codex: Option<PathBuf>,
    /// pi's agent directory, `$PI_CODING_AGENT_DIR`, else `~/.pi/agent`.
    pub(super) pi: Option<PathBuf>,
    /// `OpenCode`'s directory, `$OPENCODE_CONFIG_DIR`, else `opencode` in the
    /// configuration directory, on Windows too.
    pub(super) opencode: Option<PathBuf>,
}

impl Env {
    /// Reads the directories from the environment.
    ///
    /// # Returns
    ///
    /// The directories; a variable that is unset or empty is `None`.
    pub(super) fn read() -> Env {
        let var = |name: &str| {
            std::env::var_os(name)
                .filter(|v| !v.is_empty())
                .map(PathBuf::from)
        };
        let home = std::env::home_dir();
        let config = var("XDG_CONFIG_HOME").or_else(|| home.as_ref().map(|h| h.join(".config")));
        Env {
            opencode: var("OPENCODE_CONFIG_DIR")
                .or_else(|| config.as_ref().map(|c| c.join("opencode"))),
            config,
            codex: var("CODEX_HOME").or_else(|| home.as_ref().map(|h| h.join(".codex"))),
            pi: var("PI_CODING_AGENT_DIR")
                .or_else(|| home.as_ref().map(|h| h.join(".pi").join("agent"))),
            appdata: var("APPDATA"),
            local: var("LOCALAPPDATA"),
            home,
        }
    }
}

impl Env {
    /// A directory under the user's home.
    ///
    /// # Arguments
    ///
    /// * `rest` - The path below the home directory.
    pub(super) fn home(&self, rest: &str) -> Option<PathBuf> {
        self.home.as_ref().map(|h| h.join(rest))
    }

    /// A directory under the per-user configuration directory: `%APPDATA%`
    /// on Windows, `$XDG_CONFIG_HOME` or `~/.config` elsewhere.
    ///
    /// # Arguments
    ///
    /// * `os` - Whose paths to use.
    /// * `rest` - The path below that directory.
    pub(super) fn config(&self, os: Os, rest: &str) -> Option<PathBuf> {
        match os {
            Os::Windows => self.appdata.as_ref().map(|a| a.join(rest)),
            Os::Mac | Os::Linux => self.config.as_ref().map(|c| c.join(rest)),
        }
    }

    /// A directory where desktop applications keep their settings:
    /// `~/Library/Application Support` on macOS, else as [`Env::config`].
    ///
    /// # Arguments
    ///
    /// * `os` - Whose paths to use.
    /// * `rest` - The path below that directory.
    pub(super) fn roaming(&self, os: Os, rest: &str) -> Option<PathBuf> {
        match os {
            Os::Mac => self
                .home("Library/Application Support")
                .map(|d| d.join(rest)),
            Os::Windows | Os::Linux => self.config(os, rest),
        }
    }
}
