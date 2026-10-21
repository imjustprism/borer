//! GitHub Copilot CLI: `mcp-config.json` in `$COPILOT_HOME`, else
//! `~/.copilot`, servers under `mcpServers`, each a `local` one offering
//! all its tools.

use std::path::PathBuf;

use serde::Serialize;

use super::client::{Client, Format, at};
use super::env::{Env, Os};
use super::jsonc::inline;

/// How Copilot reaches a server: `local` runs it.
#[derive(Debug, Clone, Copy, Serialize)]
#[serde(rename_all = "lowercase")]
enum Kind {
    /// A program Copilot starts and talks to over stdio.
    Local,
}

/// A Copilot CLI server entry.
#[derive(Debug, Serialize)]
struct Entry<'a> {
    /// How it is reached.
    #[serde(rename = "type")]
    kind: Kind,
    /// The program.
    command: &'a str,
    /// Its arguments: none.
    args: [&'a str; 0],
    /// The tools offered: `*`, all of them.
    tools: [&'a str; 1],
}

/// Copilot cli.
#[derive(Debug)]
pub(super) struct Copilot;

impl Client for Copilot {
    fn name(&self) -> &'static str {
        "copilot cli"
    }

    fn place(&self, _: Os, env: &Env) -> Option<(PathBuf, PathBuf)> {
        at(
            env.var("COPILOT_HOME").or_else(|| env.home(".copilot")),
            "mcp-config.json",
        )
    }

    fn format(&self) -> Format {
        Format::Json { key: "mcpServers" }
    }

    fn entry(&self, command: &str) -> String {
        inline(&Entry {
            kind: Kind::Local,
            command,
            args: [],
            tools: ["*"],
        })
    }
}
