//! VS Code and VS Code Insiders: `mcp.json` in the user folder, servers
//! under `servers` with their transport stated.

use std::path::PathBuf;

use super::client::{Client, Format, TypedStdio, at};
use super::env::{Env, Os};
use super::jsonc::inline;

/// VS Code, or its Insiders build.
#[derive(Debug)]
pub(super) struct VsCode {
    /// Whether this is the Insiders build.
    pub(super) insiders: bool,
}

impl Client for VsCode {
    fn name(&self) -> &'static str {
        if self.insiders {
            "vs code insiders"
        } else {
            "vs code"
        }
    }

    fn place(&self, os: Os, env: &Env) -> Option<(PathBuf, PathBuf)> {
        let user = if self.insiders {
            "Code - Insiders/User"
        } else {
            "Code/User"
        };
        at(env.roaming(os, user), "mcp.json")
    }

    fn format(&self) -> Format {
        Format::Json { key: "servers" }
    }

    fn entry(&self, command: &str) -> String {
        inline(&TypedStdio::new(command))
    }

    fn restart_note(&self) -> &'static str {
        " (or run MCP: List Servers and start borer)"
    }
}
