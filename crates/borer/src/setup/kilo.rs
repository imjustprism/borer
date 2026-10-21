//! Kilo Code, built on `OpenCode`.
//!
//! Its file is `kilo.json` (or a `kilo.jsonc` already
//! there) in `$KILO_CONFIG_DIR`, else `~/.config/kilo` on every system,
//! servers under `mcp`, a local one with its command as an array.

use std::path::PathBuf;

use serde::Serialize;

use super::client::{Client, Format, json_or_jsonc};
use super::env::{Env, Os};
use super::jsonc::inline;

/// Milliseconds Kilo waits for one request, written into the entry: the
/// default minute is less than the first analysis of a large binary takes.
const TIMEOUT_MS: u32 = 600_000;

/// How Kilo reaches a server: `local` runs it.
#[derive(Debug, Clone, Copy, Serialize)]
#[serde(rename_all = "lowercase")]
enum Kind {
    /// A program Kilo starts and talks to over stdio.
    Local,
}

/// A Kilo Code server entry.
#[derive(Debug, Serialize)]
struct Entry<'a> {
    /// How it is reached.
    #[serde(rename = "type")]
    kind: Kind,
    /// The program and its arguments, as one array.
    command: [&'a str; 1],
    /// Whether it starts with Kilo.
    enabled: bool,
    /// Milliseconds one request may take.
    timeout: u32,
}

/// Kilo code.
#[derive(Debug)]
pub(super) struct Kilo;

impl Client for Kilo {
    fn name(&self) -> &'static str {
        "kilo code"
    }

    fn place(&self, _: Os, env: &Env) -> Option<(PathBuf, PathBuf)> {
        json_or_jsonc(
            env.var("KILO_CONFIG_DIR").or_else(|| env.xdg("kilo")),
            "kilo",
        )
    }

    fn format(&self) -> Format {
        Format::Json { key: "mcp" }
    }

    fn entry(&self, command: &str) -> String {
        inline(&Entry {
            kind: Kind::Local,
            command: [command],
            enabled: true,
            timeout: TIMEOUT_MS,
        })
    }
}
