//! Zed: `settings.json` in its configuration directory, servers under
//! `context_servers`.

use std::path::PathBuf;

use super::client::{Client, Format, Stdio, at};
use super::env::{Env, Os};
use super::jsonc::inline;

/// Zed.
#[derive(Debug)]
pub(super) struct Zed;

impl Client for Zed {
    fn name(&self) -> &'static str {
        "zed"
    }

    fn place(&self, os: Os, env: &Env) -> Option<(PathBuf, PathBuf)> {
        let dir = env.config(os, if os == Os::Windows { "Zed" } else { "zed" });
        at(dir, "settings.json")
    }

    fn format(&self) -> Format {
        Format::Json {
            key: "context_servers",
        }
    }

    fn entry(&self, command: &str) -> String {
        inline(&Stdio::new(command))
    }
}
