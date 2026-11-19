//! Records what `borer doctor` reports about the toolchain: the one the repository pins and
//! the compiler that built the binary. The commit and version come from `borer-front`'s
//! build, which the app shares.

use std::path::Path;
use std::process::Command;

/// Sets the pinned toolchain and the compiler's version as environment variables for the
/// compiler, and asks for a rebuild when the pin changes.
fn main() {
    let pins = Path::new("../../rust-toolchain.toml");
    println!("cargo:rerun-if-changed={}", pins.display());
    #[expect(
        clippy::disallowed_methods,
        reason = "the source tree's own file, at build time"
    )]
    let pinned = std::fs::read_to_string(pins)
        .ok()
        .and_then(|t| {
            t.lines().find_map(|l| {
                let (key, value) = l.split_once('=')?;
                (key.trim() == "channel").then(|| value.trim().trim_matches('"').to_owned())
            })
        })
        .unwrap_or_else(|| "nothing".to_owned());
    println!("cargo:rustc-env=BORER_TOOLCHAIN={pinned}");
    let rustc = std::env::var("RUSTC").unwrap_or_else(|_| "rustc".to_owned());
    let version = Command::new(&rustc)
        .arg("-V")
        .output()
        .ok()
        .filter(|out| out.status.success())
        .map(|out| String::from_utf8_lossy(&out.stdout).trim().to_owned())
        .filter(|s| !s.is_empty())
        .unwrap_or_else(|| "an unknown rustc".to_owned());
    println!("cargo:rustc-env=BORER_RUSTC={version}");
}
