//! Records what `borer doctor` and `borer --version` report about the
//! build: the commit the binary is built from and where it stands from the
//! last release tag, the toolchain the repository pins, and the compiler
//! that built it.

use std::path::Path;
use std::process::Command;

/// Runs a program and returns its trimmed output when it succeeds.
///
/// # Arguments
///
/// * `program` - The program.
/// * `args` - Its arguments.
fn output(program: &str, args: &[&str]) -> Option<String> {
    let out = Command::new(program).args(args).output().ok()?;
    out.status
        .success()
        .then(|| String::from_utf8_lossy(&out.stdout).trim().to_owned())
        .filter(|s| !s.is_empty())
}

/// The commit a crates.io package was published from, read from the
/// `.cargo_vcs_info.json` that `cargo package` writes into it.
///
/// The release workflow publishes from the release tag, so a build of the
/// package is a build of that release, though no git repository is around
/// to say so.
///
/// # Returns
///
/// The commit's first twelve hex digits, or `None` outside a package.
fn packaged_commit() -> Option<String> {
    let info = std::fs::read_to_string(".cargo_vcs_info.json").ok()?;
    let after = info.split_once("\"sha1\"")?.1;
    let sha: String = after
        .chars()
        .skip_while(|c| !c.is_ascii_hexdigit())
        .take_while(char::is_ascii_hexdigit)
        .collect();
    (sha.len() >= 12).then(|| sha[..12].to_owned())
}

/// Sets the build's facts as environment variables for the compiler, and
/// asks for a rebuild when the commit or the pinned toolchain changes.
fn main() {
    let git = |args: &[&str]| output("git", args);
    let (commit, describe) = match packaged_commit() {
        Some(sha) => {
            let version = std::env::var("CARGO_PKG_VERSION").unwrap_or_default();
            (sha.clone(), format!("v{version}-0-g{sha}"))
        }
        None => (
            git(&["rev-parse", "--short=12", "HEAD"]).unwrap_or_else(|| "unknown".to_owned()),
            git(&["describe", "--tags", "--long", "--match", "v[0-9]*"]).unwrap_or_default(),
        ),
    };
    println!("cargo:rustc-env=BORER_COMMIT={commit}");
    println!("cargo:rustc-env=BORER_DESCRIBE={describe}");
    for path in ["HEAD", "packed-refs"] {
        if let Some(p) = git(&["rev-parse", "--git-path", path]) {
            println!("cargo:rerun-if-changed={p}");
        }
    }
    if let Some(p) =
        git(&["symbolic-ref", "-q", "HEAD"]).and_then(|r| git(&["rev-parse", "--git-path", &r]))
    {
        println!("cargo:rerun-if-changed={p}");
    }
    let pins = Path::new("../../rust-toolchain.toml");
    println!("cargo:rerun-if-changed={}", pins.display());
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
    let version = output(&rustc, &["-V"]).unwrap_or_else(|| "an unknown rustc".to_owned());
    println!("cargo:rustc-env=BORER_RUSTC={version}");
}
