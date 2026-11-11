//! The CLI and the MCP server asked the same question of the same file,
//! on the real binary (`CARGO_BIN_EXE_borer`): both front ends answer with
//! the same text.

#![expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]
#![expect(
    clippy::expect_used,
    reason = "a fixture that cannot be written or run has no useful recovery in a test"
)]

use std::path::{Path, PathBuf};
use std::process::Command;

use crate::contract::tiny_pe;
use crate::reload::Client;
use crate::resources::read;
use crate::without_evidence;

/// The file offset of [`tiny_pe`]'s code, mapped at `0x140001000`.
const CODE_AT: usize = 0x200;

/// Writes [`tiny_pe`] with `code` over its lone `ret` to a file of this
/// process's own in the temp directory.
///
/// # Arguments
///
/// * `name` - The file's name after the process id.
/// * `code` - The bytes at the image's entry, `0x140001000`.
///
/// # Returns
///
/// The file's path.
fn fixture(name: &str, code: &[u8]) -> PathBuf {
    let mut image = tiny_pe();
    image[CODE_AT..CODE_AT + code.len()].copy_from_slice(code);
    let path = std::env::temp_dir().join(format!("borer_parity_{}_{name}", std::process::id()));
    std::fs::write(&path, image).expect("the fixture is writable");
    path
}

/// A path as a command line and a URI carry it.
///
/// # Arguments
///
/// * `path` - The path.
fn shown(path: &Path) -> String {
    path.to_string_lossy().replace('\\', "/")
}

/// Runs a CLI command that answers and returns what it printed.
///
/// # Arguments
///
/// * `args` - Command-line arguments after the program name.
fn cli(args: &[&str]) -> String {
    let out = Command::new(env!("CARGO_BIN_EXE_borer"))
        .arg("--no-pdb")
        .args(args)
        .output()
        .expect("spawn borer");
    assert!(
        out.status.success(),
        "{args:?}: {}",
        String::from_utf8_lossy(&out.stderr)
    );
    String::from_utf8_lossy(&out.stdout).into_owned()
}

/// A diff against a fingerprint sidecar reads the sidecar as the earlier
/// build at the CLI as it does over MCP.
///
/// The sidecar is one build's fingerprints saved beside it; the binary
/// diffed against it is the later build, so a function only the binary
/// has was added. The CLI passed the two the other way round and said the
/// later build had removed it.
#[test]
fn a_sidecar_diff_reads_the_same_at_the_cli_and_over_mcp() {
    let old = fixture("old.exe", &[0xc3]);
    let mut grown = [0xcc_u8; 0x16];
    grown[..6].copy_from_slice(&[
        0xe8, 0x0b, 0x00, 0x00, 0x00, // ASM: call 0x140001010
        0xc3, // ASM: ret
    ]);
    grown[0x10..].copy_from_slice(&[
        0xb8, 0x01, 0x00, 0x00, 0x00, // ASM: mov eax, 1
        0xc3, // ASM: ret
    ]);
    let new = fixture("new.exe", &grown);
    let sidecar = old.with_extension("bfp");
    cli(&["fingerprint", &shown(&old), &shown(&sidecar)]);
    let at_cli = cli(&["diff", &shown(&new), &shown(&sidecar)]);
    let mut client = Client::start(&shown(&new));
    let over_mcp = read(&mut client, &format!("borer://diff/{}", shown(&sidecar)));
    client.finish();
    let names = [&sidecar, &new].map(|p| {
        p.file_name()
            .expect("a file name")
            .to_string_lossy()
            .into_owned()
    });
    for file in [&old, &new, &sidecar] {
        std::fs::remove_file(file).ok();
    }
    let over_mcp = over_mcp.expect("the resource answers");
    assert_eq!(at_cli, without_evidence(&over_mcp));
    assert!(
        at_cli.starts_with(&format!(
            "# diff: {} (baseline) vs {}\n# 1 functions -> 2 functions\n",
            names[0], names[1]
        )),
        "{at_cli}"
    );
    assert!(
        at_cli.contains(&format!("# added (only in {}):\n", names[1])),
        "{at_cli}"
    );
}
