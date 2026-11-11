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
use crate::resources::{dotnet_pe, read};
use crate::without_evidence;

/// The file offset of [`tiny_pe`]'s code, mapped at [`ENTRY`].
const CODE_AT: usize = 0x200;

/// Where [`tiny_pe`]'s code is mapped and entered.
const ENTRY: &str = "0x140001000";

/// Writes [`tiny_pe`] with `code` over its lone `ret` to a file of this
/// process's own in the temp directory.
///
/// # Arguments
///
/// * `name` - The file's name after the process id.
/// * `code` - The bytes at the image's entry, [`ENTRY`].
///
/// # Returns
///
/// The file's path.
fn fixture(name: &str, code: &[u8]) -> PathBuf {
    let mut image = tiny_pe();
    image[CODE_AT..CODE_AT + code.len()].copy_from_slice(code);
    written(name, &image)
}

/// Writes an image to a file of this process's own in the temp directory.
///
/// # Arguments
///
/// * `name` - The file's name after the process id.
/// * `image` - The file's bytes.
///
/// # Returns
///
/// The file's path.
fn written(name: &str, image: &[u8]) -> PathBuf {
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

/// `decompile` prints at the CLI the text the `decompile` tool answers,
/// line for line.
///
/// The index `grep` reads stores the tool's text, so a line number it
/// gives is a line of that text. The CLI left out the `// next:` lines,
/// so every line under them had another number there.
#[test]
fn a_decompilation_reads_the_same_at_the_cli_and_over_mcp() {
    let file = fixture(
        "check.exe",
        &[
            0x81, 0xf9, 0xcd, 0xab, 0x37, 0x13, // ASM: cmp ecx, 0x1337abcd
            0x0f, 0x94, 0xc0, // ASM: sete al
            0x0f, 0xb6, 0xc0, // ASM: movzx eax, al
            0xc3, // ASM: ret
        ],
    );
    let at_cli = cli(&["decompile", &shown(&file), ENTRY]);
    let mut client = Client::start(&shown(&file));
    let over_mcp = client.text("decompile", &format!(r#"{{"address":"{ENTRY}"}}"#));
    client.finish();
    std::fs::remove_file(&file).ok();
    assert_eq!(at_cli, without_evidence(&over_mcp));
    assert!(
        at_cli.contains(&format!("\n// next: borer://solve/{ENTRY},a1 ")),
        "{at_cli}"
    );
}

/// A script run at the CLI under `--project` reads the project's names,
/// as one run over MCP after `load_project` does.
///
/// `--project` applies a project to every query; `script` ran over an
/// empty overlay, so `name()` answered `sub_...` for a function the
/// project names.
#[test]
fn a_script_reads_a_project_s_names_at_the_cli_and_over_mcp() {
    let file = fixture("named.exe", &[0xc3]);
    let image = std::fs::read(&file).expect("the fixture reads back");
    let project = file.with_extension("json");
    let saved = serde_json::json!({
        "program": shown(&file),
        "sha256": borer::project::identity(&image),
        "names": {ENTRY: "checks_serial"},
        "comments": {}
    });
    std::fs::write(&project, saved.to_string()).expect("the project is writable");
    let script = file.with_extension("rhai");
    let code = format!("print(name({ENTRY}));");
    std::fs::write(&script, &code).expect("the script is writable");
    let (binary, project_path) = (shown(&file), shown(&project));
    let at_cli = cli(&[
        "--project",
        &project_path,
        "script",
        &binary,
        &shown(&script),
    ]);
    let mut client = Client::start(&binary);
    client.text(
        "load_project",
        &serde_json::json!({ "path": project_path }).to_string(),
    );
    let over_mcp = client.text("script", &serde_json::json!({ "code": code }).to_string());
    client.finish();
    for written in [&file, &project, &script] {
        std::fs::remove_file(written).ok();
    }
    assert_eq!(at_cli, without_evidence(&over_mcp));
    assert!(at_cli.starts_with("checks_serial\n"), "{at_cli}");
}

/// `fstrings` lists the user strings a .NET method loads at the CLI, as
/// `function_strings` does over MCP.
///
/// The CLI's `function`, `disasmfn` and `xrefs` read a method's CIL, and
/// the refusal of an IL body names `function_strings` among what reads
/// it; `fstrings` alone refused the method.
#[test]
fn a_dotnet_method_s_strings_read_the_same_at_the_cli_and_over_mcp() {
    let mut image = dotnet_pe();
    image[0x250..0x258].copy_from_slice(&[
        0x1e, // ASM: a tiny IL header, 7 bytes of code
        0x72, 0x01, 0x00, 0x00, 0x70, // ASM: ldstr 0x70000001
        0x26, // ASM: pop
        0x2a, // ASM: ret
    ]);
    let file = written("managed.exe", &image);
    let binary = shown(&file);
    let at_cli = cli(&["fstrings", &binary, "Ns.Program::Main"]);
    let mut client = Client::start(&binary);
    let over_mcp = client.text("function_strings", r#"{"address":"Ns.Program::Main"}"#);
    client.finish();
    std::fs::remove_file(&file).ok();
    assert_eq!(at_cli, without_evidence(&over_mcp));
    assert!(
        at_cli.contains("\nIL_0000\t0x70000001\t") && at_cli.contains("c2.example.test"),
        "{at_cli}"
    );
}
