//! CLI path, layout and size-cap tests.

use std::process::Command;

use super::{run, run_all};

/// `--arch` with `--regions` maps a two-part dump where the command line
/// says.
///
/// The queries then read it like any image; without `--arch` the same
/// file has no code, and a region past the end of the file or a layout
/// flag on a command that reads no binary is refused.
#[test]
fn cli_maps_a_dump_at_stated_regions() {
    let mut bytes = vec![0xcc_u8; 0x30];
    // ASM: mov eax, dword ptr [0x20000]; ret
    bytes[..8].copy_from_slice(&[0x8b, 0x04, 0x25, 0x00, 0x00, 0x02, 0x00, 0xc3]);
    bytes[0x20..0x24].copy_from_slice(&42u32.to_le_bytes());
    let path = std::env::temp_dir().join(format!("borer_dump_fixture_{}.bin", std::process::id()));
    std::fs::write(&path, &bytes).expect("the fixture is writable");
    let path = path.to_string_lossy().to_string();
    let regions = "0x10000@0:0x20:rx,0x20000@0x20:0x10:rw";

    let (ok, info) = run_all(&["info", &path, "--arch", "x64", "--regions", regions]);
    let (emulated, ran) = run_all(&[
        "emulate",
        &path,
        "0x10000",
        "--arch=x64",
        "--regions",
        regions,
    ]);
    let (plain, unmapped) = run_all(&["functions", &path]);
    let (past, refusal) = run_all(&["info", &path, "--arch", "x64", "--regions", "0@0:0x31"]);
    let (stray, stray_refusal) = run_all(&["pack-keys", "--arch", "x64"]);
    drop(std::fs::remove_file(&path));

    assert!(ok, "{info}");
    assert!(info.contains("region1        0x20000"), "{info}");
    assert!(info.contains("kind stated layout"), "{info}");
    assert!(emulated && ran.contains("rax=0x2a "), "{ran}");
    assert!(!plain && unmapped.contains("raw file"), "{unmapped}");
    assert!(
        !past && refusal.contains("runs past the end of the file at 0x30"),
        "{refusal}"
    );
    assert!(
        !stray && stray_refusal.contains("pack-keys maps none"),
        "{stray_refusal}"
    );
}

/// `BORER_MAX_FILE` applies inside the program reader after stripping `@<off>`
/// and across comparison loads (`diff`), so neither slice syntax nor `diff`
/// reads an oversized file unchecked.
#[test]
fn cli_max_file_caps_carved_slices_and_diff_loads() {
    let pid = std::process::id();
    let pe = std::env::temp_dir().join(format!("borer_max_{pid}.exe"));
    let raw = std::env::temp_dir().join(format!("borer_max_{pid}.bin"));
    std::fs::write(&pe, crate::contract::tiny_pe()).expect("the fixture is writable");
    std::fs::write(&raw, [0xc3u8, 0x90, 0x90, 0x90]).expect("the raw fixture is writable");
    let (pe_s, raw_s) = (pe.to_string_lossy(), raw.to_string_lossy());
    let carved = format!("{pe_s}@0");
    for args in [
        vec!["--no-pdb", "triage", carved.as_str()],
        vec!["--arch", "x86_64", "diff", raw_s.as_ref(), pe_s.as_ref()],
    ] {
        let out = Command::new(env!("CARGO_BIN_EXE_borer"))
            .env("BORER_MAX_FILE", "16")
            .args(&args)
            .output()
            .expect("spawn borer");
        let said = format!(
            "{}{}",
            String::from_utf8_lossy(&out.stdout),
            String::from_utf8_lossy(&out.stderr)
        );
        assert!(!out.status.success(), "{args:?}: {said}");
        assert!(said.contains("past the 16-byte limit"), "{args:?}: {said}");
    }
    std::fs::remove_file(&pe).ok();
    std::fs::remove_file(&raw).ok();
}

/// Keeps `run` referenced by the submodule before more path tests land.
#[test]
fn cli_help_lists_pack() {
    let (ok, out) = run(&["help", "pack"]);
    assert!(ok && out.contains("pack"), "{out}");
}
