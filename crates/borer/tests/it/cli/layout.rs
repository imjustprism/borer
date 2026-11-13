//! CLI tests for pack inspection, stated dump layouts, and RISC-V verification.

use super::{run, run_all};

/// A pack reads back its name, keys and warnings; `pack-keys` lists what a
/// pack can set; `--pack` loads one for any command and a file that is not
/// a pack is refused.
#[test]
#[cfg_attr(
    not(windows),
    ignore = "reads borer's own build, pinned as the Windows x64 PE"
)]
fn cli_packs_read_list_and_load() {
    let exe = env!("CARGO_BIN_EXE_borer");
    let dir = std::env::temp_dir();
    let good = dir.join(format!("borer_pack_{}.borer", std::process::id()));
    let bad = dir.join(format!("borer_notpack_{}.borer", std::process::id()));
    std::fs::write(
        &good,
        "pack testpack 3\nabout a test\n[naming]\nsingleton Only\n[roles]\nclass A::B thing\nunknown x\n",
    )
    .expect("writes the pack");
    std::fs::write(&bad, "[naming]\nsingleton x\n").expect("writes the file");
    let good_path = good.to_string_lossy().to_string();
    let bad_path = bad.to_string_lossy().to_string();
    let (ok, out) = run(&["pack", &good_path]);
    assert!(ok, "pack failed:\n{out}");
    assert!(
        out.starts_with("# pack testpack 3: 3 lines in 3 keys, 1 warnings"),
        "{out}"
    );
    assert!(out.contains("naming\tsingleton\t1"), "{out}");
    let (ok, out) = run(&["pack-keys"]);
    assert!(ok, "pack-keys failed:\n{out}");
    assert!(
        out.contains("naming\tsingleton\tsingle\tinstance\t"),
        "{out}"
    );
    let (ok, out) = run(&["info", exe, "--pack", &good_path]);
    assert!(ok, "info with a pack failed:\n{out}");
    let (ok, _) = run(&["info", exe, "--pack", &bad_path]);
    std::fs::remove_file(&good).ok();
    std::fs::remove_file(&bad).ok();
    assert!(!ok, "a file that is not a pack loads");
}

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

/// `verify` checks RISC-V code against the RISC-V machine, and refuses the
/// modes it does not run for RISC-V instead of checking nothing.
///
/// The fixture is a 64-bit `EM_RISCV` executable of one `PT_LOAD` segment
/// holding `add a0, a0, a1; ret` at its entry.
#[test]
fn cli_verifies_risc_v_code() {
    const ENTRY: u64 = 0x1_0078;
    let mut bytes = vec![0u8; 0x78];
    bytes[..8].copy_from_slice(&[0x7f, b'E', b'L', b'F', 2, 1, 1, 0]);
    let mut put = |at: usize, v: u64, n: usize| {
        bytes[at..at + n].copy_from_slice(&v.to_le_bytes()[..n]);
    };
    put(0x10, 2, 2);
    put(0x12, 243, 2);
    put(0x14, 1, 4);
    put(0x18, ENTRY, 8);
    put(0x20, 0x40, 8);
    put(0x34, 64, 2);
    put(0x36, 56, 2);
    put(0x38, 1, 2);
    put(0x3a, 64, 2);
    put(0x40, 1, 4);
    put(0x44, 5, 4);
    put(0x50, 0x1_0000, 8);
    put(0x58, 0x1_0000, 8);
    put(0x60, 0x80, 8);
    put(0x68, 0x80, 8);
    put(0x70, 0x1000, 8);
    bytes.extend_from_slice(&0x00b5_0533u32.to_le_bytes()); // ASM: add a0, a0, a1
    bytes.extend_from_slice(&0x0000_8067u32.to_le_bytes()); // ASM: ret
    let path = std::env::temp_dir().join(format!("borer_riscv_verify_{}.elf", std::process::id()));
    std::fs::write(&path, &bytes).expect("the fixture is writable");
    let path = path.to_string_lossy().to_string();

    let (ok, out) = run_all(&["verify", &path, &format!("{ENTRY:#x}")]);
    assert!(
        ok && out.starts_with("# verified 1 functions, 1 blocks: 1 checked"),
        "{out}"
    );
    let (ok, out) = run_all(&["verify", &path, &format!("{ENTRY:#x}"), "1", "1", "text"]);
    assert!(!ok && out.contains("block by block only"), "{out}");

    drop(std::fs::remove_file(&path));
}
