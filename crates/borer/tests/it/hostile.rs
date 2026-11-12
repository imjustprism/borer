//! Hostile files the server reads beside a binary: a pack and the scripts it
//! names are held to their caps however the pack is built.

use std::path::PathBuf;

use borer::packs::load_scripts;
use borer_engine::pack::Pack;

/// A pack written to a directory of its own, and the pack it parses to.
///
/// # Arguments
///
/// * `name` - The pack's name, which also names its directory and file.
/// * `scripts` - The lines of its `[scripts]` section.
///
/// # Returns
///
/// The pack's file and the pack.
///
/// # Panics
///
/// When the pack cannot be written or does not parse.
#[expect(
    clippy::expect_used,
    reason = "a test helper has no recovery from a write that fails"
)]
fn pack(name: &str, scripts: &str) -> (PathBuf, Pack) {
    let dir = std::env::temp_dir().join(format!("borer-hostile-{name}-{}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("a temp dir");
    let file = dir.join(format!("{name}.borer"));
    let text = format!("pack {name} 1\n[scripts]\n{scripts}");
    std::fs::write(&file, &text).expect("the pack is written");
    let (pack, _) = Pack::parse(&text, &file.display().to_string()).expect("the pack parses");
    (file, pack)
}

/// A pack that runs itself a thousand times is refused before it reads a
/// script: each `run` line read the pack's own file again, so 100,000 of
/// them in a 1.2 MB pack read 120 GB.
///
/// # Panics
///
/// When the pack loads.
#[test]
fn a_pack_that_runs_itself_is_refused() {
    let (file, mut pack) = pack("self", &"run self.borer\n".repeat(1000));
    let read = load_scripts(&mut pack, &file);
    std::fs::remove_dir_all(file.parent().expect("a directory")).expect("cleans up");
    let refused = read.expect_err("a thousand scripts loaded");
    assert!(refused.contains("1000 scripts, past the 64"), "{refused}");
}

/// The scripts of one pack hold a bounded total: 64 of 100 KB each are
/// refused at the cap, where every one of them was read.
///
/// # Panics
///
/// When the pack loads.
#[test]
fn the_scripts_of_a_pack_hold_a_bounded_total() {
    let (file, mut pack) = pack("big", &"run big.rhai\n".repeat(64));
    let dir = file.parent().expect("a directory").to_path_buf();
    std::fs::write(dir.join("big.rhai"), vec![b' '; 100_000]).expect("the script is written");
    let read = load_scripts(&mut pack, &file);
    std::fs::remove_dir_all(&dir).expect("cleans up");
    let refused = read.expect_err("6.4 MB of scripts loaded");
    assert!(refused.contains("bytes, past the"), "{refused}");
}

/// A script that is a device is refused by its metadata, where reading
/// `/dev/zero` grew without end.
///
/// # Panics
///
/// When the device is read.
#[cfg(unix)]
#[test]
fn a_pack_script_that_is_a_device_is_refused() {
    let (file, mut pack) = pack("zero", &format!("run {}dev/zero\n", "../".repeat(32)));
    let read = load_scripts(&mut pack, &file);
    std::fs::remove_dir_all(file.parent().expect("a directory")).expect("cleans up");
    let refused = read.expect_err("/dev/zero loaded");
    assert!(refused.contains("not a regular file"), "{refused}");
}
