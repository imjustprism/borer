//! Opening a binary as a front end does: the packs found beside it fit it
//! and name its functions, and a hostile pack is refused in bounded time.

#![expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]

use std::path::PathBuf;
use std::sync::{Arc, mpsc};
use std::time::Duration;

use borer_engine::analysis::Analysis;
use borer_engine::session::{Open, Opened, Pdb, open};
use borer_engine::text::short_path;

/// Where the image is preferred to load.
const IMAGE_BASE: u64 = 0x1_4000_0000;

/// The entry function: `sub rsp, 0x28; xor eax, eax; add rsp, 0x28; ret`.
const CODE: [u8; 11] = [
    0x48, 0x83, 0xec, 0x28, 0x31, 0xc0, 0x48, 0x83, 0xc4, 0x28, 0xc3,
];

/// Builds a one-section x64 PE ([`crate::carve::tiny_pe`]) whose entry, at
/// `IMAGE_BASE + 0x1000`, is [`CODE`].
fn pe() -> Vec<u8> {
    let mut b = crate::carve::tiny_pe();
    b[0x200..0x200 + CODE.len()].copy_from_slice(&CODE);
    b
}

/// A directory of its own for one test, emptied first.
///
/// # Arguments
///
/// * `name` - What the test is, naming the directory.
#[expect(
    clippy::expect_used,
    reason = "a test helper has no recovery from a directory it cannot make"
)]
fn scratch(name: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("borer-session-{name}-{}", std::process::id()));
    std::fs::remove_dir_all(&dir).ok();
    std::fs::create_dir_all(&dir).expect("a temp dir");
    dir
}

/// Opens `binary` with `packs` as the pack files found, no PDB and no cap.
///
/// # Arguments
///
/// * `binary` - The binary.
/// * `packs` - The pack files.
#[expect(
    clippy::expect_used,
    reason = "a test helper has no recovery from a binary that does not open"
)]
fn opened(binary: &std::path::Path, packs: Vec<PathBuf>) -> Opened {
    let how = Open {
        max_file: u64::MAX,
        pdb: Pdb::Off,
        named: Arc::default(),
        packs,
        layout: None,
    };
    open(binary, &how).expect("the binary opens")
}

/// A found pack whose `[match]` lines fit the binary loads with it, says
/// so in the notes as the server prints it, and names the function its
/// signature matches.
#[test]
fn a_found_pack_that_fits_names_a_function() {
    let dir = scratch("names");
    let binary = dir.join("a.exe");
    std::fs::write(&binary, pe()).expect("the binary is written");
    let pack = dir.join("t.borer");
    std::fs::write(
        &pack,
        "pack t 1\n[match]\nsection .text\n[names]\nfn 4883EC2831C04883C428C3 by_pack\n",
    )
    .expect("the pack is written");
    let opened = opened(&binary, vec![pack.clone()]);
    std::fs::remove_dir_all(&dir).ok();
    assert_eq!(
        opened.notes,
        vec![format!(
            "pack t 1 from {} fits: section .text",
            short_path(&pack.to_string_lossy())
        )]
    );
    let a = Analysis::compute_with(&opened.program, Arc::clone(&opened.packs));
    let entry = a.function(IMAGE_BASE + 0x1000).expect("the entry is found");
    assert_eq!(entry.name.as_deref(), Some("by_pack"));
}

/// A pack whose script list names its own file 10,000 times is refused by
/// its count, in well under a second, and the binary opens without it.
#[test]
fn a_pack_that_runs_itself_ten_thousand_times_is_refused_quickly() {
    let dir = scratch("self");
    let binary = dir.join("a.exe");
    std::fs::write(&binary, pe()).expect("the binary is written");
    let pack = dir.join("self.borer");
    let text = format!(
        "pack self 1\n[scripts]\n{}",
        "run self.borer\n".repeat(10_000)
    );
    std::fs::write(&pack, text).expect("the pack is written");
    let (tx, rx) = mpsc::channel();
    std::thread::spawn(move || tx.send(Box::new(opened(&binary, vec![pack]))));
    let opened = rx
        .recv_timeout(Duration::from_secs(1))
        .expect("the open ends within a second");
    std::fs::remove_dir_all(&dir).ok();
    assert!(opened.packs.packs.is_empty(), "{:?}", opened.packs);
    assert_eq!(opened.notes.len(), 1, "{:?}", opened.notes);
    assert!(
        opened.notes[0].contains("10000 scripts, past the 64 a pack may run"),
        "{:?}",
        opened.notes
    );
}
