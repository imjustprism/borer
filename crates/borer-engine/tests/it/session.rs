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
use borer_engine::layout::Layout;
use borer_engine::program::Arch;
use borer_engine::session::{Form, Open, Opened, Pdb, open, read_dirs};
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

/// Opens `binary` with `dirs` as the pack directories, no PDB and no cap.
///
/// # Arguments
///
/// * `binary` - The binary.
/// * `dirs` - The pack directories.
#[expect(
    clippy::expect_used,
    reason = "a test helper has no recovery from a binary that does not open"
)]
fn opened(binary: &std::path::Path, dirs: Vec<PathBuf>) -> Opened {
    let how = Open {
        max_file: u64::MAX,
        form: Form::Headers(Pdb::Off),
        named: Arc::default(),
        dirs,
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
    let opened = opened(&binary, vec![dir.clone()]);
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
    let packs = dir.clone();
    std::thread::spawn(move || tx.send(Box::new(opened(&binary, vec![packs]))));
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

/// The notes of the pack directories come a directory at a time: a file
/// of the first that is no pack, then the second directory, which names
/// nothing usable.
#[test]
fn pack_directory_notes_come_in_the_order_they_are_read() {
    let dir = scratch("order");
    let bad = dir.join("bad.borer");
    std::fs::write(&bad, [0xffu8, 0xfe]).expect("the file is written");
    let mut notes = Vec::new();
    let packs = read_dirs(&[dir.clone(), PathBuf::new()], &mut notes);
    std::fs::remove_dir_all(&dir).ok();
    assert!(packs.is_empty(), "{packs:?}");
    assert_eq!(
        notes,
        vec![
            format!("skipped {}: not text", short_path(&bad.to_string_lossy())),
            "skipped a pack directory: the path is empty".to_owned(),
        ]
    );
}

/// Of two packs of one name in a directory, the one first by file name
/// fits, whatever order the directory lists them in.
#[test]
fn of_two_packs_of_one_name_the_first_by_file_name_fits() {
    let dir = scratch("twins");
    let binary = dir.join("a.exe");
    std::fs::write(&binary, pe()).expect("the binary is written");
    for file in ["b.borer", "a.borer"] {
        std::fs::write(dir.join(file), "pack foo 1\n[match]\nsection .text\n")
            .expect("the pack is written");
    }
    let opened = opened(&binary, vec![dir.clone()]);
    std::fs::remove_dir_all(&dir).ok();
    assert_eq!(opened.packs.packs.len(), 1, "{:?}", opened.packs);
    assert!(
        opened.packs.packs[0].source.ends_with("a.borer"),
        "{}",
        opened.packs.packs[0].source
    );
}

/// A raw layout maps the file's bytes where it says, its headers unread,
/// and its packs still fit.
#[test]
fn a_raw_layout_maps_the_bytes_where_it_says() {
    let dir = scratch("raw");
    let binary = dir.join("code.bin");
    std::fs::write(&binary, CODE).expect("the code is written");
    let layout = Layout::parse(Some(Arch::X86_64), Some("0x4000"), None, None)
        .expect("the layout reads")
        .expect("a layout is stated");
    let how = Open {
        max_file: u64::MAX,
        form: Form::Raw(layout),
        named: Arc::default(),
        dirs: Vec::new(),
    };
    let opened = open(&binary, &how).expect("the code opens");
    std::fs::remove_dir_all(&dir).ok();
    assert_eq!(opened.program.entry, Some(0x4000));
    assert!(opened.program.pdb_record.is_none());
    assert!(opened.notes.is_empty(), "{:?}", opened.notes);
}
