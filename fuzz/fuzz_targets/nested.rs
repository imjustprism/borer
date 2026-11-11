//! Loads the program embedded in a file by its `<file>@<offset>` path, one
//! and two levels deep: the first four bytes are the two offsets, the rest
//! is the file, written under the fuzz crate's own `target` directory rather
//! than the shared temp one. Any input may be refused; none may panic, hang
//! or exhaust memory.

#![no_main]

use borer_engine::program::Program;
use libfuzzer_sys::fuzz_target;
use std::path::{Path, PathBuf};

fuzz_target!(|data: &[u8]| {
    let Some((offs, file)) = data.split_first_chunk::<4>() else {
        return;
    };
    let (outer, inner) = (
        u16::from_le_bytes([offs[0], offs[1]]),
        u16::from_le_bytes([offs[2], offs[3]]),
    );
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("target");
    std::fs::create_dir_all(&dir).expect("the scratch directory is made");
    let path = dir.join(format!("nested-{}", std::process::id()));
    std::fs::write(&path, file).expect("the input is written");
    let shown = path.display();
    _ = Program::load_with(&PathBuf::from(format!("{shown}@{outer:#x}")), false);
    _ = Program::load_with(&PathBuf::from(format!("{shown}@{outer}@{inner}")), false);
});
