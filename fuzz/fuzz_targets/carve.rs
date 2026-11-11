//! Scans arbitrary bytes for embedded programs and containers (zip, gzip,
//! xz, 7z, cab, squashfs, cpio, uImage, cramfs, Android boot), asks again
//! at each offset found, and lists them with the entropy runs as the
//! `borer://children` answer. Any input may be refused; none may panic,
//! hang or exhaust memory.

#![no_main]

use borer_engine::carve;
use borer_engine::program::Program;
use libfuzzer_sys::fuzz_target;

/// Children asked for again by offset per input, so one input stays fast.
const ASKED: usize = 16;

fuzz_target!(|data: &[u8]| {
    for child in carve::scan(data).iter().take(ASKED) {
        _ = carve::at(data, child.off);
    }
    if let Ok(program) = Program::from_bytes_with("fuzz".into(), data.to_vec(), false, None) {
        _ = carve::children_tsv(&program);
    }
});
