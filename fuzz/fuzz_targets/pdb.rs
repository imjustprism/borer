//! Applies arbitrary bytes as the companion PDB of a small PE, then
//! decompiles the image's functions, whose headers read the PDB's line
//! programs: the first eight bytes are the image's base, the rest is the
//! file the image's debug record names, written beside it under the fuzz
//! crate's own `target` directory rather than the shared temp one. The
//! record states a zero GUID and age 1, so a PDB that keeps
//! those is applied and any other is refused as another build's. Any input
//! may be refused; none may panic, hang or exhaust memory.

#![no_main]

use borer_engine::analysis::decompile::decompile;
use borer_engine::analysis::{Analysis, Overlay};
use borer_engine::program::Program;
use libfuzzer_sys::fuzz_target;
use std::path::Path;

/// Functions decompiled per input, so one input stays fast.
const DECOMPILED: usize = 4;
/// File offset of the PE signature.
const SIG: usize = 0x40;
/// File offset of the optional header.
const OPT: usize = SIG + 24;
/// File offset of the section table.
const ROWS: usize = OPT + 0xf0;
/// File offset of `.data`, mapped at RVA `0x2000`.
const DATA: usize = 0x400;

/// Writes `bytes` into `b` at `at`.
fn put(b: &mut [u8], at: usize, bytes: &[u8]) {
    b[at..at + bytes.len()].copy_from_slice(bytes);
}

/// Writes one section table row: its name, RVA, file offset and flags, with
/// `0x200` bytes mapped.
fn row(b: &mut [u8], at: usize, name: &[u8], rva: u32, off: u32, flags: u32) {
    put(b, at, name);
    for (field, v) in [(8, 0x200), (12, rva), (16, 0x200), (20, off), (36, flags)] {
        put(b, at + field, &v.to_le_bytes());
    }
}

/// Builds a PE32+ x86-64 image at `base`: `.text` holding two functions,
/// and `.data` holding the debug directory and the `CodeView` record that
/// names `fuzz.pdb`.
fn image(base: u64) -> Vec<u8> {
    let mut b = vec![0u8; 0x600];
    put(&mut b, 0, b"MZ");
    put(&mut b, 0x3c, &0x40u32.to_le_bytes());
    put(&mut b, SIG, b"PE\0\0");
    put(&mut b, SIG + 4, &0x8664u16.to_le_bytes());
    put(&mut b, SIG + 6, &2u16.to_le_bytes());
    put(&mut b, SIG + 20, &0xf0u16.to_le_bytes());
    put(&mut b, SIG + 22, &0x22u16.to_le_bytes());
    put(&mut b, OPT, &0x20bu16.to_le_bytes());
    put(&mut b, OPT + 16, &0x1010u32.to_le_bytes());
    put(&mut b, OPT + 24, &base.to_le_bytes());
    put(&mut b, OPT + 32, &0x1000u32.to_le_bytes());
    put(&mut b, OPT + 36, &0x200u32.to_le_bytes());
    put(&mut b, OPT + 48, &6u16.to_le_bytes());
    put(&mut b, OPT + 56, &0x3000u32.to_le_bytes());
    put(&mut b, OPT + 60, &0x200u32.to_le_bytes());
    put(&mut b, OPT + 68, &3u16.to_le_bytes());
    put(&mut b, OPT + 108, &16u32.to_le_bytes());
    put(&mut b, OPT + 112 + 6 * 8, &0x2020u32.to_le_bytes());
    put(&mut b, OPT + 112 + 6 * 8 + 4, &28u32.to_le_bytes());
    row(&mut b, ROWS, b".text", 0x1000, 0x200, 0x6000_0020);
    row(&mut b, ROWS + 40, b".data", 0x2000, 0x400, 0xc000_0040);
    // ASM: mov eax, 7; ret
    put(&mut b, 0x210, &[0xb8, 0x07, 0x00, 0x00, 0x00, 0xc3]);
    // ASM: call 0x1010; ret
    put(&mut b, 0x240, &[0xe8, 0xcb, 0xff, 0xff, 0xff, 0xc3]);
    put(&mut b, DATA + 0x20 + 12, &2u32.to_le_bytes());
    put(&mut b, DATA + 0x20 + 16, &33u32.to_le_bytes());
    put(&mut b, DATA + 0x20 + 20, &0x2040u32.to_le_bytes());
    put(&mut b, DATA + 0x20 + 24, &0x440u32.to_le_bytes());
    put(&mut b, DATA + 0x40, b"RSDS");
    put(&mut b, DATA + 0x40 + 20, &1u32.to_le_bytes());
    put(&mut b, DATA + 0x40 + 24, b"fuzz.pdb");
    b
}

fuzz_target!(|data: &[u8]| {
    let Some((base, pdb)) = data.split_first_chunk::<8>() else {
        return;
    };
    let dir = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("target")
        .join(format!("pdb-{}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("the scratch directory is made");
    std::fs::write(dir.join("fuzz.pdb"), pdb).expect("the input is written");
    let bytes = image(u64::from_le_bytes(*base));
    let Ok(program) = Program::from_bytes_with(dir.join("fuzz.exe"), bytes, true, None) else {
        return;
    };
    let analysis = Analysis::compute(&program);
    let overlay = Overlay::default();
    for f in analysis.functions.iter().take(DECOMPILED) {
        _ = decompile(&program, &analysis, &overlay, f.entry);
    }
});
