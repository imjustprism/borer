//! Companion PDB files with out-of-bounds module, type, address and stream
//! sizes: each loads or skips cleanly and never panics inside `decompile`.

use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicUsize, Ordering};

use borer_engine::analysis::decompile::decompile;
use borer_engine::analysis::{Analysis, Overlay};
use borer_engine::pdb::{Outcome, Skip};
use borer_engine::program::{Program, SymbolKind};

use super::{IMAGE_BASE, measured, put16, put32, put64, serial};

/// Companion PDB bytes from the single-module fuzz seed (`5,632` bytes after the 8-byte base).
const ONE_MODULE_SEED: &[u8] = include_bytes!("../../../../fuzz/seeds/pdb/one-module");

/// Monotonic counter keeping scratch directories distinct across tests.
static NEXT_DIR: AtomicUsize = AtomicUsize::new(0);

/// Temporary directory removed when dropped.
struct ScratchDir {
    /// Directory path holding `fuzz.exe` and `fuzz.pdb`.
    path: PathBuf,
}

impl ScratchDir {
    /// Creates a fresh empty scratch directory for one companion-PDB test.
    ///
    /// # Arguments
    ///
    /// * `pdb` - Companion PDB bytes written to `fuzz.pdb`.
    ///
    /// # Returns
    ///
    /// Guard owning the directory until drop.
    fn with_pdb(pdb: &[u8]) -> Self {
        let id = NEXT_DIR.fetch_add(1, Ordering::Relaxed);
        let path =
            std::env::temp_dir().join(format!("borer-hostile-pdb-{}-{id}", std::process::id()));
        std::fs::create_dir_all(&path).expect("scratch directory created");
        std::fs::write(path.join("fuzz.pdb"), pdb).expect("companion PDB written");
        Self { path }
    }

    /// Path to the synthetic binary inside this directory.
    ///
    /// # Returns
    ///
    /// Path naming `fuzz.exe` beside `fuzz.pdb`.
    fn exe_path(&self) -> PathBuf {
        self.path.join("fuzz.exe")
    }
}

impl Drop for ScratchDir {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.path);
    }
}

/// Writes one PE section header with `0x200` mapped and raw bytes.
///
/// # Arguments
///
/// * `b` - PE image buffer.
/// * `at` - Section header offset.
/// * `name` - Section name bytes (at most 8).
/// * `rva` - Section RVA.
/// * `off` - Raw file offset.
/// * `flags` - `IMAGE_SCN_*` characteristics.
fn pe_row(b: &mut [u8], at: usize, name: &[u8], rva: u32, off: u32, flags: u32) {
    b[at..at + name.len()].copy_from_slice(name);
    put32(b, at + 8, 0x200);
    put32(b, at + 12, rva);
    put32(b, at + 16, 0x200);
    put32(b, at + 20, off);
    put32(b, at + 36, flags);
}

/// Builds the PE32+ image matching `fuzz/seeds/pdb/one-module`: two functions
/// at RVAs `0x1010` (`pick`) and `0x1040` (`entry`), and an `RSDS` record
/// naming `fuzz.pdb` with zero GUID and age `1`.
///
/// # Returns
///
/// Complete `0x600`-byte PE32+ image loaded at [`IMAGE_BASE`].
fn pdb_pe() -> Vec<u8> {
    const SIG: usize = 0x40;
    const OPT: usize = SIG + 24;
    const ROWS: usize = OPT + 0xf0;
    const DATA_OFF: usize = 0x400;
    let mut b = vec![0u8; 0x600];
    b[..2].copy_from_slice(b"MZ");
    put32(&mut b, 0x3c, u32::try_from(SIG).expect("fits"));
    b[SIG..SIG + 4].copy_from_slice(b"PE\0\0");
    put16(&mut b, SIG + 4, 0x8664);
    put16(&mut b, SIG + 6, 2);
    put16(&mut b, SIG + 20, 0xf0);
    put16(&mut b, SIG + 22, 0x22);
    put16(&mut b, OPT, 0x20b);
    put32(&mut b, OPT + 16, 0x1010);
    put64(&mut b, OPT + 24, IMAGE_BASE);
    put32(&mut b, OPT + 32, 0x1000);
    put32(&mut b, OPT + 36, 0x200);
    put16(&mut b, OPT + 48, 6);
    put32(&mut b, OPT + 56, 0x3000);
    put32(&mut b, OPT + 60, 0x200);
    put16(&mut b, OPT + 68, 3);
    put32(&mut b, OPT + 108, 16);
    put32(&mut b, OPT + 112 + 6 * 8, 0x2020);
    put32(&mut b, OPT + 112 + 6 * 8 + 4, 28);
    pe_row(&mut b, ROWS, b".text", 0x1000, 0x200, 0x6000_0020);
    pe_row(&mut b, ROWS + 40, b".data", 0x2000, 0x400, 0xc000_0040);
    // ASM: mov eax, 7; ret
    b[0x210..0x216].copy_from_slice(&[0xb8, 0x07, 0x00, 0x00, 0x00, 0xc3]);
    // ASM: call 0x1010; ret
    b[0x240..0x246].copy_from_slice(&[0xe8, 0xcb, 0xff, 0xff, 0xff, 0xc3]);
    put32(&mut b, DATA_OFF + 0x20 + 12, 2);
    put32(&mut b, DATA_OFF + 0x20 + 16, 33);
    put32(&mut b, DATA_OFF + 0x20 + 20, 0x2040);
    put32(&mut b, DATA_OFF + 0x20 + 24, 0x440);
    b[DATA_OFF + 0x40..DATA_OFF + 0x44].copy_from_slice(b"RSDS");
    put32(&mut b, DATA_OFF + 0x40 + 20, 1);
    b[DATA_OFF + 0x40 + 24..DATA_OFF + 0x40 + 32].copy_from_slice(b"fuzz.pdb");
    b
}

/// Returns a mutable copy of the `5,632`-byte PDB inside [`ONE_MODULE_SEED`].
///
/// # Returns
///
/// Companion PDB bytes starting with the MSF 7.00 magic.
fn seed_pdb() -> Vec<u8> {
    ONE_MODULE_SEED[8..].to_vec()
}

/// Loads [`pdb_pe`] beside `pdb` with debug symbols enabled.
///
/// # Arguments
///
/// * `dir` - Scratch directory holding `fuzz.pdb`.
///
/// # Returns
///
/// Loaded [`Program`] with companion-PDB resolution applied.
fn load_with_pdb(dir: &Path) -> Program {
    Program::from_bytes_with(dir.join("fuzz.exe"), pdb_pe(), true, None)
        .expect("the synthetic PE loads")
}

/// Skips a module line program whose `c13_lines_size` runs past its stream,
/// keeping symbols, signatures and locals and decompiling every function.
///
/// Patches `c13_lines_size` at PDB byte offset `0xa6c` to `0x1_0000` (past
/// Stream 5's `0xf4` bytes) so `ModuleInfo::lines_data` would otherwise panic.
#[test]
fn a_module_line_size_past_its_stream_keeps_symbols_and_decompiles() {
    let _serial = serial();
    let mut pdb = seed_pdb();
    assert_eq!(
        u32::from_le_bytes(pdb[0xa6c..0xa70].try_into().expect("four bytes")),
        0x40,
        "offset 0xa6c in one-module is module 0's c13_lines_size"
    );
    put32(&mut pdb, 0xa6c, 0x1_0000);
    let dir = ScratchDir::with_pdb(&pdb);
    let program = Program::from_bytes_with(dir.exe_path(), pdb_pe(), true, None)
        .expect("the synthetic PE loads");
    assert_eq!(
        program.pdb,
        Some(Outcome::Applied {
            named: 3,
            dropped: 0,
        })
    );
    let syms: Vec<(&str, u64, SymbolKind)> = program
        .symbols
        .iter()
        .map(|s| (s.name.as_str(), s.addr, s.kind))
        .collect();
    assert!(
        syms.contains(&("pick", IMAGE_BASE + 0x1010, SymbolKind::Local)),
        "{syms:?}"
    );
    assert!(
        syms.contains(&("entry", IMAGE_BASE + 0x1040, SymbolKind::Local)),
        "{syms:?}"
    );
    assert!(
        syms.contains(&("DATA", IMAGE_BASE + 0x2018, SymbolKind::Data)),
        "{syms:?}"
    );
    let sub = program
        .debug_functions
        .iter()
        .find(|d| d.name == "pick")
        .expect("pick's signature and locals survive");
    assert_eq!(sub.return_type.as_deref(), Some("uint32_t"));
    let params: Vec<Option<&str>> = sub
        .parameters
        .iter()
        .map(|p| p.type_name.as_deref())
        .collect();
    assert_eq!(params, vec![Some("int32_t"), Some("uint32_t")]);
    for local in ["local", "bias"] {
        assert!(
            sub.locals.values().any(|n| n == local),
            "missing local {local} in {:?}",
            sub.locals
        );
    }
    let analysis = Analysis::compute(&program);
    let overlay = Overlay::default();
    let pick_text = decompile(&program, &analysis, &overlay, IMAGE_BASE + 0x1010)
        .expect("pick decompiles instead of panicking in pdb::sources");
    let entry_text = decompile(&program, &analysis, &overlay, IMAGE_BASE + 0x1040)
        .expect("entry decompiles instead of panicking in pdb::sources");
    assert!(pick_text.contains("pick("), "{pick_text}");
    assert!(!pick_text.contains("// source:"), "{pick_text}");
    assert!(entry_text.contains("entry("), "{entry_text}");
    assert!(entry_text.contains("pick("), "{entry_text}");
    assert!(!entry_text.contains("// source:"), "{entry_text}");
}

/// Hostile TPI argument counts, overflowing section offsets, amplified MSF
/// stream lengths and malformed C13 line blocks neither panic nor allocate
/// beyond the input bound.
#[test]
fn hostile_pdb_type_address_and_stream_headers_neither_panic_nor_amplify() {
    let _serial = serial();

    let mut huge_args = seed_pdb();
    put32(&mut huge_args, 0x83c, 0x4000_0000);
    let dir_args = ScratchDir::with_pdb(&huge_args);
    let (prog_args, extra_args) = measured(|| load_with_pdb(&dir_args.path));
    assert!(
        extra_args < 2 << 20,
        "oversized LF_ARGLIST allocated {extra_args} bytes"
    );
    assert_eq!(
        prog_args.pdb,
        Some(Outcome::Applied {
            named: 3,
            dropped: 0,
        })
    );
    let a_args = Analysis::compute(&prog_args);
    assert!(
        decompile(
            &prog_args,
            &a_args,
            &Overlay::default(),
            IMAGE_BASE + 0x1010
        )
        .is_some(),
        "oversized LF_ARGLIST still decompiles"
    );

    let mut overflow_rva = seed_pdb();
    put32(&mut overflow_rva, 0xc24, 0xffff_fff0);
    let dir_rva = ScratchDir::with_pdb(&overflow_rva);
    let prog_rva = load_with_pdb(&dir_rva.path);
    let a_rva = Analysis::compute(&prog_rva);
    assert!(
        decompile(&prog_rva, &a_rva, &Overlay::default(), IMAGE_BASE + 0x1040).is_some(),
        "overflowing PdbInternalSectionOffset decompiles without panic"
    );

    let mut bad_block = seed_pdb();
    put32(&mut bad_block, 0xce0, 4);
    let dir_block = ScratchDir::with_pdb(&bad_block);
    let prog_block = load_with_pdb(&dir_block.path);
    let a_block = Analysis::compute(&prog_block);
    assert!(
        decompile(
            &prog_block,
            &a_block,
            &Overlay::default(),
            IMAGE_BASE + 0x1010
        )
        .is_some(),
        "underflowing C13 block_size skips the line block and decompiles"
    );

    let mut amp_msf = seed_pdb();
    put32(&mut amp_msf, 0x1208, 0x4000_0000);
    let dir_msf = ScratchDir::with_pdb(&amp_msf);
    let (prog_msf, extra_msf) = measured(|| load_with_pdb(&dir_msf.path));
    assert_eq!(prog_msf.pdb, Some(Outcome::Skipped(Skip::Unreadable)));
    assert!(
        extra_msf < 2 << 20,
        "amplified MSF stream allocated {extra_msf} bytes"
    );
}
