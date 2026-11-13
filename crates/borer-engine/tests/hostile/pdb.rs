//! Companion PDB files with out-of-bounds module, type, address and stream
//! sizes: each loads or skips cleanly and never panics inside `decompile`.

use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicUsize, Ordering};

use borer_engine::analysis::decompile::decompile;
use borer_engine::analysis::{Analysis, Overlay};
use borer_engine::pdb::{Outcome, Skip};
use borer_engine::program::{Program, SymbolKind};

use super::{IMAGE_BASE, LOAD_HEAP_PER_BYTE, measured, put16, put32, put64, serial};

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

/// Short TPI records, invalid `LF_POINTER` modes and huge MSF `page_size`
/// headers neither panic nor amplify memory.
#[test]
fn short_tpi_pointer_modes_and_huge_msf_pages_stay_bounded() {
    let _serial = serial();
    let pe_len = pdb_pe().len();

    let mut zero_tpi = seed_pdb();
    put32(&mut zero_tpi, 0x80c, 0x1003);
    put32(&mut zero_tpi, 0x810, 34);
    put32(&mut zero_tpi, 0x120c, 56 + 34);
    zero_tpi[0x838..0x85a].fill(0);
    put16(&mut zero_tpi, 0x838, 0);
    put16(&mut zero_tpi, 0x83a, 14);
    put16(&mut zero_tpi, 0x83c, 0x1008);
    put32(&mut zero_tpi, 0x83e, 0x75);
    put16(&mut zero_tpi, 0x844, 2);
    put32(&mut zero_tpi, 0x846, 0x1002);
    put16(&mut zero_tpi, 0x84a, 14);
    put16(&mut zero_tpi, 0x84c, 0x1201);
    put32(&mut zero_tpi, 0x84e, 0x3fff_ffff);
    let dir_zero = ScratchDir::with_pdb(&zero_tpi);
    let (prog_zero, extra_zero) = measured(|| load_with_pdb(&dir_zero.path));
    assert!(
        extra_zero < 2 << 20,
        "zero-length TPI record bypassed guard and allocated {extra_zero} bytes"
    );
    let a_zero = Analysis::compute(&prog_zero);
    assert!(
        decompile(
            &prog_zero,
            &a_zero,
            &Overlay::default(),
            IMAGE_BASE + 0x1010
        )
        .is_some()
    );

    let mut empty_item = seed_pdb();
    put32(&mut empty_item, 0x808, 0x1001);
    put32(&mut empty_item, 0x80c, 0x1002);
    put32(&mut empty_item, 0x810, 2);
    put32(&mut empty_item, 0x120c, 58);
    put16(&mut empty_item, 0x838, 0);
    let dir_empty = ScratchDir::with_pdb(&empty_item);
    let prog_empty = load_with_pdb(&dir_empty.path);
    let a_empty = Analysis::compute(&prog_empty);
    assert!(
        decompile(
            &prog_empty,
            &a_empty,
            &Overlay::default(),
            IMAGE_BASE + 0x1010
        )
        .is_some()
    );

    let mut bad_ptr = seed_pdb();
    put32(&mut bad_ptr, 0x810, 28);
    put32(&mut bad_ptr, 0x120c, 56 + 28);
    bad_ptr[0x838..0x854].fill(0);
    put16(&mut bad_ptr, 0x838, 10);
    put16(&mut bad_ptr, 0x83a, 0x1002);
    put32(&mut bad_ptr, 0x83c, 0x74);
    put32(&mut bad_ptr, 0x840, 7 << 5);
    put16(&mut bad_ptr, 0x844, 14);
    put16(&mut bad_ptr, 0x846, 0x1008);
    put32(&mut bad_ptr, 0x848, 0x1000);
    let dir_ptr = ScratchDir::with_pdb(&bad_ptr);
    let prog_ptr = load_with_pdb(&dir_ptr.path);
    let a_ptr = Analysis::compute(&prog_ptr);
    assert!(
        decompile(&prog_ptr, &a_ptr, &Overlay::default(), IMAGE_BASE + 0x1010).is_some(),
        "invalid LF_POINTER mode must not hit unreachable!()"
    );

    let mut huge_page = seed_pdb()[..4096].to_vec();
    put32(&mut huge_page, 32, 0x80_0000);
    put32(&mut huge_page, 40, 2);
    put32(&mut huge_page, 44, 4);
    put32(&mut huge_page, 52, 1);
    let dir_hp = ScratchDir::with_pdb(&huge_page);
    let (prog_hp, extra_hp) = measured(|| load_with_pdb(&dir_hp.path));
    assert_eq!(prog_hp.pdb, Some(Outcome::Skipped(Skip::Unreadable)));
    assert!(
        extra_hp <= LOAD_HEAP_PER_BYTE * (huge_page.len() + pe_len) + (256 << 10),
        "8 MiB MSF page_size on 4 KiB file allocated {extra_hp} bytes"
    );
}

/// Packs `streams` into an MSF 7.00 image with `0x200`-byte pages.
///
/// # Arguments
///
/// * `streams` - Raw stream byte slices in directory order.
///
/// # Returns
///
/// Complete MSF 7.00 container at least `4,096` bytes long.
fn pack_msf(streams: &[Vec<u8>]) -> Vec<u8> {
    const PAGE: usize = 0x200;
    let mut pages = vec![vec![0u8; PAGE], vec![0xff; PAGE], vec![0xff; PAGE]];
    let mut dir = Vec::new();
    dir.extend_from_slice(&u32::try_from(streams.len()).expect("fits").to_le_bytes());
    let mut stream_pages = Vec::new();
    for s in streams {
        dir.extend_from_slice(&u32::try_from(s.len()).expect("fits").to_le_bytes());
        for chunk in s.chunks(PAGE) {
            stream_pages.push(u32::try_from(pages.len()).expect("fits"));
            let mut p = vec![0u8; PAGE];
            p[..chunk.len()].copy_from_slice(chunk);
            pages.push(p);
        }
    }
    for pg in stream_pages {
        dir.extend_from_slice(&pg.to_le_bytes());
    }
    let mut dir_pages = Vec::new();
    for chunk in dir.chunks(PAGE) {
        dir_pages.push(u32::try_from(pages.len()).expect("fits"));
        let mut p = vec![0u8; PAGE];
        p[..chunk.len()].copy_from_slice(chunk);
        pages.push(p);
    }
    let list_pg = u32::try_from(pages.len()).expect("fits");
    let mut lp = vec![0u8; PAGE];
    for (i, pg) in dir_pages.iter().enumerate() {
        put32(&mut lp, i * 4, *pg);
    }
    pages.push(lp);
    while pages.len() * PAGE < 4096 {
        pages.push(vec![0u8; PAGE]);
    }
    let total = u32::try_from(pages.len()).expect("fits");
    pages[0][..32].copy_from_slice(b"Microsoft C/C++ MSF 7.00\r\n\x1aDS\0\0\0");
    put32(&mut pages[0], 32, u32::try_from(PAGE).expect("fits"));
    put32(&mut pages[0], 36, 1);
    put32(&mut pages[0], 40, total);
    put32(&mut pages[0], 44, u32::try_from(dir.len()).expect("fits"));
    put32(&mut pages[0], 52, list_pg);
    pages.concat()
}

/// Repeated `DBIModuleInfo.stream` references and deeply nested `S_BLOCK32`
/// records skip duplicate module streams and keep scope/line walks linear.
#[test]
fn duplicate_module_streams_and_deep_block_scopes_stay_linear() {
    let _serial = serial();
    let seed = seed_pdb();
    let u32_le = |at: usize| {
        usize::try_from(u32::from_le_bytes(seed[at..at + 4].try_into().expect("4"))).expect("usize")
    };
    let s1 = seed[0x600..0x600 + u32_le(0x1208)].to_vec();
    let s2 = seed[0x800..0x800 + u32_le(0x120c)].to_vec();
    let sym_len = u32_le(0xa64);
    let c13_len = u32_le(0xa6c);
    let mut mod_syms = seed[0xc00..0xc00 + sym_len].to_vec();
    for _ in 0..4096 {
        mod_syms.extend_from_slice(&[2, 0, 0x03, 0x11]);
    }
    let mut c13 = seed[0xc00 + sym_len..0xc00 + sym_len + c13_len].to_vec();
    c13.extend_from_slice(&0xf2u32.to_le_bytes());
    c13.extend_from_slice(&32u32.to_le_bytes());
    c13.extend_from_slice(&0u32.to_le_bytes());
    c13.extend_from_slice(&0u16.to_le_bytes());
    c13.extend_from_slice(&0u16.to_le_bytes());
    c13.extend_from_slice(&0x10u32.to_le_bytes());
    c13.extend_from_slice(&0u32.to_le_bytes());
    c13.extend_from_slice(&1u32.to_le_bytes());
    c13.extend_from_slice(&20u32.to_le_bytes());
    c13.extend_from_slice(&0u32.to_le_bytes());
    c13.extend_from_slice(&0x8000_0001u32.to_le_bytes());
    let mut s5 = mod_syms.clone();
    s5.extend_from_slice(&c13);
    let mod_info_len = u32_le(0xa18);
    let dbg_len = u32_le(0xa30);
    let mut one_mod = seed[0xa40..0xa40 + mod_info_len].to_vec();
    put32(
        &mut one_mod,
        36,
        u32::try_from(mod_syms.len()).expect("fits"),
    );
    put32(&mut one_mod, 44, u32::try_from(c13.len()).expect("fits"));
    let mod_list = one_mod.repeat(256);
    let dbg = seed[0xa40 + mod_info_len..0xa40 + mod_info_len + dbg_len].to_vec();
    let mut s3 = seed[0xa00..0xa40].to_vec();
    put32(&mut s3, 24, u32::try_from(mod_list.len()).expect("fits"));
    s3.extend_from_slice(&mod_list);
    s3.extend_from_slice(&dbg);
    let s6 = seed[0xe00..0xe00 + u32_le(0x121c)].to_vec();
    let s7 = seed[0x1000..0x1000 + u32_le(0x1220)].to_vec();
    let pdb = pack_msf(&[Vec::new(), s1, s2, s3, Vec::new(), s5, s6, s7]);
    let dir = ScratchDir::with_pdb(&pdb);
    #[expect(
        clippy::disallowed_methods,
        reason = "the test bounds the time a hostile DBI module list and scope chain take"
    )]
    let started = std::time::Instant::now();
    let (prog, extra) = measured(|| load_with_pdb(&dir.path));
    assert_eq!(
        prog.pdb,
        Some(Outcome::Applied {
            named: 3,
            dropped: 0,
        })
    );
    let analysis = Analysis::compute(&prog);
    let text = decompile(&prog, &analysis, &Overlay::default(), IMAGE_BASE + 0x1010)
        .expect("pick decompiles cleanly");
    assert!(started.elapsed() < std::time::Duration::from_secs(2));
    assert!(
        extra <= LOAD_HEAP_PER_BYTE * (pdb.len() + pdb_pe().len()) + (1 << 20),
        "duplicate module streams allocated {extra} bytes on {} bytes",
        pdb.len()
    );
    assert!(text.contains("pick("), "{text}");
}
