//! Discovery sums the sizes a file states without overflowing, and reads
//! unwind entries that name each other without looping.
//!
//! An ELF whose function symbols claim more bytes together than the address
//! space holds is read, and its sizes are summed saturating, never past
//! `u64::MAX` (a mutation of a corpus library found the sum trap under
//! overflow checks). A PE32+ `.pdata` entry whose odd unwind address names
//! itself, or two that name each other, loads (the `nested` fuzz target found
//! goblin following that chain forever).

use std::path::PathBuf;

use borer_engine::analysis::Analysis;
use borer_engine::program::Program;

use super::{CODE, DATA, IMAGE_BASE, Sec, elfgen, load, pe, put32, serial, text};

/// The exception directory's slot.
const EXCEPTION_DIR: usize = 3;

/// Where `.pdata` maps.
const PDATA: u32 = 0x2000;

/// Where `.xdata` maps.
const XDATA: u32 = 0x3000;

/// Entries in the test's `.pdata`, each two bytes of `.text`.
const ENTRY_COUNT: usize = 26;

/// How long a load may take before the test calls it a hang, in seconds.
const BOUND_SECS: u64 = 10;

/// Returns the address of `.pdata` entry `k`, relative to the image base.
fn slot(k: usize) -> u32 {
    PDATA + 12 * u32::try_from(k).expect("few entries")
}

/// Returns entry `k`'s function as `(start, end)` virtual addresses.
fn extent(k: usize) -> (u64, u64) {
    let start = IMAGE_BASE + 0x1000 + 2 * u64::try_from(k).expect("few entries");
    (start, start + 2)
}

/// Returns each entry's unwind address.
///
/// Entry 0 names itself, 1 and 2 name each other, 3 names 4 whose info at
/// [`XDATA`] is chained, 5 names an address past the directory, 6 an
/// address inside it that starts no entry, 7 reaches chained info after
/// eight hops and 16 after nine.
fn unwind_addresses() -> [u32; ENTRY_COUNT] {
    let mut unwind = [0; ENTRY_COUNT];
    unwind[0] = slot(0) | 1;
    unwind[1] = slot(2) | 1;
    unwind[2] = slot(1) | 1;
    unwind[3] = slot(4) | 1;
    unwind[4] = XDATA;
    unwind[5] = slot(ENTRY_COUNT) | 1;
    unwind[6] = (slot(1) + 4) | 1;
    for k in (7..15).chain(16..25) {
        unwind[k] = slot(k + 1) | 1;
    }
    unwind[15] = XDATA;
    unwind[25] = XDATA;
    unwind
}

/// Unwind entries whose indirections never end load within the bound.
///
/// Those that loop, leave the directory or run past eight hops are each a
/// function with no unwind info; chains of one to eight hops reach the
/// chained info they name.
///
/// # Panics
///
/// When the load takes longer than [`BOUND_SECS`], a refused entry is not a
/// function range, or the chained chunks are not the entries that reach
/// [`XDATA`] within eight hops.
#[test]
fn unwind_entries_naming_each_other_load_without_looping() {
    let _held = serial();
    let mut pdata = vec![0u8; ENTRY_COUNT * 12];
    for (k, unwind) in unwind_addresses().into_iter().enumerate() {
        let (start, end) = extent(k);
        put32(
            &mut pdata,
            k * 12,
            u32::try_from(start - IMAGE_BASE).expect("fits"),
        );
        put32(
            &mut pdata,
            k * 12 + 4,
            u32::try_from(end - IMAGE_BASE).expect("fits"),
        );
        put32(&mut pdata, k * 12 + 8, unwind);
    }
    let mut xdata = vec![0u8; 16];
    xdata[0] = 1 | (4 << 3);
    let size = u32::try_from(pdata.len()).expect("fits");
    let bytes = pe(
        &[
            Sec::sound(".text", 0x1000, text(), CODE),
            Sec::sound(".pdata", PDATA, pdata, DATA),
            Sec::sound(".xdata", XDATA, xdata, DATA),
        ],
        &[(EXCEPTION_DIR, PDATA, size)],
    );
    let (send, done) = std::sync::mpsc::channel();
    std::thread::spawn(move || send.send(load(bytes)).expect("the test waits"));
    let p = done
        .recv_timeout(std::time::Duration::from_secs(BOUND_SECS))
        .expect("the load ends within the bound");
    for k in [0, 1, 2, 5, 6, 16] {
        assert!(
            p.function_ranges.contains(&extent(k)),
            "entry {k}: {:x?}",
            p.function_ranges
        );
    }
    let chained: Vec<_> = [3, 4]
        .into_iter()
        .chain(7..16)
        .chain(17..ENTRY_COUNT)
        .map(extent)
        .collect();
    assert_eq!(p.headers.chained_chunks, chained);
}
/// Two function symbols of 2^63 bytes each load and are discovered
/// without the sum of their sizes overflowing.
///
/// # Panics
///
/// When the image does not load, the sum overflows, or the entry is not
/// discovered.
#[test]
fn function_sizes_past_the_address_space_sum_without_overflow() {
    let _held = serial();
    let mut symtab = vec![0u8; 24];
    for k in 0..2u64 {
        symtab.extend(elfgen::sym_sized(1, 0x12, 1, 0x1000 + k, 1 << 63));
    }
    let code = vec![0xc3; 0x10];
    let mut secs = vec![
        elfgen::Sec::new(".text", elfgen::PROGBITS, elfgen::AX, 0x1000, code),
        elfgen::Sec::new(".symtab", elfgen::SYMTAB, 0, 0x2000, symtab),
        elfgen::Sec::new(".strtab", elfgen::STRTAB, 0, 0x3000, b"\0f\0".to_vec()),
    ];
    secs[1].link = 3;
    secs[1].info = 1;
    secs[1].entsize = 24;
    let bytes = elfgen::build(elfgen::ET_EXEC, elfgen::EM_X86_64, 0x1000, &secs);
    let p = Program::from_bytes(PathBuf::from("sizes.elf"), bytes).expect("the image loads");
    assert!(p.function_ranges.len() >= 2, "{:?}", p.function_ranges);
    let a = Analysis::compute(&p);
    assert!(a.function(0x1000).is_some());
}
