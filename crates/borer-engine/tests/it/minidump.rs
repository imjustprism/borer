//! Minidump and ELF core loading: a dump's memory, mapped as a program.

#![expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]

use borer_engine::program::Program;

/// Writes a `u16` at `at`, little-endian.
fn u16_at(out: &mut [u8], at: usize, v: u16) {
    out[at..at + 2].copy_from_slice(&v.to_le_bytes());
}

/// Writes a `u32` at `at`, little-endian.
fn u32_at(out: &mut [u8], at: usize, v: u32) {
    out[at..at + 4].copy_from_slice(&v.to_le_bytes());
}

/// Writes a `u64` at `at`, little-endian.
fn u64_at(out: &mut [u8], at: usize, v: u64) {
    out[at..at + 8].copy_from_slice(&v.to_le_bytes());
}

/// A minidump of an x64 process: one module, one memory range holding
/// `ret`, an exception context naming where it stopped.
///
/// # Returns
///
/// The dump's bytes.
fn dump() -> Vec<u8> {
    // The layout: header (32), directory (4 entries, 48), memory list
    // (4 + 16), module list (4 + 108), system info (4), exception stream
    // (168) and its context (0x100), then the memory's bytes.
    let mut d = vec![0u8; 0x400];
    d[..4].copy_from_slice(b"MDMP");
    u32_at(&mut d, 4, 0xA793); // the version's high half
    u32_at(&mut d, 8, 4); // four streams
    let dir = 32;
    u32_at(&mut d, 12, u32::try_from(dir).unwrap_or(0));
    // MemoryListStream: one range at file 0x380 mapping 0x7ff0_0000.
    u32_at(&mut d, dir, 5);
    u32_at(&mut d, dir + 4, 4 + 16);
    u32_at(&mut d, dir + 8, 0x80);
    u32_at(&mut d, 0x80, 1);
    u64_at(&mut d, 0x84, 0x7ff0_0000);
    u32_at(&mut d, 0x8c, 0x20);
    u32_at(&mut d, 0x90, 0x380);
    // ModuleListStream: one module at 0x140000000 named a.exe.
    u32_at(&mut d, dir + 12, 4);
    u32_at(&mut d, dir + 16, 4 + 108);
    u32_at(&mut d, dir + 20, 0xa0);
    u32_at(&mut d, 0xa0, 1);
    u64_at(&mut d, 0xa4, 0x1_4000_0000);
    u32_at(&mut d, 0xac, 0x1000);
    u32_at(&mut d, 0xb8, 0x118); // the name
    let mut name: Vec<u8> = 10u32.to_le_bytes().to_vec();
    for u in "a.exe".encode_utf16() {
        name.extend_from_slice(&u.to_le_bytes());
    }
    d[0x118..0x118 + name.len()].copy_from_slice(&name);
    // SystemInfoStream: AMD64.
    u32_at(&mut d, dir + 24, 7);
    u32_at(&mut d, dir + 28, 4);
    u32_at(&mut d, dir + 32, 0xd0);
    u32_at(&mut d, 0xd0, 9);
    // ExceptionStream: a context at 0x200 whose Rip is in the range.
    u32_at(&mut d, dir + 36, 6);
    u32_at(&mut d, dir + 40, 168);
    u32_at(&mut d, dir + 44, 0x100);
    u32_at(&mut d, 0x100 + 160, 0xf8);
    u32_at(&mut d, 0x100 + 164, 0x200);
    u64_at(&mut d, 0x200 + 0xf8, 0x7ff0_0010);
    // The memory: a ret, and bytes around it.
    d[0x380] = 0xc3;
    d
}

/// A minidump loads as a program: its ranges are sections that read back
/// the dumped bytes, its module names its base, and the exception
/// context's stop address is the entry.
#[test]
fn a_minidump_loads_as_its_memory() {
    let p = Program::from_bytes("crash.dmp".into(), dump()).expect("loads");
    assert_eq!(p.arch, borer_engine::program::Arch::X86_64);
    assert_eq!(p.entry, Some(0x7ff0_0010));
    assert_eq!(p.image_base, 0x1_4000_0000);
    assert_eq!(p.symbols.len(), 1);
    assert_eq!(p.symbols[0].name, "a.exe");
    assert_eq!(p.symbols[0].addr, 0x1_4000_0000);
    let read = p.read_va_upto(0x7ff0_0000, 4).expect("mapped");
    assert_eq!(read.first(), Some(&0xc3));
    assert!(p.section_at(0x7ff0_0010).is_some());
    assert!(p.headers.kind.is_some_and(|k| k.contains("minidump")));
}

/// A dump whose directory or header does not sit in the file refuses to
/// load, saying so, rather than answering empty.
#[test]
fn a_cut_minidump_is_refused() {
    let cut = &dump()[..0x20];
    assert!(Program::from_bytes("cut.dmp".into(), cut.to_vec()).is_err());
}

/// An ELF core maps its `PT_LOAD` segments as the memory they hold.
#[test]
fn an_elf_core_loads_its_load_segments() {
    // An ET_CORE ELF64 with one PT_LOAD: `ret` at 0x7ff0_0000.
    let mut e = vec![0u8; 0x120];
    e[..4].copy_from_slice(&[0x7f, b'E', b'L', b'F']);
    e[4] = 2; // ELFCLASS64
    e[5] = 1; // little-endian
    u16_at(&mut e, 16, 4); // ET_CORE
    u16_at(&mut e, 18, 62); // x86-64
    u32_at(&mut e, 20, 1); // EV_CURRENT
    u64_at(&mut e, 32, 0x40); // the program headers
    u16_at(&mut e, 52, 64); // the header size
    u16_at(&mut e, 54, 56); // one header
    u16_at(&mut e, 56, 1); // of it
    u32_at(&mut e, 0x40, 1); // PT_LOAD
    u32_at(&mut e, 0x44, 5); // r-x
    u64_at(&mut e, 0x48, 0x80); // offset
    u64_at(&mut e, 0x50, 0x7ff0_0000); // vaddr
    u64_at(&mut e, 0x58, 0x10); // filesz
    u64_at(&mut e, 0x60, 0x10); // memsz
    e[0x80] = 0xc3;
    let p = Program::from_bytes("core.elf".into(), e).expect("loads");
    assert_eq!(p.arch, borer_engine::program::Arch::X86_64);
    let read = p.read_va_upto(0x7ff0_0000, 4).expect("mapped");
    assert_eq!(read.first(), Some(&0xc3));
}
