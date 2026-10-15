//! Minidump and ELF core loading: a dump's memory, mapped as a program,
//! and the hostile headers a half-written or forged dump brings.

#![expect(
    clippy::missing_panics_doc,
    clippy::expect_used,
    reason = "assertions are the point of a test"
)]

use borer_engine::program::{Arch, Program};

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

// ---- fixtures ----

/// A minidump of an x64 process: one module, one memory range holding
/// `ret`, an exception context naming where it stopped.
///
/// The directory (at 32) names four streams and ends at 0x50; the first
/// stream sits at 0x80, leaving four spare directory slots at 0x50..0x80
/// for [`add_stream`]. The memory list names one range at file 0x380
/// mapping `0x7ff0_0000`; its count sits at 0x80 and the range's start,
/// size and file offset at 0x84, 0x8c and 0x90. The module list (0xa0)
/// names one module at 0x140000000 whose name (0x118) is `a.exe`. The
/// system-info stream (0xd0) states AMD64. The exception stream (0x100)
/// points at a context (0x200) of the x64 size whose Rip names an
/// address inside the range.
///
/// # Returns
///
/// The dump's bytes.
fn dump() -> Vec<u8> {
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
    u32_at(&mut d, 0x100 + 160, 0x4d0); // a full x64 CONTEXT's size
    u32_at(&mut d, 0x100 + 164, 0x200);
    u64_at(&mut d, 0x200 + 0xf8, 0x7ff0_0010);
    // The memory: a ret, and bytes around it.
    d[0x380] = 0xc3;
    d
}

/// Appends one more stream to the [`dump`] fixture: a directory entry in
/// the spare slots its header leaves (0x50..0x80, four of them) and the
/// stream's bytes at the end of the file.
///
/// # Arguments
///
/// * `d` - The dump, grown by the stream.
/// * `kind` - The stream type (`ThreadListStream` 3, `Memory64ListStream`
///   9, `MemoryInfoListStream` 16).
/// * `stream` - The stream's bytes, relocated as they are.
///
/// # Returns
///
/// The stream's file offset.
fn add_stream(d: &mut Vec<u8>, kind: u32, stream: &[u8]) -> usize {
    let entries = u32::from_le_bytes(d[8..12].try_into().expect("four bytes"));
    let at = 32 + usize::try_from(entries).expect("fits") * 12;
    let rva = d.len();
    u32_at(d, at, kind);
    u32_at(d, at + 4, u32::try_from(stream.len()).expect("fits"));
    u32_at(d, at + 8, u32::try_from(rva).expect("fits"));
    d.extend_from_slice(stream);
    u32_at(d, 8, entries + 1);
    rva
}

/// Moves the fixture's `MemoryListStream` to `ranges` as `(start, bytes)`,
/// each range's bytes appended to the file and mapped where it says.
fn set_memory(d: &mut Vec<u8>, ranges: &[(u64, &[u8])]) {
    let mut list = vec![0u8; 4 + 16 * ranges.len()];
    u32_at(&mut list, 0, u32::try_from(ranges.len()).expect("fits"));
    for (k, &(start, bytes)) in ranges.iter().enumerate() {
        let at = d.len();
        let e = 4 + 16 * k;
        u64_at(&mut list, e, start);
        u32_at(&mut list, e + 8, u32::try_from(bytes.len()).expect("fits"));
        u32_at(&mut list, e + 12, u32::try_from(at).expect("fits"));
        d.extend_from_slice(bytes);
    }
    let list_at = d.len();
    d.extend_from_slice(&list);
    u32_at(d, 40, u32::try_from(list_at).expect("fits"));
}

/// Builds a `ThreadListStream` of one thread per stack, as
/// `(start, size, file offset)`.
///
/// # Returns
///
/// The stream's bytes.
fn threads(stacks: &[(u64, u32, u32)]) -> Vec<u8> {
    let mut s = vec![0u8; 4 + 48 * stacks.len()];
    u32_at(&mut s, 0, u32::try_from(stacks.len()).expect("fits"));
    for (k, &(start, size, at)) in stacks.iter().enumerate() {
        let e = 4 + 48 * k;
        u64_at(&mut s, e + 24, start);
        u32_at(&mut s, e + 32, size);
        u32_at(&mut s, e + 36, at);
    }
    s
}

/// Builds a `Memory64ListStream` packing `ranges` as `(start, size)` from
/// file offset `base`, one after another.
///
/// # Returns
///
/// The stream's bytes.
fn memory64(base: u64, ranges: &[(u64, u64)]) -> Vec<u8> {
    let mut s = vec![0u8; 16 + 16 * ranges.len()];
    u64_at(&mut s, 0, base);
    u64_at(&mut s, 8, u64::try_from(ranges.len()).expect("fits"));
    for (k, &(start, size)) in ranges.iter().enumerate() {
        let e = 16 + 16 * k;
        u64_at(&mut s, e, start);
        u64_at(&mut s, e + 8, size);
    }
    s
}

/// Builds a `MemoryInfoListStream` stating `entries` as
/// `(base, size, protection)`, each `entry` bytes apart as its header
/// claims (the real `MINIDUMP_MEMORY_INFO` is 48).
///
/// # Returns
///
/// The stream's bytes.
fn memory_info(entry: u32, entries: &[(u64, u64, u32)]) -> Vec<u8> {
    let mut s = vec![0u8; 16 + 48 * entries.len()];
    u32_at(&mut s, 0, 16);
    u32_at(&mut s, 4, entry);
    u64_at(&mut s, 8, u64::try_from(entries.len()).expect("fits"));
    for (k, &(base, size, protect)) in entries.iter().enumerate() {
        let e = 16 + 48 * k;
        u64_at(&mut s, e, base);
        u64_at(&mut s, e + 24, size);
        u32_at(&mut s, e + 36, protect);
    }
    s
}

/// An ELF core of an x64 process: one `PT_LOAD` holding `ret` at
/// `0x7ff0_0000`, its bytes at file 0x80.
///
/// # Returns
///
/// The core's bytes.
fn elf_core() -> Vec<u8> {
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
    u64_at(&mut e, 0x48, 0x80); // p_offset
    u64_at(&mut e, 0x50, 0x7ff0_0000); // p_vaddr
    u64_at(&mut e, 0x58, 0x7ff0_0000); // p_paddr
    u64_at(&mut e, 0x60, 0x10); // p_filesz
    u64_at(&mut e, 0x68, 0x10); // p_memsz
    e[0x80] = 0xc3;
    e
}

/// Whether every section's file extent sits inside the file: the bound
/// every claimed range and segment clamps to.
fn sections_sit_in_the_file(p: &Program) -> bool {
    let len = u64::try_from(p.bytes.len()).unwrap_or(u64::MAX);
    p.sections
        .iter()
        .all(|s| (s.file_size == 0 || s.file_off.0 < len) && s.file_off.0 + s.file_size <= len)
}

/// A splitmix64 generator: a deterministic, dependency-free sequence.
#[derive(Debug)]
struct SplitMix64(u64);

impl SplitMix64 {
    /// The next value of the sequence.
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        z ^ (z >> 31)
    }
}

// ---- loading ----

/// A minidump loads as a program: its ranges are sections that read back
/// the dumped bytes, its module names its base, and the exception
/// context's stop address is the entry.
#[test]
fn a_minidump_loads_as_its_memory() {
    let p = Program::from_bytes("crash.dmp".into(), dump()).expect("loads");
    assert_eq!(p.arch, Arch::X86_64);
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

/// A directory count claiming more entries than the file can hold
/// refuses to load: the directory does not sit in the file.
#[test]
fn a_directory_count_past_the_file_is_refused() {
    let mut d = dump();
    u32_at(&mut d, 8, 0x1000);
    assert!(Program::from_bytes("count.dmp".into(), d).is_err());
}

/// A directory whose RVA sits past the end of the file refuses to load.
#[test]
fn a_directory_past_the_file_is_refused() {
    let mut d = dump();
    u32_at(&mut d, 12, 0x1_0000);
    assert!(Program::from_bytes("dir.dmp".into(), d).is_err());
}

/// A dump with zero streams still loads: nothing mapped, no entry, no
/// base, an unknown architecture.
#[test]
fn a_dump_with_no_streams_loads_empty() {
    let mut d = dump();
    u32_at(&mut d, 8, 0);
    let p = Program::from_bytes("empty.dmp".into(), d).expect("loads");
    assert!(p.sections.is_empty());
    assert_eq!(p.arch, Arch::Unknown);
    assert_eq!(p.entry, None);
    assert_eq!(p.image_base, 0);
}

/// Version garbage still loads: only the magic and the directory place
/// the format, and the version half is never read.
#[test]
fn version_garbage_still_loads() {
    let mut d = dump();
    u32_at(&mut d, 4, 0xffff_ffff);
    let p = Program::from_bytes("ver.dmp".into(), d).expect("loads");
    assert_eq!(p.arch, Arch::X86_64);
    assert_eq!(p.entry, Some(0x7ff0_0010));
}

// ---- the memory list ----

/// A range whose file offset sits past the end of the file is skipped:
/// the dump holds none of its bytes, so no section maps it.
#[test]
fn a_range_past_the_files_end_is_skipped() {
    let mut d = dump();
    u32_at(&mut d, 0x90, 0x1_0000);
    let p = Program::from_bytes("far.dmp".into(), d).expect("loads");
    assert!(p.sections.is_empty());
    assert!(p.section_at(0x7ff0_0000).is_none());
    assert!(p.read_va_upto(0x7ff0_0000, 4).is_none());
}

/// A range longer than what the file holds from its offset is clamped:
/// the section answers for the bytes the file does hold, and a read past
/// them fails cleanly.
#[test]
fn a_range_longer_than_the_file_is_clamped_to_it() {
    let mut d = dump();
    u32_at(&mut d, 0x8c, 0x1000);
    let p = Program::from_bytes("clamp.dmp".into(), d).expect("loads");
    let held = 0x400 - 0x380;
    let s = p.section_at(0x7ff0_0000).expect("clamped");
    assert_eq!(s.file_size, held);
    assert_eq!(
        p.read_va_upto(0x7ff0_0000, 4).and_then(|b| b.first()),
        Some(&0xc3)
    );
    assert!(p.read_va_upto(0x7ff0_0000 + held - 1, 4).is_some());
    assert!(p.read_va_upto(0x7ff0_0000 + held, 4).is_none());
}

/// A range of size zero holds nothing and maps no section.
#[test]
fn a_zero_size_range_is_skipped() {
    let mut d = dump();
    u32_at(&mut d, 0x8c, 0);
    let p = Program::from_bytes("zero.dmp".into(), d).expect("loads");
    assert!(p.sections.is_empty());
}

/// A memory list of zero ranges loads; the exception's stop address
/// needs no memory to be read.
#[test]
fn a_memory_list_of_no_ranges_loads() {
    let mut d = dump();
    u32_at(&mut d, 0x80, 0);
    let p = Program::from_bytes("none.dmp".into(), d).expect("loads");
    assert!(p.sections.is_empty());
    assert_eq!(p.entry, Some(0x7ff0_0010));
}

/// A range whose size overflows when added to its start still reads: the
/// span saturates and the file-backed bytes answer at the range's start,
/// never panicking.
#[test]
fn a_range_whose_end_overflows_still_reads() {
    let mut d = dump();
    u64_at(&mut d, 0x84, u64::MAX - 0x10);
    u32_at(&mut d, 0x8c, 0x20);
    let p = Program::from_bytes("end.dmp".into(), d).expect("loads");
    assert!(p.section_at(u64::MAX - 0x10).is_some());
    assert_eq!(
        p.read_va_upto(u64::MAX - 0x10, 1).and_then(|b| b.first()),
        Some(&0xc3)
    );
}

/// A memory list claiming billions of ranges stays bounded: the entries
/// that parse hold file extents inside the file, and the count is capped.
#[test]
fn a_huge_range_count_stays_bounded() {
    let mut d = dump();
    u32_at(&mut d, 0x80, 0xffff_ffff);
    let p = Program::from_bytes("many.dmp".into(), d).expect("loads");
    assert!(p.sections.len() <= 0x1_0000);
    assert!(sections_sit_in_the_file(&p));
}

// ---- the memory64 list ----

/// Memory64 ranges packed from a base past the end of the file are
/// skipped, and the memory list's own range survives beside them.
#[test]
fn memory64_based_past_the_files_end_is_skipped() {
    let mut d = dump();
    add_stream(&mut d, 9, &memory64(0x1000_0000, &[(0x3000_0000, 0x10)]));
    let p = Program::from_bytes("b64.dmp".into(), d).expect("loads");
    assert!(p.section_at(0x3000_0000).is_none());
    assert!(p.section_at(0x7ff0_0000).is_some());
}

/// Memory64 sizes that overflow the running file cursor saturate it: the
/// first range is clamped to what the file holds and the one the cursor
/// overflows onto reads nothing, without a wrap.
#[test]
fn memory64_sizes_that_overflow_the_cursor_saturate() {
    let mut d = dump();
    add_stream(
        &mut d,
        9,
        &memory64(0x3a0, &[(0x3000_0000, u64::MAX), (0x4000_0000, 0x10)]),
    );
    let len = d.len();
    let p = Program::from_bytes("o64.dmp".into(), d).expect("loads");
    assert_eq!(p.sections.len(), 2);
    let huge = p.section_at(0x3000_0000).expect("clamped");
    assert_eq!(huge.file_size, u64::try_from(len - 0x3a0).unwrap());
    assert!(p.read_va_upto(0x3000_0000, 4).is_some());
    assert!(p.read_va_upto(0x3000_0000 + huge.file_size, 4).is_none());
    assert!(p.read_va_upto(0x4000_0000, 4).is_none());
}

/// Memory64 ranges may overlap the memory list's: both stay sections
/// (the coverage rule folds stacks only), and each address reads.
#[test]
fn memory64_ranges_may_overlap_the_memory_list() {
    let mut d = dump();
    add_stream(&mut d, 9, &memory64(0x390, &[(0x7ff0_0010, 0x20)]));
    let p = Program::from_bytes("ovl.dmp".into(), d).expect("loads");
    assert_eq!(p.sections.len(), 2);
    assert!(p.read_va_upto(0x7ff0_0000, 4).is_some());
    assert!(p.read_va_upto(0x7ff0_0020, 4).is_some());
}

/// A memory64 range mapped low with a size near the whole address space
/// answers at its start and refuses cleanly at the top: the file offset
/// an address that high would map to cannot exist.
#[test]
fn a_read_far_above_a_low_range_refuses_cleanly() {
    let mut d = dump();
    u32_at(&mut d, 0x80, 0); // the memory list names nothing
    add_stream(&mut d, 9, &memory64(0x380, &[(0x10, u64::MAX - 0x20)]));
    let p = Program::from_bytes("low.dmp".into(), d).expect("loads");
    assert_eq!(p.read_va_upto(0x10, 1).and_then(|b| b.first()), Some(&0xc3));
    let top = u64::MAX - 0x100;
    assert!(p.section_at(top).is_some());
    assert!(p.read_va_upto(top, 4).is_none());
    assert!(p.read_va(top, 1).is_none());
    assert!(p.va_to_offset(top).is_none());
}

// ---- threads ----

/// A thread stack a listed range already covers is not added again.
#[test]
fn a_covered_thread_stack_is_not_added_again() {
    let mut d = dump();
    add_stream(&mut d, 3, &threads(&[(0x7ff0_0000, 0x10, 0x390)]));
    let p = Program::from_bytes("cov.dmp".into(), d).expect("loads");
    assert_eq!(p.sections.len(), 1);
}

/// A thread stack no listed range covers becomes a section that reads
/// the bytes its descriptor names.
#[test]
fn an_uncovered_thread_stack_becomes_a_section() {
    let mut d = dump();
    d[0x3f0] = 0x90;
    add_stream(&mut d, 3, &threads(&[(0x2000_0000, 8, 0x3f0)]));
    let p = Program::from_bytes("stk.dmp".into(), d).expect("loads");
    assert_eq!(p.sections.len(), 2);
    assert_eq!(p.read_va_upto(0x2000_0000, 1), Some(&[0x90][..]));
}

/// A thread list of zero threads changes nothing.
#[test]
fn no_threads_changes_nothing() {
    let mut d = dump();
    add_stream(&mut d, 3, &threads(&[]));
    let p = Program::from_bytes("t0.dmp".into(), d).expect("loads");
    assert_eq!(p.sections.len(), 1);
}

/// A stack under a range whose end overflows is covered: the range's
/// span saturates instead of wrapping past it.
#[test]
fn a_stack_under_a_range_whose_end_overflows_is_covered() {
    let mut d = dump();
    add_stream(&mut d, 9, &memory64(0x3a0, &[(0x1000, u64::MAX - 0x800)]));
    add_stream(&mut d, 3, &threads(&[(0x2000_0000, 0x10, 0x3f0)]));
    let p = Program::from_bytes("sat.dmp".into(), d).expect("loads");
    assert_eq!(p.sections.len(), 2);
}

// ---- modules ----

/// A module name RVA pointing at garbage (the memory's 0xc3 read as a
/// byte length) keeps the module with an empty name.
#[test]
fn a_module_named_by_garbage_keeps_an_empty_name() {
    let mut d = dump();
    u32_at(&mut d, 0xb8, 0x380);
    let p = Program::from_bytes("gname.dmp".into(), d).expect("loads");
    assert_eq!(p.symbols.len(), 1);
    assert_eq!(p.symbols[0].name, "");
    assert_eq!(p.symbols[0].addr, 0x1_4000_0000);
}

/// A name of one lone surrogate decodes lossily to the replacement
/// character rather than failing the module.
#[test]
fn a_lone_surrogate_name_decodes_lossily() {
    let mut d = dump();
    u32_at(&mut d, 0x118, 2);
    u16_at(&mut d, 0x11c, 0xd800);
    let p = Program::from_bytes("sur.dmp".into(), d).expect("loads");
    assert_eq!(p.symbols.len(), 1);
    assert_eq!(p.symbols[0].name, "\u{fffd}");
}

/// Name lengths that are odd or past the 0x1000 cap are refused: the
/// module keeps an empty name.
#[test]
fn odd_or_oversized_name_lengths_are_refused() {
    for len in [7u32, 0x2002] {
        let mut d = dump();
        u32_at(&mut d, 0x118, len);
        let p = Program::from_bytes("nlen.dmp".into(), d).expect("loads");
        assert_eq!(p.symbols[0].name, "", "length {len}");
    }
}

/// A module based at zero names no symbol and leaves the image base at
/// zero: nothing about the row is a fact worth keeping.
#[test]
fn a_module_at_zero_names_no_symbol_and_no_base() {
    let mut d = dump();
    u64_at(&mut d, 0xa4, 0);
    let p = Program::from_bytes("m0.dmp".into(), d).expect("loads");
    assert!(p.symbols.is_empty());
    assert_eq!(p.image_base, 0);
}

// ---- system info and the exception ----

/// Each architecture the system-info stream can state maps, and one it
/// cannot maps to [`Arch::Unknown`].
#[test]
fn each_stated_architecture_maps() {
    for (code, arch, machine) in [
        (0u16, Arch::X86, "x86"),
        (9, Arch::X86_64, "x86-64"),
        (12, Arch::Arm64, "arm64"),
        (0x99, Arch::Unknown, "unknown"),
    ] {
        let mut d = dump();
        u16_at(&mut d, 0xd0, code);
        let p = Program::from_bytes("arch.dmp".into(), d).expect("loads");
        assert_eq!(p.arch, arch, "code {code}");
        assert_eq!(p.headers.machine.as_deref(), Some(machine));
    }
}

/// An exception context whose RVA sits past the end of the file leaves
/// the program with no entry.
#[test]
fn a_context_past_the_files_end_leaves_no_entry() {
    let mut d = dump();
    u32_at(&mut d, 0x1a4, 0x1000);
    let p = Program::from_bytes("ctx.dmp".into(), d).expect("loads");
    assert_eq!(p.entry, None);
}

/// An exception context too small to hold the architecture's stop
/// register leaves no entry: it states nothing readable.
#[test]
fn a_context_too_small_for_rip_leaves_no_entry() {
    let mut d = dump();
    u32_at(&mut d, 0x1a0, 0x10);
    let p = Program::from_bytes("small.dmp".into(), d).expect("loads");
    assert_eq!(p.entry, None);
}

/// An arm64 dump carries no entry: the exception context's layout is
/// architecture-specific and only the x86 ones are read.
#[test]
fn an_arm64_dump_has_no_entry() {
    let mut d = dump();
    u16_at(&mut d, 0xd0, 12);
    let p = Program::from_bytes("arm.dmp".into(), d).expect("loads");
    assert_eq!(p.arch, Arch::Arm64);
    assert!(p.is_64);
    assert_eq!(p.entry, None);
}

// ---- memory info ----

/// The protections the memory-info stream states set each section's
/// writable and executable flags, and a range it states nothing about
/// stays readable, writable and executable.
#[test]
fn memory_info_protections_set_the_section_flags() {
    let mut d = dump();
    let one = [0u8; 0x10];
    set_memory(
        &mut d,
        &[
            (0x1000, &one),
            (0x2000, &one),
            (0x3000, &one),
            (0x4000, &one),
            (0x5000, &one),
        ],
    );
    add_stream(
        &mut d,
        16,
        &memory_info(
            48,
            &[
                (0x1000, 0x10, 0x04),
                (0x2000, 0x10, 0x10),
                (0x3000, 0x10, 0x20),
                (0x4000, 0x10, 0x40),
            ],
        ),
    );
    let p = Program::from_bytes("prot.dmp".into(), d).expect("loads");
    let flags = |va: u64| p.section_at(va).map(|s| (s.writable, s.executable));
    assert_eq!(flags(0x1000), Some((true, false)), "readwrite");
    assert_eq!(flags(0x2000), Some((false, true)), "execute");
    assert_eq!(flags(0x3000), Some((false, true)), "execute-read");
    assert_eq!(flags(0x4000), Some((true, true)), "execute-readwrite");
    assert_eq!(flags(0x5000), Some((true, true)), "stated nowhere");
}

/// A memory-info entry size of zero or past 64 is unusable: the stream
/// states nothing and every range keeps the default snapshot flags.
#[test]
fn an_unusable_memory_info_entry_size_leaves_the_default() {
    for entry in [0u32, 80] {
        let mut d = dump();
        add_stream(
            &mut d,
            16,
            &memory_info(entry, &[(0x7ff0_0000, 0x20, 0x04)]),
        );
        let p = Program::from_bytes("esz.dmp".into(), d).expect("loads");
        let s = p.section_at(0x7ff0_0000).expect("mapped");
        assert!(s.writable && s.executable, "entry size {entry}");
    }
}

// ---- the mutation sweep ----

/// Five hundred seeded mutations of the valid dump never panic.
///
/// Each mutation flips one random byte or cuts the file at a random
/// offset; every outcome is a program or an error, and a program that
/// loads keeps every section inside the file.
#[test]
fn five_hundred_mutations_never_panic() {
    let mut rng = SplitMix64(0x5eed_0d15_5eed_0d15);
    let len = u64::try_from(dump().len()).unwrap();
    for _ in 0..500 {
        let mut d = dump();
        if rng.next() & 1 == 0 {
            let at = usize::try_from(rng.next() % len).unwrap();
            let bit = u8::try_from(rng.next() % 8).unwrap();
            d[at] ^= 1 << bit;
        } else {
            let cut = usize::try_from(rng.next() % (len + 1)).unwrap();
            d.truncate(cut);
        }
        if let Ok(p) = Program::from_bytes("mutation.dmp".into(), d) {
            assert!(sections_sit_in_the_file(&p));
        }
    }
}

// ---- elf cores ----

/// An ELF core maps its `PT_LOAD` segments as the memory they hold.
#[test]
fn an_elf_core_loads_its_load_segments() {
    let p = Program::from_bytes("core.elf".into(), elf_core()).expect("loads");
    assert_eq!(p.arch, Arch::X86_64);
    let read = p.read_va_upto(0x7ff0_0000, 4).expect("mapped");
    assert_eq!(read.first(), Some(&0xc3));
}

/// Program headers a core cannot hold - a count of 0xffff, or a table
/// past the end of the file - refuse the load or map only what fits,
/// never panicking.
#[test]
fn core_phdrs_the_file_cannot_hold_are_refused_or_bounded() {
    let mutators: [fn(&mut Vec<u8>); 2] = [
        |e| u16_at(e, 56, 0xffff),   // e_phnum
        |e| u64_at(e, 32, 0x1_0000), // e_phoff past the end
    ];
    for mutate in mutators {
        let mut e = elf_core();
        mutate(&mut e);
        if let Ok(p) = Program::from_bytes("core.elf".into(), e) {
            assert!(sections_sit_in_the_file(&p));
        }
    }
}

/// A core segment longer than the file's remainder is clamped to it: the
/// section reads what the file holds and nothing past it.
#[test]
fn a_core_segment_longer_than_the_file_is_clamped() {
    let mut e = elf_core();
    u64_at(&mut e, 0x60, 0x100); // p_filesz from 0x80 in a 0x120 file
    let p = Program::from_bytes("core.elf".into(), e).expect("loads");
    let s = p.section_at(0x7ff0_0000).expect("mapped");
    assert_eq!(s.file_size, 0x120 - 0x80);
    assert_eq!(
        p.read_va_upto(0x7ff0_0000, 0x200).map(<[u8]>::len),
        Some(0x120 - 0x80)
    );
}

/// A core segment whose vaddr plus size overflows is refused: the row is
/// dropped, counted as such, and the rest of the core still loads.
#[test]
fn a_core_segment_whose_end_overflows_is_refused() {
    let mut e = elf_core();
    u64_at(&mut e, 0x50, u64::MAX - 8); // p_vaddr + memsz 0x10 overflows
    let p = Program::from_bytes("core.elf".into(), e).expect("loads");
    assert!(p.sections.is_empty());
    assert_eq!(p.headers.dropped_sections, 1);
}
