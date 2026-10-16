//! Engine unit tests: disassembly, strings, entropy, hexdump, program
//! loading, bounded reads, typed reads and the crypto scan. Part of the
//! phase -1 termination test (`cargo test`).

#![expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]

use borer_engine::{disasm, entropy, hexdump, strings};

/// `b8 01 00 00 00; c3` decodes as `mov eax,1; ret` with the right lengths and addresses.
#[test]
fn disassemble_known_bytes() {
    let code: &[u8] = &[0xb8, 0x01, 0x00, 0x00, 0x00, 0xc3];
    let lines = disasm::disassemble(code, 0x1000, 64, 16);
    assert_eq!(lines.len(), 2);
    assert!(lines[0].text.contains("mov") && lines[0].text.contains("eax"));
    assert_eq!(lines[0].bytes.len(), 5);
    assert_eq!(lines[1].text.trim(), "ret");
    assert_eq!(lines[1].va, 0x1005);
}

/// A nop sled stops at the requested instruction count.
#[test]
fn disassemble_respects_max_instrs() {
    let code: &[u8] = &[0x90; 32];
    let lines = disasm::disassemble(code, 0x2000, 64, 3);
    assert_eq!(lines.len(), 3);
    assert!(lines.iter().all(|l| l.text.trim() == "nop"));
}

/// `jmp $` (`eb fe`) renders as a jump.
#[test]
fn disassemble_relative_jump_renders_target() {
    let lines = disasm::disassemble(&[0xeb, 0xfe], 0x3000, 64, 4);
    assert!(lines[0].text.starts_with("jmp"));
}

/// A run of `0xff` bytes decodes invalid somewhere; the sweep continues and
/// every line has text.
#[test]
fn disassemble_invalid_bytes_do_not_stop_the_sweep() {
    let code: &[u8] = &[0xff; 64];
    let lines = disasm::disassemble(code, 0, 64, 64);
    assert!(!lines.is_empty());
    assert!(lines.iter().all(|l| !l.text.is_empty()));
}

/// A NUL-terminated ASCII run is found with its offset, text and length.
#[test]
fn finds_strings() {
    let bytes = b"\x00\x00Hello, borer!\x00\x01";
    let hits = strings::find_strings(bytes, 5);
    assert_eq!(hits.len(), 1);
    assert_eq!(hits[0].off, 2);
    assert_eq!(hits[0].text, "Hello, borer!");
    assert_eq!(hits[0].len, 13);
}

/// Runs shorter than the minimum length are skipped.
#[test]
fn strings_respect_min_len() {
    let bytes = b"abc\x00abcdef\x00";
    let hits = strings::find_strings(bytes, 5);
    assert_eq!(hits.len(), 1);
    assert_eq!(hits[0].text, "abcdef");
}

/// A UTF-16LE run is found with its text, offset and code-unit length.
#[test]
fn finds_wide_strings() {
    let bytes = b"\x00\x00a\x00d\x00v\x00a\x00p\x00i\x00\x00\x00";
    let hits = strings::find_wide_strings(bytes, 5);
    assert_eq!(hits.len(), 1);
    assert_eq!(hits[0].off, 2);
    assert_eq!(hits[0].text, "advapi");
    assert_eq!(hits[0].len, 6);
}

/// A UTF-16LE run abutting an ASCII string does not swallow that string's
/// last character.
///
/// `"rand_s\0"` followed by `L"advapi"` puts a printable byte and a NUL in
/// front of the wide run, which reads as one more code unit and yields
/// `L"sadvapi"`, a DLL name that is not in the data. The run must start
/// after the ASCII terminator.
#[test]
fn wide_strings_do_not_start_on_an_ascii_tail() {
    let bytes = b"rand_s\x00a\x00d\x00v\x00a\x00p\x00i\x00\x00\x00";
    let hits = strings::find_wide_strings(bytes, 5);
    assert_eq!(hits.len(), 1);
    assert_eq!(hits[0].text, "advapi");
    assert_eq!(hits[0].off, 7);
}

/// A long string's display text is cut, and its whole text still holds
/// what lies past the cut, in either encoding: a filter tested against the
/// cut text missed it.
#[test]
fn a_long_string_keeps_its_whole_text_past_the_display_cut() {
    let mut long = vec![b'a'; 300];
    long.extend_from_slice(b"needle\0");
    let ascii = strings::find_strings(&long, 5);
    assert_eq!(ascii.len(), 1);
    assert!(!ascii[0].text.contains("needle"), "{}", ascii[0].text);
    assert!(ascii[0].full_text(&long).ends_with("needle"));
    let wide: Vec<u8> = long.iter().flat_map(|b| [*b, 0]).collect();
    let utf16 = strings::find_wide_strings(&wide, 5);
    assert_eq!(utf16.len(), 1);
    assert!(utf16[0].full_text(&wide).ends_with("needle"));
    let short = strings::find_strings(b"\0short\0", 5);
    assert_eq!(short[0].full_text(b"\0short\0"), "short");
}

/// Both walks answer what a per-byte state machine answers.
///
/// The data stresses them: runs planted across the eight-byte word
/// boundaries and at the buffer's ends, ASCII tails before wide runs
/// (trimmed by a unit), a wide run straddling word boundaries in both
/// phases, and pseudo-random filler between them.
///
/// # Panics
///
/// When a walk disagrees with the reference walk at any minimum length.
#[test]
fn walks_match_the_per_byte_state_machines() {
    /// Size of the pseudo-random buffer the runs are planted into.
    const LEN: usize = 0x3000;
    let mut x = 0x2545_F491_u32;
    let mut bytes: Vec<u8> = Vec::with_capacity(LEN);
    for _ in 0..LEN {
        x ^= x << 13;
        x ^= x >> 17;
        x ^= x << 5;
        bytes.push(borer_engine::num::lo8(u64::from(x)));
    }
    for at in [0, 1, 7, 8, 15, 16, 31, 32, LEN / 2, LEN - 9, LEN - 6] {
        bytes[at..at + 6].copy_from_slice(b"Tail;!");
    }
    for (at, tail) in [(40usize, true), (LEN / 2 + 7, true), (LEN / 2 + 13, false)] {
        let mut p = at;
        if tail {
            bytes[p..p + 4].copy_from_slice(b"abc\x00");
            p += 4;
        }
        for b in b"wide run" {
            bytes[p] = *b;
            bytes[p + 1] = 0;
            p += 2;
        }
    }
    let ascii_ref = |min_len: usize| -> Vec<(u64, usize, String)> {
        let mut hits: Vec<(u64, usize, String)> = Vec::new();
        let mut start: Option<usize> = None;
        for (i, &b) in bytes.iter().enumerate() {
            match (start, strings::printable(b)) {
                (None, true) => start = Some(i),
                (Some(s), false) => {
                    if i - s >= min_len {
                        let text = String::from_utf8_lossy(&bytes[s..i]).to_string();
                        hits.push((s as u64, i - s, text));
                    }
                    start = None;
                }
                (None, false) | (Some(_), true) => {}
            }
        }
        if let Some(s) = start
            && bytes.len() - s >= min_len
        {
            let text = String::from_utf8_lossy(&bytes[s..]).to_string();
            hits.push((s as u64, bytes.len() - s, text));
        }
        hits
    };
    let wide_ref = |min_len: usize| -> Vec<(u64, usize, String)> {
        let mut hits: Vec<(u64, usize, String)> = Vec::new();
        let mut i = 0;
        while i + 1 < bytes.len() {
            let unit = strings::printable(bytes[i]) && bytes[i + 1] == 0;
            let tail = i > 0 && strings::printable(bytes[i - 1]);
            if !unit || tail {
                i += 1;
                continue;
            }
            let start = i;
            while i + 1 < bytes.len() && strings::printable(bytes[i]) && bytes[i + 1] == 0 {
                i += 2;
            }
            let len = (i - start) / 2;
            if len >= min_len {
                let raw: Vec<u8> = bytes[start..i].iter().step_by(2).copied().collect();
                hits.push((start as u64, len, String::from_utf8_lossy(&raw).to_string()));
            }
        }
        hits
    };
    for min_len in 1..10 {
        let got: Vec<(u64, usize, String)> = strings::find_strings(&bytes, min_len)
            .iter()
            .map(|h| (h.off, h.len, h.text.clone()))
            .collect();
        let want = ascii_ref(min_len);
        assert_eq!(got, want, "ascii min {min_len}");
        let got: Vec<(u64, usize, String)> = strings::find_wide_strings(&bytes, min_len)
            .iter()
            .map(|h| (h.off, h.len, h.text.clone()))
            .collect();
        let want = wide_ref(min_len);
        assert_eq!(got, want, "utf16 min {min_len}");
    }
}

/// A `/NN` section name that stayed unresolved is called out, not passed off
/// as a name.
///
/// PE names over eight bytes are a COFF string-table offset. A rebuilt image
/// can carry the sections while the table is gone, and `/19` then reads like
/// a real section rather than the offset it is; on one such binary nine
/// DWARF sections showed up that way.
#[test]
fn unresolved_section_names_are_noted() {
    let h = borer_engine::headers::Headers {
        unresolved_section_names: 9,
        ..borer_engine::headers::Headers::default()
    };
    let out = h.render();
    assert!(out.contains("9 section names unresolved"), "{out}");
    assert!(
        borer_engine::headers::Headers::default()
            .render()
            .is_empty()
    );
}

/// Shannon entropy is near 0 for constant data and near 8 for a uniform byte cycle.
#[test]
fn entropy_bounds() {
    assert!(entropy::shannon(&[0u8; 1024]) < 0.001);
    let seq: Vec<u8> = (0..=255u8).cycle().take(4096).collect();
    assert!(entropy::shannon(&seq) > 7.9);
}

/// The hexdump shows hex bytes, the ASCII gutter, and a 12-wide `0x` address column.
#[test]
fn hexdump_renders() {
    let s = hexdump::hexdump(b"Hello, borer!", 0x1000);
    assert!(s.contains("48 65 6c 6c 6f"));
    assert!(s.contains("|Hello, borer!|"));
    assert!(s.contains("0x0000001000"));
}

/// The test binary itself is a real PE and parses end to end.
///
/// Its entry maps into a section, the exception table yields function
/// ranges, the header facts name the mitigations and the PDB, and the
/// summary renders them. It loads without the companion PDB, because the
/// assertion that the exception table's count is the range count states
/// that one source exactly; an applied PDB's procedure extents join the
/// ranges on top of it.
#[cfg(windows)]
#[test]
fn parses_own_pe() {
    use borer_engine::program::{BinaryFormat, Program};
    let exe = std::env::current_exe().unwrap();
    let p = Program::load_with(&exe, false).unwrap();
    assert_eq!(p.format, BinaryFormat::Pe);
    assert!(!p.sections.is_empty());
    let entry = p.entry.expect("PE must have an entry point");
    assert!(
        p.va_to_offset(entry).is_some(),
        "entry {entry:#x} must map into a section; sections: {}",
        p.section_list()
    );
    assert!(!p.function_ranges.is_empty(), "no .pdata function ranges");
    assert!(
        p.function_ranges.windows(2).all(|w| w[0] < w[1]),
        "ranges not sorted"
    );
    assert_eq!(p.headers.kind, Some("exe"));
    assert_eq!(p.headers.subsystem, Some("console"));
    assert!(p.headers.mitigations.contains(&"dep"), "{:?}", p.headers);
    assert!(p.headers.mitigations.contains(&"aslr"), "{:?}", p.headers);
    assert!(
        p.headers
            .debug_id
            .as_deref()
            .is_some_and(|d| d.contains(".pdb")),
        "{:?}",
        p.headers.debug_id
    );
    assert_eq!(p.headers.unwind_functions, p.function_ranges.len());
    let s = p.summary();
    assert!(s.contains("format:  PE"));
    assert!(s.contains("entry"));
    assert!(s.contains("mitigations: "), "{s}");
    assert!(s.contains("libraries ("), "{s}");
}

/// Builds a raw x86-64 program with `.text` at 0x1000 and `.data` at 0x2000.
///
/// `.data` has a 0x100-byte zero-filled tail beyond its file bytes.
///
/// # Arguments
///
/// * `text` - Bytes of `.text`.
/// * `data` - File-backed bytes of `.data`.
fn two_section_program(text: Vec<u8>, data: Vec<u8>) -> borer_engine::program::Program {
    use borer_engine::program::{Arch, Program, Section};
    let text_len = text.len() as u64;
    let data_len = data.len() as u64;
    let mut bytes = text;
    bytes.extend(data);
    Program::raw(
        bytes,
        Arch::X86_64,
        0,
        Some(0x1000),
        vec![
            Section::mapped(".text", 0x1000, 0, text_len, false, true),
            Section {
                vsize: data_len + 0x100,
                ..Section::mapped(".data", 0x2000, text_len, data_len, true, false)
            },
        ],
    )
}

/// The mapped headers are readable, because they are mapped.
///
/// A PE's headers sit at the image base, one to one with the start of the
/// file, and they are not a section. Every reader that goes through the
/// section table therefore refused the one address a binary is most often
/// opened at - its `MZ` - while the live reader answered it, so the same
/// question had two answers depending on which side of the tool asked.
#[test]
fn the_mapped_headers_are_readable_at_the_image_base() {
    let p = pe_with_headers();
    assert_eq!(p.read_va(0x400000, 2), Some(&b"MZ"[..]));
    assert_eq!(
        p.read_va_upto(0x400000, 4096).map(<[u8]>::len),
        Some(0x400),
        "a bounded read of the headers stops where they end"
    );
}

/// A read that would leave the headers is refused, as a read leaving a
/// section is: the bytes after them belong to whatever the file put there.
#[test]
fn a_read_past_the_headers_is_refused() {
    let p = pe_with_headers();
    assert!(
        p.read_va(0x4003f0, 0x20).is_none(),
        "read ran past the headers"
    );
    assert!(
        p.read_va(0x300000, 1).is_none(),
        "read below the image base"
    );
    assert!(
        p.read_va(0x400400, 1).is_none(),
        "the gap between the headers and the first section is not mapped"
    );
}

/// A PE whose headers are mapped at the base, the layout a linker writes.
fn pe_with_headers() -> borer_engine::program::Program {
    use borer_engine::program::{Arch, BinaryFormat, Program, Section};
    let mut bytes = vec![0u8; 0x400];
    bytes[0] = b'M';
    bytes[1] = b'Z';
    bytes.extend_from_slice(&[0x90; 16]);
    let mut p = Program::raw(
        bytes,
        Arch::X86_64,
        0x400000,
        Some(0x401000),
        vec![Section::mapped(".text", 0x401000, 0x400, 16, false, true)],
    );
    p.path = std::path::PathBuf::from("hdr.exe");
    p.format = BinaryFormat::Pe;
    p
}

/// Exact reads refuse to spill into the next section or into a section's
/// zero-filled tail; bounded reads stop at the file extent.
#[test]
fn reads_never_cross_a_section_file_extent() {
    let p = two_section_program(vec![0x90; 16], vec![0x41; 8]);
    assert!(p.read_va(0x100c, 4).is_some());
    assert!(
        p.read_va(0x100c, 8).is_none(),
        "read crossed into the next section"
    );
    assert!(p.read_va(0x2008, 1).is_none());
    assert_eq!(p.read_va_upto(0x2004, 100).map(<[u8]>::len), Some(4));
}

/// Typed reads render integers, pointers (with their target), C strings and
/// floats; unmapped addresses fail; kind aliases parse.
#[test]
fn typed_reads() {
    use borer_engine::memory::{Kind, read_values};
    let mut data = Vec::new();
    data.extend_from_slice(&0x1122_3344_5566_7788u64.to_le_bytes());
    data.extend_from_slice(&0x1000u64.to_le_bytes());
    data.extend_from_slice(b"hi there\0");
    data.extend_from_slice(&1.5f32.to_le_bytes());
    let p = two_section_program(vec![0x90; 16], data);
    let v = read_values(&p, 0x2000, Kind::U64, 1).unwrap();
    assert_eq!(v[0].text, "0x1122334455667788");
    let v = read_values(&p, 0x2000, Kind::U8, 3).unwrap();
    assert_eq!(v.len(), 3);
    assert_eq!(v[2].at, 0x2002);
    let v = read_values(&p, 0x2008, Kind::Ptr, 1).unwrap();
    assert_eq!(v[0].target, Some(0x1000));
    let v = read_values(&p, 0x2010, Kind::CStr, 1).unwrap();
    assert_eq!(v[0].text, "\"hi there\" (len 8)");
    let v = read_values(&p, 0x2019, Kind::F32, 1).unwrap();
    assert_eq!(v[0].text, "1.5");
    assert!(read_values(&p, 0x9000, Kind::U8, 1).is_err());
    assert_eq!(Kind::parse("dword"), Some(Kind::U32));
    assert_eq!(Kind::parse("nonsense"), None);
}

/// Bytes no section maps are read by file offset.
///
/// A whole file with no sections and a PE's headers alike. A read by
/// address there is refused with the offset form that reads it, which
/// `off:` and `off=` spell.
#[test]
fn bytes_no_section_maps_are_read_by_offset() {
    use borer_engine::analysis::parse_off;
    use borer_engine::memory::{Kind, read_values, read_values_at_offset};
    use borer_engine::program::{Arch, Program};
    let mut bytes = b"QklFMQ\0".to_vec();
    bytes.extend_from_slice(&0x1122_3344u32.to_le_bytes());
    let raw = Program::raw(bytes, Arch::Unknown, 0, None, Vec::new());
    assert_eq!(raw.unmapped(), [(0, raw.bytes.as_slice())]);

    let v = read_values_at_offset(&raw, 0, Kind::CStr, 1).unwrap();
    assert_eq!((v[0].at, v[0].text.as_str()), (0, "\"QklFMQ\" (len 6)"));
    let v = read_values_at_offset(&raw, 7, Kind::U32, 2).unwrap();
    assert_eq!(v.len(), 1, "the second value runs past the end of the file");
    assert_eq!((v[0].at, v[0].text.as_str()), (7, "0x11223344"));
    let err = read_values_at_offset(&raw, 11, Kind::U8, 1).unwrap_err();
    assert!(err.starts_with("file offset 0xb is past the end"), "{err}");

    let err = read_values(&raw, 0, Kind::U8, 1).unwrap_err();
    assert!(
        err.contains("sections: none; the file's bytes are read by file offset, as off:0x0"),
        "{err}"
    );
    let dump = hexdump::file_hexdump(&raw, 0, 64).unwrap();
    assert!(
        dump.starts_with(
            "# off 0x0..0xb, rows by file offset; no section maps it
"
        ),
        "{dump}"
    );
    assert!(dump.contains("|QklFMQ."), "{dump}");

    let pe = pe_with_headers();
    assert_eq!(pe.unmapped().len(), 1, "the headers, before .text");
    assert_eq!(pe.unmapped()[0].0, 0);
    let v = read_values_at_offset(&pe, 0, Kind::U16, 1).unwrap();
    assert_eq!(v[0].text, "0x5a4d");
    assert!(
        hexdump::file_hexdump(&pe, 0x400, 4)
            .unwrap()
            .contains("it loads at 0x401000")
    );

    assert_eq!(parse_off("off:0x30"), Some(0x30));
    assert_eq!(parse_off("off=48"), Some(48));
    assert_eq!(parse_off("0x30"), None);
}

/// The AES S-box prefix and the ChaCha constant are found at their addresses;
/// clean data yields no hits.
#[test]
fn crypto_constant_scan() {
    use borer_engine::crypto::{find_crypto_constants, render};
    let sbox: Vec<u8> = vec![
        0x63, 0x7c, 0x77, 0x7b, 0xf2, 0x6b, 0x6f, 0xc5, 0x30, 0x01, 0x67, 0x2b, 0xfe, 0xd7, 0xab,
        0x76,
    ];
    let mut data = vec![0u8; 8];
    data.extend(&sbox);
    data.extend(b"expand 32-byte k");
    let p = two_section_program(vec![0x90; 16], data);
    let hits = find_crypto_constants(&p);
    let names: Vec<&str> = hits.iter().map(|h| h.name).collect();
    assert!(names.contains(&"AES forward S-box"), "{names:?}");
    assert!(
        names.iter().any(|n| n.starts_with("ChaCha20 / Salsa20")),
        "{names:?}"
    );
    assert_eq!(hits[0].va, Some(0x2008));
    assert!(render(&hits).starts_with("# 2 crypto/hash constant hits"));
    assert!(find_crypto_constants(&two_section_program(vec![0x90; 16], vec![0; 64])).is_empty());
}

/// Where two runs of one function part ways: the comparison that split
/// them, the callees each side then visits, and what each returned.
///
/// `f` at 0x1000 is `cmp ecx,5; jge H; call G; ret; H: call H2; ret`, G
/// at 0x1011 `lea eax,[rcx+1]; ret` and H2 at 0x1015 `lea eax,[rcx+2];
/// ret`, so input 1 takes G and input 9 H2.
#[test]
fn a_diff_names_the_branch_and_each_sides_calls() {
    use borer_engine::analysis::{Analysis, Overlay, render::run_diff_tsv};
    let code: Vec<u8> = [
        &[0x83, 0xf9, 0x05][..],
        &[0x7d, 0x06],
        &[0xe8, 0x07, 0x00, 0x00, 0x00],
        &[0xc3],
        &[0xe8, 0x05, 0x00, 0x00, 0x00],
        &[0xc3],
        &[0x8d, 0x41, 0x01, 0xc3],
        &[0x8d, 0x41, 0x02, 0xc3],
    ]
    .concat();
    let p = two_section_program(code, vec![0; 8]);
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let out = run_diff_tsv(&p, &a, &o, "0x1000/1;9").expect("a diff");
    assert!(
        out.contains("# first divergence: step 3 at 0x1005 in sub_1000 vs 0x100b in sub_1000"),
        "{out}"
    );
    assert!(out.contains("# input 1 then called: sub_1011"), "{out}");
    assert!(out.contains("# input 2 then called: sub_1015"), "{out}");
    assert!(
        out.contains("returned 0x2") && out.contains("returned 0xb"),
        "{out}"
    );
    let agree = run_diff_tsv(&p, &a, &o, "0x1000/1;1").expect("a diff");
    assert!(
        agree.contains("# the runs agree on every traced step"),
        "{agree}"
    );
    let refused = run_diff_tsv(&p, &a, &o, "0x1000/1;2;3").expect_err("three inputs");
    assert!(refused.contains("two inputs"), "{refused}");
}

/// The same table stored the other way round, xored with a constant and
/// added one, is named with what was done to it; the plain form reports
/// once and no delta form doubles it.
#[test]
fn crypto_constant_storage_variants() {
    use borer_engine::crypto::{Storage, find_crypto_constants};
    let k: Vec<u8> = vec![
        0x98, 0x2f, 0x8a, 0x42, 0x91, 0x44, 0x37, 0x71, 0xcf, 0xfb, 0xc0, 0xb5, 0xa5, 0xdb, 0xb5,
        0xe9,
    ];
    let forms: [(Vec<u8>, Storage); 4] = [
        (k.clone(), Storage::Native),
        (
            k.chunks(4).flat_map(|c| c.iter().rev().copied()).collect(),
            Storage::Swapped,
        ),
        (k.iter().map(|b| b ^ 0x5a).collect(), Storage::Xored(0x5a)),
        (
            k.iter().map(|b| b.wrapping_add(0x11)).collect(),
            Storage::Added(0x11),
        ),
    ];
    for (stored, storage) in &forms {
        let mut data = vec![0u8; 8];
        data.extend(stored);
        let p = two_section_program(vec![0x90; 16], data);
        let hits = find_crypto_constants(&p);
        assert_eq!(hits.len(), 1, "{storage}: {hits:?}");
        assert_eq!(hits[0].name, "SHA-256 K constants", "{storage}: {hits:?}");
        assert_eq!(&hits[0].storage, storage, "{hits:?}");
    }
}

/// A constant in bytes no section maps is found by its file offset, as
/// `search` finds it: a table appended after the last section was missed.
#[test]
fn crypto_constants_past_the_sections_are_found() {
    use borer_engine::crypto::{UNMAPPED, find_crypto_constants, rows};
    let mut p = two_section_program(vec![0x90; 16], vec![0; 16]);
    p.bytes.extend_from_slice(b"\0\0\0\0expand 32-byte k");
    let hits = find_crypto_constants(&p);
    assert_eq!(hits.len(), 1, "{hits:?}");
    assert_eq!((hits[0].va, hits[0].file_off), (None, 0x24));
    assert_eq!(hits[0].section, UNMAPPED);
    assert!(rows(&hits).contains("off=0x24"), "{}", rows(&hits));
}

/// The per-site rows of the crypto table page, under a `showing N of M`
/// header, while the groups count every hit.
#[test]
fn the_crypto_table_pages_its_rows() {
    use borer_engine::analysis::{Analysis, Overlay, render::crypto_tsv};
    let data: Vec<u8> = b"expand 32-byte k".repeat(3);
    let p = two_section_program(vec![0x90; 16], data);
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let first = crypto_tsv(&p, &a, &o, 0, 2);
    assert!(
        first.starts_with("# 3 crypto/hash constant hits"),
        "{first}"
    );
    assert!(first.contains("# showing 2 of 3 hits from 0\n"), "{first}");
    assert!(
        first.contains("# 1 more hits; offset=2 for the next page"),
        "{first}"
    );
    let last = crypto_tsv(&p, &a, &o, 2, 2);
    assert!(last.contains("# showing 1 of 3 hits from 2\n"), "{last}");
    assert!(last.contains("0x2020"), "{last}");
    assert!(!last.contains("more hits"), "{last}");
}

/// A PE whose exception directory points nowhere still loads.
///
/// A protector rewrites the data directories so a strict parse of the
/// exception table fails on a file that still runs. The loader retries such a
/// PE permissively; here the test binary's own exception-table RVA is set out
/// of range, the strict goblin parse is confirmed to reject it, and the
/// permissive path is confirmed to load it with its sections and entry.
#[cfg(windows)]
#[test]
fn a_pe_with_a_broken_exception_directory_still_loads() {
    use borer_engine::program::{BinaryFormat, Program};
    let exe = std::env::current_exe().unwrap();
    let mut bytes = std::fs::read(&exe).unwrap();
    let e_lfanew = u32::from_le_bytes(bytes[0x3c..0x40].try_into().unwrap()) as usize;
    assert_eq!(&bytes[e_lfanew..e_lfanew + 4], b"PE\0\0", "not a PE");
    let opt = e_lfanew + 24;
    let magic = u16::from_le_bytes(bytes[opt..opt + 2].try_into().unwrap());
    assert_eq!(magic, 0x20b, "expected PE32+");
    let exception_dir = opt + 112 + 3 * 8;
    bytes[exception_dir..exception_dir + 4].copy_from_slice(&0x7fff_ffffu32.to_le_bytes());
    assert!(
        goblin::Object::parse(&bytes).is_err(),
        "strict parse should reject the broken directory"
    );
    let p = Program::from_bytes(exe, bytes).expect("permissive load");
    assert_eq!(p.format, BinaryFormat::Pe);
    assert!(!p.sections.is_empty(), "no sections after permissive load");
    assert!(p.entry.is_some(), "no entry after permissive load");
}

/// An anti-debug query is answered the way an unwatched process would, and
/// the answer is recorded.
///
/// Every emulation feature dies the moment a target checks for a debugger:
/// the run takes the detection path and reports on code that never executes
/// in anger.
#[test]
fn anti_debug_queries_are_answered_benignly() {
    use borer_engine::emulate::Emulator;
    use borer_engine::program::{Arch, Program, Section, Symbol, SymbolKind};
    // ASM: mov rcx,0; call qword [rel slot]; ret
    let code: Vec<u8> = vec![
        0x48, 0xc7, 0xc1, 0x00, 0x00, 0x00, 0x00, 0xff, 0x15, 0xf7, 0x0f, 0x00, 0x00, 0xc3,
    ];
    let mut bytes = code;
    bytes.resize(0x1000, 0);
    bytes.extend(std::iter::repeat_n(0u8, 0x1000));
    let mut p = Program::raw(
        bytes,
        Arch::X86_64,
        0,
        Some(0x1000),
        vec![
            Section::mapped(".text", 0x1000, 0, 0x1000, false, true),
            Section::mapped(".idata", 0x2000, 0x1000, 0x1000, false, false),
        ],
    );
    p.symbols = vec![Symbol {
        name: "KERNEL32.dll!IsDebuggerPresent".to_owned(),
        addr: 0x2004,
        kind: SymbolKind::Import,
    }];
    let mut emu = Emulator::new(&p, 200).expect("emulator");
    emu.install_imports();
    emu.run(0x1000);
    assert_eq!(emu.neutralized(), vec!["IsDebuggerPresent"]);
}

/// A pointer the modeled allocator hands out reads as zero and keeps what
/// the run wrote, instead of faulting where the OS would not.
#[test]
fn an_allocated_pointer_is_backed_memory() {
    use borer_engine::emulate::{Emulator, Stop};
    use borer_engine::program::{Arch, Program, Section, Symbol, SymbolKind};
    let code: Vec<u8> = [0xff, 0x15, 0xfa, 0x0f, 0x00, 0x00, 0x8a, 0x00, 0xc3].to_vec();
    let mut bytes = code;
    bytes.extend(std::iter::repeat_n(0u8, 0x1000));
    let mut p = Program::raw(
        bytes,
        Arch::X86_64,
        0,
        Some(0x1000),
        vec![
            Section::mapped(".text", 0x1000, 0, 0x1000, false, true),
            Section::mapped(".idata", 0x2000, 0x1000, 0x1000, false, false),
        ],
    );
    p.symbols = vec![Symbol {
        name: "ucrtbase.dll!malloc".to_owned(),
        addr: 0x2000,
        kind: SymbolKind::Import,
    }];
    let mut emu = Emulator::new(&p, 200).expect("emulator");
    emu.install_imports();
    let run = emu.run(0x1000);
    assert_ne!(run.stop, Stop::Fault(0));
    let at = emu.last_alloc().expect("an allocation");
    assert_eq!(emu.byte_at(at), Some(0), "reads as zero");
    assert!(emu.api_names().contains(&"malloc"), "malloc serviced");
}

/// A 32-bit call through an import slot reaches the API stub, as a 64-bit
/// one does.
///
/// The stubs were 64-bit addresses written as eight bytes, so a four-byte
/// slot held the zero low half and the call went to address zero; and the
/// call read eight bytes from its slot, so the next slot's stub rode along
/// in the high half. Two adjacent slots catch both.
#[test]
fn a_32_bit_call_through_an_import_slot_reaches_the_api() {
    use borer_engine::emulate::{Emulator, Stop};
    use borer_engine::program::{Arch, Program, Section, Symbol, SymbolKind};
    // ASM: call dword [0x2004]; ret
    let code: Vec<u8> = vec![0xff, 0x15, 0x04, 0x20, 0x00, 0x00, 0xc3];
    let mut bytes = code;
    bytes.resize(0x1000, 0);
    bytes.extend(std::iter::repeat_n(0u8, 0x1000));
    let mut p = Program::raw(
        bytes,
        Arch::X86,
        0,
        Some(0x1000),
        vec![
            Section::mapped(".text", 0x1000, 0, 0x1000, false, true),
            Section::mapped(".idata", 0x2000, 0x1000, 0x1000, false, false),
        ],
    );
    p.symbols = vec![
        Symbol {
            name: "KERNEL32.dll!IsDebuggerPresent".to_owned(),
            addr: 0x2004,
            kind: SymbolKind::Import,
        },
        Symbol {
            name: "KERNEL32.dll!GetTickCount".to_owned(),
            addr: 0x2008,
            kind: SymbolKind::Import,
        },
    ];
    let mut emu = Emulator::new(&p, 200).expect("emulator");
    emu.install_imports();
    let run = emu.run(0x1000);
    assert_eq!(run.stop, Stop::Returned, "{run:?}");
    assert_eq!(emu.api_names(), ["IsDebuggerPresent"]);
    assert_eq!(emu.neutralized(), vec!["IsDebuggerPresent"]);
}

/// A 32-bit image's allocations come back as pointers its four-byte
/// registers hold, and a write through one reads back.
///
/// Allocations started at a base above 2^32, so `eax` held only the zero
/// low half and the write landed at address zero; and `malloc` answered
/// its size as the pointer, because the first argument was taken as the
/// address asked for, as only `VirtualAlloc`'s is.
#[test]
fn a_32_bit_allocation_returns_a_pointer_the_image_can_hold() {
    use borer_engine::emulate::{Emulator, Stop};
    use borer_engine::program::{Arch, Program, Section, Symbol, SymbolKind};
    let code: Vec<u8> = vec![
        0x6a, 0x04, 0x68, 0x00, 0x10, 0x00, 0x00, 0x68, 0x00, 0x20, 0x00, 0x00, 0x6a, 0x00, 0xff,
        0x15, 0x04, 0x20, 0x00, 0x00, 0x89, 0xc6, 0xc7, 0x00, 0x44, 0x33, 0x22, 0x11, 0x8b, 0x08,
        0x6a, 0x10, 0xff, 0x15, 0x08, 0x20, 0x00, 0x00, 0x83, 0xc4, 0x04, 0xc3,
    ];
    let mut bytes = code;
    bytes.resize(0x1000, 0);
    bytes.extend(std::iter::repeat_n(0u8, 0x1000));
    let mut p = Program::raw(
        bytes,
        Arch::X86,
        0,
        Some(0x1000),
        vec![
            Section::mapped(".text", 0x1000, 0, 0x1000, false, true),
            Section::mapped(".idata", 0x2000, 0x1000, 0x1000, false, false),
        ],
    );
    p.symbols = vec![
        Symbol {
            name: "KERNEL32.dll!VirtualAlloc".to_owned(),
            addr: 0x2004,
            kind: SymbolKind::Import,
        },
        Symbol {
            name: "msvcrt.dll!malloc".to_owned(),
            addr: 0x2008,
            kind: SymbolKind::Import,
        },
    ];
    let mut emu = Emulator::new(&p, 200).expect("emulator");
    emu.install_imports();
    let run = emu.run(0x1000);
    assert_eq!(run.stop, Stop::Returned, "{run:?}");
    assert_eq!(emu.api_names(), ["VirtualAlloc", "malloc"]);
    let block = emu.register("rsi").expect("rsi");
    let heap = emu.register("rax").expect("rax");
    for ptr in [block, heap] {
        assert!((0x3000..1 << 32).contains(&ptr), "{ptr:#x}");
    }
    assert_ne!(block, heap);
    assert_eq!(emu.register("rcx"), Some(0x1122_3344));
    let written: Vec<Option<u8>> = (0..4).map(|k| emu.peek(block + k)).collect();
    assert_eq!(written, [Some(0x44), Some(0x33), Some(0x22), Some(0x11)]);
}
