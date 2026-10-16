//! Carving a firmware-style blob.
//!
//! The programs and containers it holds are found by signature and
//! validated headers, the program opens as one of its own with its parent
//! recorded, a random block is flagged by its entropy, and signatures over
//! bad headers are not listed.

#![expect(
    clippy::missing_panics_doc,
    clippy::expect_used,
    reason = "assertions are the point of a test"
)]

use std::path::PathBuf;

use borer_engine::carve::{Kind, Size, at, children_tsv, scan};
use borer_engine::program::{BinaryFormat, Program};

/// Where the embedded PE starts in the blob.
const PE_AT: usize = 0x400;
/// Where the zip archive starts.
const ZIP_AT: usize = 0x900;
/// Where the first gzip stream starts: zeros follow it.
const GZIP_AT: usize = 0xa00;
/// Where the ELF header starts.
const ELF_AT: usize = 0xb00;
/// Where the Mach-O header starts.
const MACHO_AT: usize = 0xc00;
/// Where the second gzip stream starts, random bytes after it.
const STREAM_AT: usize = 0x1000;
/// Where the random block with no header starts.
const RANDOM_AT: usize = 0x2000;
/// Where the forged signatures start, one every 0x40 bytes.
const FORGED_AT: usize = 0x3000;
/// Size of the blob.
const BLOB_LEN: usize = 0x3400;

/// Writes bytes at an offset.
fn put(b: &mut [u8], at: usize, bytes: &[u8]) {
    b[at..at + bytes.len()].copy_from_slice(bytes);
}

/// Bytes from an `xorshift64` generator: deterministic noise.
fn noise(len: usize, mut state: u64) -> Vec<u8> {
    (0..len)
        .map(|_| {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            state.to_le_bytes()[3]
        })
        .collect()
}

/// The CRC-32 zip and gzip use (IEEE, reflected).
fn crc32(data: &[u8]) -> u32 {
    let mut crc = u32::MAX;
    for &byte in data {
        crc ^= u32::from(byte);
        for _ in 0..8 {
            crc = (crc >> 1) ^ (0xedb8_8320 & (crc & 1).wrapping_neg());
        }
    }
    !crc
}

/// A PE32+ x86-64 console exe, 0x400 bytes: headers, then one `.text`
/// section of 0x200 file bytes at 0x200.
fn tiny_pe() -> Vec<u8> {
    /// The PE signature's offset.
    const SIG: usize = 0x80;
    /// The optional header's offset.
    const OPT: usize = SIG + 24;
    /// The section row's offset.
    const ROW: usize = OPT + 0xf0;
    let mut b = vec![0u8; 0x400];
    put(&mut b, 0, b"MZ");
    put(&mut b, 0x3c, &0x80u32.to_le_bytes());
    put(&mut b, SIG, b"PE\0\0");
    put(&mut b, SIG + 4, &0x8664u16.to_le_bytes());
    put(&mut b, SIG + 6, &1u16.to_le_bytes());
    put(&mut b, SIG + 20, &0xf0u16.to_le_bytes());
    put(&mut b, SIG + 22, &0x22u16.to_le_bytes());
    put(&mut b, OPT, &0x20bu16.to_le_bytes());
    put(&mut b, OPT + 16, &0x1000u32.to_le_bytes());
    put(&mut b, OPT + 24, &0x1_4000_0000u64.to_le_bytes());
    put(&mut b, OPT + 32, &0x1000u32.to_le_bytes());
    put(&mut b, OPT + 36, &0x200u32.to_le_bytes());
    put(&mut b, OPT + 48, &6u16.to_le_bytes());
    put(&mut b, OPT + 56, &0x2000u32.to_le_bytes());
    put(&mut b, OPT + 60, &0x200u32.to_le_bytes());
    put(&mut b, OPT + 68, &3u16.to_le_bytes());
    put(&mut b, OPT + 108, &16u32.to_le_bytes());
    put(&mut b, ROW, b".text");
    put(&mut b, ROW + 8, &0x200u32.to_le_bytes());
    put(&mut b, ROW + 12, &0x1000u32.to_le_bytes());
    put(&mut b, ROW + 16, &0x200u32.to_le_bytes());
    put(&mut b, ROW + 20, &0x200u32.to_le_bytes());
    put(&mut b, ROW + 36, &0x6000_0020u32.to_le_bytes());
    // ASM: mov eax, 7; ret
    put(&mut b, 0x200, &[0xb8, 0x07, 0x00, 0x00, 0x00, 0xc3]);
    b
}

/// A stored zip of one entry `a.txt` holding `hello`: local header, data,
/// central directory and its end record, offsets counted from its start.
fn tiny_zip() -> Vec<u8> {
    let data = b"hello";
    let crc = crc32(data).to_le_bytes();
    let mut z = Vec::new();
    z.extend_from_slice(b"PK\x03\x04\x14\x00\x00\x00\x00\x00\x00\x00\x00\x00");
    z.extend_from_slice(&crc);
    z.extend_from_slice(&5u32.to_le_bytes());
    z.extend_from_slice(&5u32.to_le_bytes());
    z.extend_from_slice(&5u16.to_le_bytes());
    z.extend_from_slice(&0u16.to_le_bytes());
    z.extend_from_slice(b"a.txt");
    z.extend_from_slice(data);
    let cd = z.len();
    z.extend_from_slice(b"PK\x01\x02\x14\x00\x14\x00\x00\x00\x00\x00\x00\x00\x00\x00");
    z.extend_from_slice(&crc);
    z.extend_from_slice(&5u32.to_le_bytes());
    z.extend_from_slice(&5u32.to_le_bytes());
    z.extend_from_slice(&5u16.to_le_bytes());
    z.extend_from_slice(&[0; 12]);
    z.extend_from_slice(&0u32.to_le_bytes());
    z.extend_from_slice(b"a.txt");
    let cd_len = z.len() - cd;
    z.extend_from_slice(b"PK\x05\x06\x00\x00\x00\x00\x01\x00\x01\x00");
    z.extend_from_slice(&u32::try_from(cd_len).expect("small").to_le_bytes());
    z.extend_from_slice(&u32::try_from(cd).expect("small").to_le_bytes());
    z.extend_from_slice(&0u16.to_le_bytes());
    z
}

/// A gzip header naming `name`, then the first byte of a deflate block of
/// type `btype`.
fn gzip_header(name: &[u8], btype: u8) -> Vec<u8> {
    let mut g = vec![0x1f, 0x8b, 0x08, 0x08, 0, 0, 0, 0, 0x00, 0x03];
    g.extend_from_slice(name);
    g.push(0);
    g.push(1 | (btype << 1));
    g
}

/// An ELF64 x86-64 executable header with no program or section headers.
fn tiny_elf() -> Vec<u8> {
    let mut e = vec![0u8; 64];
    put(&mut e, 0, b"\x7fELF\x02\x01\x01");
    put(&mut e, 16, &2u16.to_le_bytes());
    put(&mut e, 18, &0x3eu16.to_le_bytes());
    put(&mut e, 20, &1u32.to_le_bytes());
    put(&mut e, 52, &64u16.to_le_bytes());
    e
}

/// A Mach-O 64 x86-64 executable header with one `LC_SEGMENT_64` whose
/// file bytes run to 0x100.
fn tiny_macho() -> Vec<u8> {
    let mut m = vec![0u8; 0x100];
    put(&mut m, 0, &0xfeed_facfu32.to_le_bytes());
    put(&mut m, 4, &0x0100_0007u32.to_le_bytes());
    put(&mut m, 8, &3u32.to_le_bytes());
    put(&mut m, 12, &2u32.to_le_bytes());
    put(&mut m, 16, &1u32.to_le_bytes());
    put(&mut m, 20, &72u32.to_le_bytes());
    put(&mut m, 32, &0x19u32.to_le_bytes());
    put(&mut m, 36, &72u32.to_le_bytes());
    put(&mut m, 32 + 48, &0x100u64.to_le_bytes());
    m
}

/// The blob: an embedded PE, a zip, a gzip followed by zeros, an ELF and a
/// Mach-O header, a gzip followed by noise, a random block, and forged
/// signatures whose headers do not hold.
fn blob() -> Vec<u8> {
    let mut b = vec![0u8; BLOB_LEN];
    put(&mut b, 0, b"firmware blob v1\n");
    put(&mut b, PE_AT, &tiny_pe());
    put(&mut b, ZIP_AT, &tiny_zip());
    put(&mut b, GZIP_AT, &gzip_header(b"x.bin", 0));
    put(&mut b, ELF_AT, &tiny_elf());
    put(&mut b, MACHO_AT, &tiny_macho());
    put(&mut b, STREAM_AT, &noise(0x800, 0x9e37_79b9_7f4a_7c15));
    put(&mut b, STREAM_AT, &gzip_header(b"payload", 2));
    put(&mut b, RANDOM_AT, &noise(0x800, 0x0123_4567_89ab_cdef));
    let forged: [&[u8]; 9] = [
        b"MZ\0\0\0\0\0\0",
        b"PK\x03\x04\x14\x00\x00\x00\xff\xff",
        b"\x7fELF\x07\x01\x01",
        b"MSCF\x01\0\0\0\x40\0\0\0",
        b"\xfd7zXZ\x00\x00\x04\0\0\0\0",
        b"7z\xbc\xaf\x27\x1c\x00\x04\0\0\0\0",
        b"hsqs\0\0\0\0",
        b"\x27\x05\x19\x56\0\0\0\0",
        b"ANDROID!\0\0\0\0",
    ];
    for (k, f) in forged.iter().enumerate() {
        put(&mut b, FORGED_AT + 0x40 * k, f);
    }
    put(&mut b, FORGED_AT + 0x3c, &0x10u32.to_le_bytes());
    put(&mut b, FORGED_AT + 0x300, &gzip_header(b"bad", 3));
    b
}

/// Loads bytes as a program from a temporary file named for the test.
fn written(bytes: &[u8], name: &str) -> PathBuf {
    let path = std::env::temp_dir().join(format!("borer-carve-{name}-{}.bin", std::process::id()));
    std::fs::write(&path, bytes).expect("temp file");
    path
}

/// Every program and container is found at its offset with its size and
/// identity, and no forged signature is.
#[test]
fn the_blob_s_children_are_found_and_forgeries_are_not() {
    let b = blob();
    let found = scan(&b);
    let seen: Vec<(u64, Kind, Size)> = found.iter().map(|c| (c.off, c.kind, c.size)).collect();
    assert_eq!(
        seen,
        vec![
            (0x400, Kind::Pe, Size::Stated(0x400)),
            (
                0x900,
                Kind::Zip,
                Size::Stated(u64::try_from(tiny_zip().len()).expect("small"))
            ),
            (0xa00, Kind::Gzip, Size::Unknown),
            (0xb00, Kind::Elf, Size::Stated(64)),
            (0xc00, Kind::MachO, Size::Stated(0x100)),
            (0x1000, Kind::Gzip, Size::Unknown),
        ],
        "{found:#?}"
    );
    let identity = |off: u64| {
        found
            .iter()
            .find(|c| c.off == off)
            .map(|c| c.identity.clone())
            .unwrap_or_default()
    };
    assert_eq!(identity(0x400), "PE32+ x86-64 exe, console, 1 section");
    assert_eq!(identity(0x900), "zip archive, 1 entry, first 'a.txt'");
    assert_eq!(identity(0xa00), "gzip stream (deflate) of 'x.bin'");
    assert_eq!(
        identity(0xb00),
        "ELF64 x86-64 executable (little-endian), 0 sections"
    );
    assert_eq!(identity(0xc00), "Mach-O 64 x86-64 execute, 1 load command");
}

/// The listing names every child, sizes the stream before its noise from
/// the entropy run, flags the random block with no header, and is the same
/// on a second read.
#[test]
fn the_listing_flags_the_random_block_and_repeats() {
    let p = Program::from_bytes(PathBuf::from("blob.bin"), blob()).expect("any bytes load");
    assert_eq!(p.format, BinaryFormat::Raw);
    let out = children_tsv(&p);
    assert!(
        out.starts_with(
            "# children of blob.bin: 6 programs or containers by signature, 1 high-entropy run with none\n"
        ),
        "{out}"
    );
    for row in [
        "\n0x400\t0x400\tpe\tPE32+ x86-64 exe, console, 1 section\n",
        "\n0x900\t0x71\tzip\tzip archive, 1 entry, first 'a.txt'\n",
        "\n0xa00\t-\tgzip\tgzip stream (deflate) of 'x.bin'\n",
        "\n0x1000\t~0x800\tgzip\tgzip stream (deflate) of 'payload'\n",
        "\n0x2000\t0x800\tentropy\t",
    ] {
        assert!(out.contains(row), "{row:?} in\n{out}");
    }
    assert!(!out.contains("\n0x3"), "a forgery is listed:\n{out}");
    assert_eq!(out, children_tsv(&p));
}

/// `<file>@<offset>` opens the embedded PE as a program with its parent
/// recorded and said by the summary; an offset holding a container, or
/// nothing, is refused with what is there.
#[test]
fn an_embedded_pe_opens_as_its_own_program() {
    let path = written(&blob(), "open");
    let shown = path.display().to_string();
    let child = Program::load(&PathBuf::from(format!("{shown}@0x400")));
    let zip = Program::load(&PathBuf::from(format!("{shown}@0x900")));
    let nothing = Program::load(&PathBuf::from(format!("{shown}@0x123")));
    let past = Program::load(&PathBuf::from(format!("{shown}@0x99999")));
    drop(std::fs::remove_file(&path));
    let child = child.expect("the embedded PE loads");
    assert_eq!(child.format, BinaryFormat::Pe);
    assert_eq!(child.bytes.len(), 0x400);
    assert_eq!(child.entry, Some(0x1_4000_1000));
    let parent = child
        .parent
        .as_ref()
        .expect("a carved program has a parent");
    assert_eq!(
        (parent.path.clone(), parent.off, parent.len),
        (path, 0x400, 0x400)
    );
    assert!(
        child.summary().contains(&format!(
            "parent:  {shown} at file offset 0x400, 0x400 bytes\n"
        )),
        "{}",
        child.summary()
    );
    let zip = format!("{:#}", zip.expect_err("a zip is not a program"));
    assert!(zip.contains("holds a zip at 0x900"), "{zip}");
    let nothing = format!("{:#}", nothing.expect_err("nothing starts there"));
    assert!(
        nothing.contains("no PE, ELF or Mach-O image starts at 0x123"),
        "{nothing}"
    );
    let past = format!("{:#}", past.expect_err("past the end"));
    assert!(past.contains("past the end"), "{past}");
}

/// The containers a firmware image carries are each identified from a
/// header that validates: its CRC, its reserved fields, its version.
#[test]
fn firmware_containers_are_identified() {
    let mut uimage = vec![0u8; 64];
    put(&mut uimage, 0, &0x2705_1956u32.to_be_bytes());
    put(&mut uimage, 12, &0x100u32.to_be_bytes());
    uimage[28..32].copy_from_slice(&[5, 22, 2, 1]);
    put(&mut uimage, 32, b"Linux-6.1");
    let crc = crc32(&uimage);
    put(&mut uimage, 4, &crc.to_be_bytes());

    let mut seven = b"7z\xbc\xaf\x27\x1c\x00\x04".to_vec();
    let mut tail = 0x40u64.to_le_bytes().to_vec();
    tail.extend_from_slice(&0x20u64.to_le_bytes());
    tail.extend_from_slice(&0u32.to_le_bytes());
    seven.extend_from_slice(&crc32(&tail).to_le_bytes());
    seven.extend_from_slice(&tail);

    let mut cab = b"MSCF".to_vec();
    for v in [0u32, 0x200, 0, 0x2c, 0] {
        cab.extend_from_slice(&v.to_le_bytes());
    }
    cab.extend_from_slice(&[3, 1, 1, 0, 2, 0]);

    let mut cpio = Vec::new();
    for (name, size) in [(&b"init"[..], 3usize), (&b"TRAILER!!!"[..], 0)] {
        let mut h = format!("070701{}", "00000000".repeat(6));
        h.push_str(&format!("{size:08x}"));
        h.push_str(&"00000000".repeat(4));
        h.push_str(&format!("{:08x}", name.len() + 1));
        h.push_str("00000000");
        cpio.extend_from_slice(h.as_bytes());
        cpio.extend_from_slice(name);
        cpio.push(0);
        while cpio.len() % 4 != 0 {
            cpio.push(0);
        }
        cpio.extend(std::iter::repeat_n(b'x', size));
        while cpio.len() % 4 != 0 {
            cpio.push(0);
        }
    }

    let mut boot = vec![0u8; 1664];
    put(&mut boot, 0, b"ANDROID!");
    put(&mut boot, 8, &0x1800u32.to_le_bytes());
    put(&mut boot, 16, &0x900u32.to_le_bytes());
    put(&mut boot, 36, &0x800u32.to_le_bytes());

    let mut squash = vec![0u8; 96];
    put(&mut squash, 0, b"hsqs");
    put(&mut squash, 4, &7u32.to_le_bytes());
    put(&mut squash, 12, &0x2_0000u32.to_le_bytes());
    put(&mut squash, 20, &4u16.to_le_bytes());
    put(&mut squash, 22, &17u16.to_le_bytes());
    put(&mut squash, 28, &4u16.to_le_bytes());
    put(&mut squash, 40, &0x3000u64.to_le_bytes());

    let mut cram = vec![0u8; 64];
    put(&mut cram, 0, &0x28cd_3d45u32.to_le_bytes());
    put(&mut cram, 4, &0x1000u32.to_le_bytes());
    put(&mut cram, 16, b"Compressed ROMFS");
    put(&mut cram, 44, &12u32.to_le_bytes());
    put(&mut cram, 48, b"rootfs");

    let cases: [(&[u8], Kind, Size, &str); 7] = [
        (
            &uimage,
            Kind::UImage,
            Size::Stated(0x140),
            "uImage 'Linux-6.1', arm64 kernel, gzip",
        ),
        (
            &seven,
            Kind::SevenZip,
            Size::Stated(0x80),
            "7z archive, format 0.4",
        ),
        (
            &cab,
            Kind::Cab,
            Size::Stated(0x200),
            "cabinet, 2 files in 1 folder",
        ),
        (
            &cpio,
            Kind::Cpio,
            Size::Stated(u64::try_from(cpio.len()).expect("small")),
            "cpio archive (newc), 1 entry, first 'init'",
        ),
        (
            &boot,
            Kind::AndroidBoot,
            Size::Stated(0x800 + 0x1800 + 0x1000),
            "Android boot image v0, kernel 0x1800 bytes, ramdisk 0x900 bytes, page 0x800",
        ),
        (
            &squash,
            Kind::Squashfs,
            Size::Stated(0x3000),
            "squashfs 4.0, xz, 7 inodes, 128 KiB blocks",
        ),
        (
            &cram,
            Kind::Cramfs,
            Size::Stated(0x1000),
            "cramfs 'rootfs', 12 files",
        ),
    ];
    for (bytes, kind, size, identity) in cases {
        let mut file = vec![0u8; 0x10];
        file.extend_from_slice(bytes);
        file.resize(0x10 + 0x5000, 0);
        let child = at(&file, 0x10).unwrap_or_else(|| panic!("{kind:?} validates"));
        assert_eq!((child.kind, child.size), (kind, size), "{child:?}");
        assert_eq!(child.identity, identity);
        let mut forged = file.clone();
        forged[0x10 + 6] ^= 0x40;
        if matches!(kind, Kind::UImage | Kind::SevenZip) {
            assert!(at(&forged, 0x10).is_none(), "{kind:?} with a bad CRC");
        }
    }
}

/// A stated size past the end of the file is cut there and the cut said.
#[test]
fn a_truncated_program_says_so() {
    let pe = tiny_pe();
    let mut b = vec![0u8; 0x100];
    b.extend_from_slice(&pe[..0x300]);
    let child = at(&b, 0x100).expect("the headers still validate");
    assert_eq!(child.size, Size::Stated(0x300));
    assert!(
        child
            .identity
            .ends_with("; truncated: the headers state 0x400 bytes and 0x300 remain"),
        "{}",
        child.identity
    );
}
