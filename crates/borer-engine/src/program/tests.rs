#![expect(clippy::disallowed_methods, reason = "the tests read their own files")]
use super::{Arch, Program, caught, unusable_path};

/// The summary of a file with no code says why code tools have nothing
/// to read and what its magic names, and claims no width for an
/// architecture it does not know; it read `arch: unknown (32-bit)`.
///
/// # Panics
///
/// When a line is missing or the width is claimed.
#[test]
fn the_summary_of_a_file_with_no_code_says_so() {
    let p = Program::raw(
        b"PK\x03\x04\x14\0\0\0".to_vec(),
        Arch::Unknown,
        0,
        None,
        Vec::new(),
    );
    let s = p.summary();
    assert!(s.contains("arch: unknown\n"), "{s}");
    assert!(s.contains("code:    raw file, arch 'unknown': "), "{s}");
    assert!(s.contains("magic:   zip archive\n"), "{s}");
    let code = Program::raw_x64(&[0xc3]).summary();
    assert!(code.contains("arch: x86-64 (64-bit)\n"), "{code}");
    assert!(
        !code.contains("code:") && !code.contains("magic:"),
        "{code}"
    );
}

/// A raw arm64 program has eight-byte pointers, as a loaded arm64
/// image does; `is_64` followed the x86 decoder width, which arm64 has
/// none of, and the summary called the program 32-bit.
///
/// # Panics
///
/// When the program is not 64-bit or the summary says otherwise.
#[test]
fn a_raw_arm64_program_is_64_bit() {
    let p = Program::raw(vec![0; 4], Arch::Arm64, 0, None, Vec::new());
    assert!(p.is_64);
    let s = p.summary();
    assert!(
        s.contains(
            "arch: arm64 (64-bit)
"
        ),
        "{s}"
    );
    assert!(!Program::raw(vec![0xc3], Arch::X86, 0, None, Vec::new()).is_64);
}

/// A section table of thousands of rows is listed up to the cap.
///
/// The summary and the compact list error messages append both stop
/// there, under a line that says how many there are: 65,535 rows made one
/// `binary_info` answer 4.6 MB.
///
/// # Panics
///
/// When a row past the cap is listed or the counts are not said.
#[test]
fn a_huge_section_table_is_listed_up_to_the_cap() {
    let sections = (0u64..1000)
        .map(|i| super::Section::mapped(&format!("s{i}"), 0x1000 * (i + 1), 0, 1, false, false))
        .collect();
    let p = Program::raw(vec![0xc3], Arch::X86_64, 0, None, sections);
    let s = p.summary();
    assert!(
        s.contains("sections (1000):\n# showing 64 of 1000 sections\n"),
        "{s}"
    );
    assert!(s.contains("  s63 ") && !s.contains("  s64 "), "{s}");
    let list = p.section_list();
    assert!(
        list.ends_with("s63(0x40000..0x40001) ... 936 more"),
        "{list}"
    );
}

/// A device name is refused instead of read.
///
/// Windows resolves these in every directory and under any extension, and
/// reading the console blocks on its input: inside the MCP server, whose
/// stdin carries the protocol, that consumed the session's own stream and
/// ended it with no reply to the call that asked for it.
///
/// # Panics
///
/// When a device is treated as a file, or a file as a device.
#[test]
fn a_device_name_is_not_a_file() {
    let is_device = |p: &str| unusable_path(std::path::Path::new(p)).is_some();
    if cfg!(windows) {
        assert!(is_device("con"), "the console");
        assert!(is_device("CON"), "the filesystem does not care about case");
        assert!(is_device("con.txt"), "an extension does not make it a file");
        assert!(is_device(r"C:\tmp\con"), "nor does a directory");
        assert!(is_device("com1") && is_device("LPT9"), "the numbered ports");
        assert!(Program::load(std::path::Path::new("con")).is_err());
        assert!(
            is_device("CONIN$") && is_device("conout$"),
            "the console halves"
        );
        assert!(is_device(r"\\.\pipe\borer"), "a pipe");
        assert!(
            is_device("//./PhysicalDrive0"),
            "a disk, spelled with slashes"
        );
        assert!(is_device(r"\\?\GLOBALROOT\Device\Null"), "an object path");
        assert!(!is_device(r"\\?\C:\tmp\a.exe"), "a long drive path");
        for share in [
            r"\\?\UNC\host\share\a.exe",
            r"\\host\share\a.exe",
            "//host/share/a.exe",
            r"\\?\unc\host\share\a.pdb",
        ] {
            let why = unusable_path(std::path::Path::new(share));
            assert!(
                why.as_deref()
                    .is_some_and(|w| w.contains("names a network share")),
                "{share}: {why:?}"
            );
            let refused =
                Program::load(std::path::Path::new(share)).expect_err("a share is never opened");
            assert!(refused.to_string().contains("network share"), "{refused}");
        }
        assert!(
            !is_device(r"\\.\C:\tmp\a.exe"),
            "a drive path in the device space"
        );
        let dir = std::env::temp_dir();
        let refused = Program::load(&dir).expect_err("a directory is no program");
        assert!(refused.to_string().contains("is a directory"), "{refused}");
    }
    assert!(!is_device("control.dll"), "a real name starting with con");
    assert!(!is_device("com0"), "there is no COM0");
    assert!(!is_device("com10"), "nor a two-digit port");
    assert!(!is_device("borer.exe"));
    assert!(unusable_path(std::path::Path::new("")).is_some());
}

/// A path in the NT object namespace is refused in every spelling, as
/// every spelling of a share is.
///
/// Windows hands a `\??\` path to the kernel unparsed, and `\??\UNC` is the
/// network redirector: the check took `\??\UNC\host\share\x` for a rooted
/// local path, so opening it, or asking whether it existed, connected to the
/// host and authenticated as the user.
///
/// # Panics
///
/// When such a path is let through, or a drive path refused.
#[test]
fn an_nt_path_is_never_a_file() {
    if cfg!(windows) {
        let let_through: Vec<&str> = [
            r"\??\UNC\host.invalid\s\x",
            r"\??\C:\x",
            r"\??\unc\host.invalid\s",
            "//?/UNC/host.invalid/s",
            r"\\.\UNC\host.invalid\s",
            r"\\?\GLOBALROOT\Device\Mup\host.invalid\s",
            r"\\;LanmanRedirector\host.invalid\s",
        ]
        .into_iter()
        .filter(|p| unusable_path(std::path::Path::new(p)).is_none())
        .collect();
        assert!(let_through.is_empty(), "{let_through:?}");
    }
    assert_eq!(unusable_path(std::path::Path::new(r"C:\x")), None);
}

/// A `\\.\` path that climbs with `..` is refused: Windows folds `..` there
/// with `\\.\` as the root, so `\\.\C:\..\UNC\host\share\x` opens the share
/// and `\\.\C:\..\pipe\x` a named pipe.
///
/// The check took both for drive paths, and a PE whose debug record names
/// the first had every load of it ask the host whether the PDB was there.
/// Only a `..` component climbs: a name holding two dots is a name.
///
/// # Panics
///
/// When such a path is let through, or a name with two dots refused.
#[test]
fn a_device_path_climbing_out_of_its_drive_is_refused() {
    if cfg!(windows) {
        let let_through: Vec<&str> = [
            r"\\.\C:\..\UNC\host.invalid\s\x",
            "//./C:/x/../../UNC/host.invalid/s",
            r"\\.\C:\..\pipe\x",
            r"\\.\C:\..\x",
            "//?/C:/../UNC/host.invalid/s/x.pdb",
            r"\\?/C:/../UNC/host.invalid/s",
            r"/\?\C:\..\UNC\host.invalid\s",
            "//?/C:/../pipe/x",
        ]
        .into_iter()
        .filter(|p| unusable_path(std::path::Path::new(p)).is_none())
        .collect();
        assert!(let_through.is_empty(), "{let_through:?}");
        let named = unusable_path(std::path::Path::new(r"\\.\C:\d\a..b.exe"));
        assert_eq!(named, None, "a name with two dots");
        let unparsed = unusable_path(std::path::Path::new(r"\\?\C:\x"));
        assert_eq!(unparsed, None, "an exact long drive path");
    }
}

/// A device name is refused however Windows spells it: Windows 11 reads a
/// trailing space or dot, a `:`, a non-drive character before `:` and a
/// superscript port digit as the device (probed with `RtlIsDosDeviceName_U`),
/// and the stem the check compared kept each of them.
///
/// # Panics
///
/// When one is let through, or a file named like one refused.
#[test]
fn a_device_name_is_refused_however_windows_spells_it() {
    if cfg!(windows) {
        let let_through: Vec<&str> = [
            "con ",
            "con  .",
            "con:",
            "conin$:",
            "aux:",
            "COM1:",
            "COM\u{b9}",
            "lpt\u{b3}",
            "1:nul",
            ";:nul",
            "/:nul",
        ]
        .into_iter()
        .filter(|p| unusable_path(std::path::Path::new(p)).is_none())
        .collect();
        assert!(let_through.is_empty(), "{let_through:?}");
        let why = unusable_path(std::path::Path::new("1:nul")).expect("1:nul is NUL");
        assert!(why.contains("names a device"), "{why}");
    }
    for file in ["com\u{b9}0", "comet.exe", "nul_x.bin", "1:comet.exe"] {
        assert_eq!(unusable_path(std::path::Path::new(file)), None, "{file}");
    }
}

/// Builds a minimal x86-64 PE32+ image whose `CodeView` PDB70 debug record
/// holds `pdb_path`.
///
/// # Panics
///
/// When `pdb_path` does not fit in the `.text` page.
fn pe_with_codeview(pdb_path: &str) -> Vec<u8> {
    const PE: usize = 0x80;
    const OPT: usize = PE + 24;
    const SEC: usize = OPT + 0xf0;
    const DBG: usize = 0x220;
    const RSDS: usize = 0x240;
    let rsds_len = u64::try_from(24 + pdb_path.len() + 1).expect("rsds size");
    let mut b = vec![0u8; 0x600];
    assert!(RSDS + 25 + pdb_path.len() <= b.len(), "record path fits");
    b[..2].copy_from_slice(b"MZ");
    b[PE..PE + 4].copy_from_slice(b"PE\0\0");
    b[SEC..SEC + 5].copy_from_slice(b".text");
    b[0x200] = 0xc3;
    b[RSDS..RSDS + 4].copy_from_slice(b"RSDS");
    b[RSDS + 4..RSDS + 20].fill(1);
    b[RSDS + 24..RSDS + 24 + pdb_path.len()].copy_from_slice(pdb_path.as_bytes());
    for (at, val, width) in [
        (0x3c, 0x80u64, 4usize),
        (PE + 4, 0x8664, 2),
        (PE + 6, 1, 2),
        (PE + 20, 0xf0, 2),
        (PE + 22, 0x22, 2),
        (OPT, 0x20b, 2),
        (OPT + 16, 0x1000, 4),
        (OPT + 24, 0x1_4000_0000, 8),
        (OPT + 32, 0x1000, 4),
        (OPT + 36, 0x200, 4),
        (OPT + 48, 6, 2),
        (OPT + 56, 0x2000, 4),
        (OPT + 60, 0x200, 4),
        (OPT + 68, 3, 2),
        (OPT + 108, 16, 4),
        (OPT + 160, 0x1020, 4),
        (OPT + 164, 28, 4),
        (SEC + 8, 0x400, 4),
        (SEC + 12, 0x1000, 4),
        (SEC + 16, 0x400, 4),
        (SEC + 20, 0x200, 4),
        (SEC + 36, 0x6000_0020, 4),
        (DBG + 12, 2, 4),
        (DBG + 16, rsds_len, 4),
        (DBG + 20, 0x1040, 4),
        (DBG + 24, 0x240, 4),
        (RSDS + 20, 1, 4),
    ] {
        b[at..at + width].copy_from_slice(&val.to_le_bytes()[..width]);
    }
    b
}

/// A PE whose `CodeView` record climbs through `//?/` loads without that
/// path being tried.
///
/// Windows leaves only an exact `\\?\` unparsed, so it folded the `..` and
/// the record reached any file, share or device it named: here a local file
/// that is no PDB, which the lookup found and reported unreadable.
///
/// # Panics
///
/// When the record does not parse or its path is tried.
#[test]
fn a_record_climbing_through_a_device_path_is_never_tried() {
    if !cfg!(windows) {
        return;
    }
    let dir = std::env::temp_dir().join(format!("borer-cv-{}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("a temp dir");
    let decoy = dir.join("cv.pdb");
    std::fs::write(&decoy, b"no pdb").expect("written");
    let climb = format!("//?/X:/../{}", decoy.display()).replace('\\', "/");
    let bytes = pe_with_codeview(&climb);
    let loaded = Program::from_bytes_with(dir.join("bin").join("x.exe"), bytes, true, None);
    std::fs::remove_dir_all(&dir).expect("cleans up");
    let loaded = loaded.expect("the image loads");
    assert_eq!(loaded.pdb_record.map(|r| r.path), Some(climb.clone()));
    assert!(loaded.pdb.is_none(), "{climb} was tried: {:?}", loaded.pdb);
}

/// The section index answers what a scan of the table in file order does.
///
/// However the sections nest or overlap, its rows do not overlap: a
/// table of sections that all overlap one another costs a look-up one
/// binary search, where a walk back over the rows visited every one of
/// them.
///
/// # Panics
///
/// When a look-up differs from the scan, or the rows overlap.
#[test]
fn the_section_index_answers_as_a_scan_does() {
    use super::{Section, section_in};
    let mut sections: Vec<Section> = (0..2000u64)
        .map(|k| {
            let va = 0x1000 + (k % 37) * 0x100;
            let size = 0x10_0000 - k * 0x80;
            Section::mapped(&format!("s{k}"), va, 0, size, false, k % 3 == 0)
        })
        .collect();
    sections.push(Section::mapped("bss", 0x9000_0000, 0, 0, false, false));
    sections.push(Section::mapped("far", 0x8000_0000, 0, 0x100, false, false));
    let index = Program::index_sections(&sections);
    assert!(index.len() <= 2 * sections.len(), "{} rows", index.len());
    assert!(
        index.windows(2).all(|w| w[0].end <= w[1].va),
        "rows overlap"
    );
    let scan = |va: u64| {
        sections
            .iter()
            .find(|s| s.file_size > 0 && va >= s.va.0 && va - s.va.0 < s.vsize.max(s.file_size))
    };
    for va in (0..0x11_0000u64).step_by(0x3f).chain([
        0x8000_0000,
        0x8000_00ff,
        0x8000_0100,
        0x9000_0000,
        u64::MAX,
    ]) {
        assert_eq!(
            section_in(&sections, &index, va).map(|s| s.name.as_str()),
            scan(va).map(|s| s.name.as_str()),
            "{va:#x}"
        );
    }
}

/// A read by path takes only a regular file within its cap, judged
/// before it is opened, so a pipe or a device never blocks or reads
/// forever.
///
/// # Panics
///
/// When a directory, a device, a pipe or an oversized file is read.
#[test]
fn a_read_takes_only_a_regular_file_within_its_cap() {
    use super::read_regular;
    let dir = std::env::temp_dir().join(format!("borer-regular-{}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("a temp dir");
    let file = dir.join("ten.txt");
    std::fs::write(&file, b"0123456789").expect("written");
    assert_eq!(
        read_regular(&file, 10).expect("within the cap"),
        b"0123456789"
    );
    let over = read_regular(&file, 9).expect_err("past the cap");
    assert!(over.to_string().contains("past the 9"), "{over}");
    let isdir = read_regular(&dir, u64::MAX).expect_err("a directory");
    assert!(isdir.to_string().contains("is a directory"), "{isdir}");
    #[cfg(unix)]
    {
        let device =
            read_regular(std::path::Path::new("/dev/zero"), u64::MAX).expect_err("a device");
        assert!(
            device.to_string().contains("not a regular file"),
            "{device}"
        );
        let fifo = dir.join("pipe");
        if std::process::Command::new("mkfifo")
            .arg(&fifo)
            .status()
            .is_ok_and(|s| s.success())
        {
            let pipe = read_regular(&fifo, u64::MAX).expect_err("a pipe");
            assert!(pipe.to_string().contains("not a regular file"), "{pipe}");
            assert!(Program::load(&fifo).is_err(), "a pipe is no program");
        }
    }
    std::fs::remove_dir_all(&dir).expect("cleans up");
}

/// The checked open and stat refuse what the checked read refuses: a share
/// before any call, a directory by its metadata; a path that names nothing
/// stats as `None`, where the read is an error.
///
/// # Panics
///
/// When a share or a directory is let through, or a missing file errs.
#[test]
fn the_checked_open_and_stat_refuse_as_the_read_does() {
    use super::{checked_metadata, open_regular};
    let dir = std::env::temp_dir();
    let isdir = open_regular(&dir, u64::MAX).expect_err("a directory");
    assert!(isdir.to_string().contains("is a directory"), "{isdir}");
    let missing = checked_metadata(&dir.join("borer-no-such-file")).map(|m| m.is_some());
    assert_eq!(missing, Ok(false));
    if cfg!(windows) {
        let share = std::path::Path::new(r"\\host.invalid\share\x");
        assert!(checked_metadata(share).is_err() && open_regular(share, u64::MAX).is_err());
    }
}

/// A name out of the file cannot forge a row in a listing.
///
/// Section names are eight raw bytes the file chooses freely, and every
/// listing borer prints is one record to a line. A name holding a newline
/// therefore reads as two records, the second of them invented by the file
/// under analysis and indistinguishable from a real one; a terminal escape
/// in the same place rewrites whatever is around it. The running test
/// binary is the fixture, so the name comes through the real parser rather
/// than a constructed `Section`.
///
/// # Panics
///
/// When a hostile name survives into a section name.
#[test]
fn a_name_out_of_the_file_cannot_forge_a_row() {
    let exe = std::env::current_exe().expect("the test binary has a path");
    let mut bytes = std::fs::read(&exe).expect("the test binary is readable");
    if bytes.first_chunk::<2>() != Some(b"MZ") {
        return;
    }
    let at = |b: &[u8], off: usize, n: usize| -> usize {
        let mut v = 0usize;
        for (i, byte) in b.iter().skip(off).take(n).enumerate() {
            v |= (*byte as usize) << (8 * i);
        }
        v
    };
    let lfanew = at(&bytes, 0x3c, 4);
    let table = lfanew + 4 + 20 + at(&bytes, lfanew + 4 + 16, 2);
    let Some(name) = bytes.get_mut(table..table + 8) else {
        panic!("the test binary has no section table at {table:#x}");
    };
    name.copy_from_slice(b".t\nEVIL\x1b");

    let program = Program::from_bytes(exe, bytes).expect("a PE with an odd name still loads");
    let first = &program.sections.first().expect("it has sections").name;
    assert!(
        !first.contains(char::is_control),
        "a row can be forged: {first:?}"
    );
    assert!(
        first.starts_with(".t"),
        "the readable part is kept: {first:?}"
    );
}

/// A parse that faults on a damaged file is an error, not a crash.
///
/// The parser indexes a file by the offsets the file's own headers state,
/// and a truncated or rewritten file states offsets outside it. That
/// faults rather than failing, which unwinds past every `Result` the
/// caller was ready for - and in a server it takes the session with it.
/// Damaged and hostile files are the job here, so the fault is caught and
/// told as what it is.
///
/// # Panics
///
/// When a fault reaches the caller, or a sound parse does not.
#[test]
fn a_parse_that_faults_is_told_as_an_error() {
    let faulted = caught(|| {
        let small = [0u8; 4];
        let past = std::hint::black_box(small.len() + 5);
        #[expect(clippy::indexing_slicing, reason = "the fault under test")]
        small[past]
    });
    assert!(faulted.is_err(), "the fault reached the caller");
    let said = faulted.unwrap_err().to_string();
    assert!(
        said.contains("truncated or damaged"),
        "the error does not say what happened: {said}"
    );
    assert!(
        !said.contains("  "),
        "the message reads as one line: {said}"
    );
}

/// A file too short or too damaged to parse says what it is.
///
/// An empty file is refused in those words, a few bytes of no known
/// format load as raw bytes as a longer one does, and a file whose magic
/// names a format but whose headers do not parse is called truncated or
/// damaged, not an unrecognized format.
///
/// # Panics
///
/// When a file loads or is refused otherwise.
#[test]
fn a_short_file_says_what_it_is() {
    let load = |b: &[u8]| Program::from_bytes(std::path::PathBuf::from("short"), b.to_vec());
    let empty = load(b"").expect_err("an empty file is no program");
    assert!(empty.to_string().contains("the file is empty"), "{empty}");
    let one = load(b"x").expect("one byte of nothing known loads raw");
    assert_eq!(one.format, super::BinaryFormat::Raw);
    for (bytes, kind) in [(&b"MZ"[..], "a PE"), (b"ELF", "an ELF image")] {
        let said = load(bytes).expect_err("a header too short").to_string();
        assert!(
            said.starts_with(&format!(
                "the file starts like {kind} but its headers do not parse"
            )),
            "{said}"
        );
        assert!(said.contains("truncated or damaged"), "{said}");
    }
}

/// A parse that does not fault is returned untouched.
///
/// # Panics
///
/// When a sound parse is reported as a fault.
#[test]
fn a_parse_that_holds_is_returned_as_it_is() {
    assert_eq!(caught(|| 7u32).ok(), Some(7));
}

/// The panic hook is put back, so a later fault still reports itself,
/// also after two parses overlapped.
///
/// Silencing the hook for the length of the parse keeps a backtrace about
/// a file the caller already knows is broken off stderr. Leaving it
/// silenced would hide every unrelated panic the process goes on to have.
///
/// # Panics
///
/// When the hook is not restored.
#[test]
fn the_panic_hook_is_put_back_after_a_parse() {
    let marker = std::sync::Arc::new(std::sync::atomic::AtomicBool::new(false));
    let seen = std::sync::Arc::clone(&marker);
    std::panic::set_hook(Box::new(move |_| {
        seen.store(true, std::sync::atomic::Ordering::SeqCst);
    }));
    let _ = caught(|| panic!("under test"));
    let out = std::panic::catch_unwind(|| panic!("after"));
    assert!(out.is_err());
    assert!(
        marker.load(std::sync::atomic::Ordering::SeqCst),
        "the hook this test installed never ran again"
    );
    let both = std::sync::Arc::new(std::sync::Barrier::new(2));
    let overlapping: Vec<_> = (0..2)
        .map(|_| {
            let both = std::sync::Arc::clone(&both);
            std::thread::spawn(move || {
                let _ = caught(|| {
                    both.wait();
                    panic!("overlapping")
                });
            })
        })
        .collect();
    for t in overlapping {
        t.join().expect("a parse thread finishes");
    }
    marker.store(false, std::sync::atomic::Ordering::SeqCst);
    let out = std::panic::catch_unwind(|| panic!("after two at once"));
    assert!(out.is_err());
    assert!(
        marker.load(std::sync::atomic::Ordering::SeqCst),
        "two overlapping parses left the process without its hook"
    );
    let _ = std::panic::take_hook();
}
