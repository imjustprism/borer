//! What built and wraps a file, from hand-built PEs: each finding names its
//! evidence and how sure it is, and a file nothing names is called unknown.

#![expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]

use borer_engine::toolchain::lines;

use crate::bundle::{NET_BUNDLE, image, load, pyinstaller_archive, with_resources};

/// The summary lines about what built and wraps `bytes`, joined.
fn said(bytes: Vec<u8>) -> String {
    lines(&load(bytes), false).join("\n")
}

/// A payload names its wrapper, with what its table says and where the
/// table is.
#[test]
fn a_payload_names_its_wrapper() {
    let pkg = pyinstaller_archive();
    let bytes = image(vec![0; 0x200], &pkg);
    let start = bytes.len() - pkg.len();
    let out = said(bytes);
    assert!(
        out.contains(&format!(
            "wrapper: PyInstaller, Python 3.11, loads python311.dll (high: payload table at {start:#x})"
        )),
        "{out}"
    );
    assert!(
        out.contains(&format!(
            "payload: PyInstaller at {start:#x}, 2 entries; borer://children"
        )),
        "{out}"
    );
}

/// A .NET apphost whose bundle marker points at no bundle is a launcher.
#[test]
fn an_apphost_without_a_bundle_is_a_launcher() {
    let mut marker = vec![0u8; 0x200];
    marker[8..40].copy_from_slice(&NET_BUNDLE);
    let out = said(image(marker, &[]));
    assert!(
        out.contains("wrapper: .NET apphost (high: bundle marker at 0x608"),
        "{out}"
    );
}

/// The VCL's own resources name Delphi, and an `AutoIt` script resource
/// its wrapper, with where each sits.
#[test]
fn resources_name_delphi_and_autoit() {
    let mut script = vec![0xa3; 16];
    script.extend_from_slice(b"AU3!EA06");
    let out = said(with_resources(&[("SCRIPT", &script), ("DVCLAL", &[1; 16])]));
    assert!(
        out.contains("built:   Delphi or C++Builder (high: RCDATA DVCLAL at 0x"),
        "{out}"
    );
    assert!(
        out.contains(
            "wrapper: AutoIt, an AU3! script record, encrypted (high: payload table at 0x"
        ),
        "{out}"
    );
}

/// Compiler texts name the compiler with their version, and a file with
/// none says it is unknown.
#[test]
fn compiler_texts_name_their_version() {
    let mut d = vec![0u8; 0x200];
    let gcc = b"GCC: (Rev2, Built by MSYS2 project) 13.2.0\0";
    d[0x10..0x10 + gcc.len()].copy_from_slice(gcc);
    let rust = b"/rustc/0123456789abcdef0123456789abcdef01234567/library/core/src/panicking.rs";
    d[0x80..0x80 + rust.len()].copy_from_slice(rust);
    let out = said(image(d, &[]));
    assert!(out.contains("built:   GCC, (Rev2, Built by MSYS2 project) 13.2.0 (high: compiler identification at 0x"), "{out}");
    assert!(
        out.contains("built:   Rust, rustc commit 0123456789ab (medium: rustc source path at 0x"),
        "{out}"
    );
    let plain = said(image(vec![0; 0x200], &[]));
    assert!(
        plain.starts_with("built:   unknown: no Rich header, compiler text or runtime mark"),
        "{plain}"
    );
}

/// UPX's header mark names it with its version, and with its sections
/// renamed says it was modified.
#[test]
fn a_upx_header_mark_names_a_renamed_upx() {
    let mut b = image(vec![0; 0x200], &[]);
    b[0x3d0..0x3d9].copy_from_slice(b"4.22\0UPX!");
    let out = said(b);
    assert!(
        out.contains("packer:  UPX, sections renamed: a modified or hand-edited UPX (high: UPX! mark at 0x3d5 in the headers, written by UPX 4.22)"),
        "{out}"
    );
}

/// A raw image, a dump with no headers, is still read for the marks in its
/// bytes, and says nothing of a compiler it cannot see.
#[test]
fn a_raw_image_keeps_its_marks() {
    use borer_engine::program::{Arch, Program};
    let mut bytes = vec![0u8; 0x100];
    bytes.extend_from_slice(b"\xff Go buildinf:\x08\x02go1.22.3\0");
    let raw = Program::raw(bytes, Arch::X86_64, 0, None, Vec::new());
    let out = lines(&raw, false).join("\n");
    assert!(
        out.contains("built:   Go, go1.22.3 (medium: build information at 0x100)"),
        "{out}"
    );
    let empty = Program::raw(vec![0; 0x100], Arch::X86_64, 0, None, Vec::new());
    assert!(lines(&empty, false).is_empty());
}

/// A rustc source path reads high only with a second sign behind it.
///
/// The sign is a second path under its commit in a loaded section, or
/// rustc's version text naming that commit. Paths under many commits, one
/// each, are what no build writes: the finding says so and reads low, as it
/// does when the version text names another commit.
#[test]
fn a_rust_mark_reads_high_only_with_a_second_sign() {
    let commit = "0123456789abcdef0123456789abcdef01234567";
    let path = |c: &str, file: &str| format!("/rustc/{c}/library/{file}\0");
    let said_with = |texts: &[String]| {
        let joined = texts.concat();
        let mut d = vec![0u8; 0x600];
        d[0x40..0x40 + joined.len()].copy_from_slice(joined.as_bytes());
        said(image(d, &[]))
    };
    let two = said_with(&[
        path(commit, "core/src/panicking.rs"),
        path(commit, "alloc/src/raw_vec.rs"),
    ]);
    assert!(
        two.contains("built:   Rust, rustc commit 0123456789ab (high: rustc source path at 0x")
            && two.contains("; 2 paths of that commit in loaded sections)"),
        "{two}"
    );
    let version = |short: &str| {
        said_with(&[
            path(commit, "core/src/panicking.rs"),
            format!("rustc version 1.96.1 ({short} 2026-01-01)\0"),
        ])
    };
    let agrees = version("0123456");
    assert!(
        agrees.contains("(high: rustc source path at 0x")
            && agrees.contains("; rustc version text at 0x"),
        "{agrees}"
    );
    let hashless = said_with(&[
        path(commit, "core/src/panicking.rs"),
        "rustc version 1.96.1\0".to_owned(),
    ]);
    assert!(
        hashless.contains("(medium: rustc source path at 0x") && !hashless.contains("version text"),
        "a version text naming no commit is no second sign: {hashless}"
    );
    let other = version("fedcba987");
    assert!(
        other.contains("(low: rustc source path at 0x") && other.contains(" names another commit)"),
        "{other}"
    );
    let other_commit = "fedcba9876543210fedcba9876543210fedcba98";
    let mut d = vec![0u8; 0x600];
    let mixed = [
        path(other_commit, "core/src/lib.rs"),
        path(commit, "core/src/panicking.rs"),
        path(commit, "alloc/src/raw_vec.rs"),
    ]
    .concat();
    d[0x40..0x40 + mixed.len()].copy_from_slice(mixed.as_bytes());
    let bytes = image(d, &[]);
    let needle = format!("/rustc/{commit}/");
    let named_at = bytes
        .windows(needle.len())
        .position(|w| w == needle.as_bytes())
        .expect("the named commit's first path");
    let two_commits = said(bytes);
    assert!(
        two_commits.contains(&format!(
            "built:   Rust, rustc commit 0123456789ab (high: rustc source path at {named_at:#x}; 2 paths of that commit"
        )),
        "the path cited is one of the commit named: {two_commits}"
    );
    let many: Vec<String> = (0..8u64)
        .map(|k| path(&format!("{k:040x}"), "core/src/lib.rs"))
        .collect();
    let planted = said_with(&many);
    assert!(
        planted.contains("built:   Rust, rustc commit 000000000000 (low: rustc source path at 0x")
            && planted.contains(
                "; paths under 8 rustc commits, one path each: no build writes that, so they read as planted)"
            ),
        "{planted}"
    );
}

/// A Rust-mangled symbol is a second sign for a rustc source path.
///
/// A C++ name ending like one without its hash is not, and neither is a
/// second path under the commit in a section the loader does not map, since
/// a debug table repeats what the code holds.
#[test]
fn a_rust_mangled_symbol_backs_a_rustc_path() {
    use crate::elfgen::{self, A, AX, EM_X86_64, ET_EXEC, PROGBITS, STRTAB, SYMTAB, Sec};
    use borer_engine::program::Program;
    let path = |file: &str| {
        format!("/rustc/0123456789abcdef0123456789abcdef01234567/library/{file}\0").into_bytes()
    };
    let built = |name: &str| {
        let mut strtab = vec![0u8];
        strtab.extend_from_slice(name.as_bytes());
        strtab.push(0);
        let mut symtab = vec![0u8; 24];
        symtab.extend(elfgen::sym_sized(1, 0x12, 1, 0x1000, 1));
        let mut secs = vec![
            Sec::new(".text", PROGBITS, AX, 0x1000, vec![0xc3; 0x10]),
            Sec::new(".rodata", PROGBITS, A, 0x2000, path("core/src/lib.rs")),
            Sec::new(".symtab", SYMTAB, 0, 0x3000, symtab),
            Sec::new(".strtab", STRTAB, 0, 0x3100, strtab),
            Sec::new(".debug_str", PROGBITS, 0, 0x3200, path("alloc/src/lib.rs")),
        ];
        secs[2].link = 4;
        secs[2].info = 1;
        secs[2].entsize = 24;
        let bytes = elfgen::build(ET_EXEC, EM_X86_64, 0x1000, &secs);
        let p = Program::from_bytes(std::path::PathBuf::from("rust.elf"), bytes).expect("loads");
        lines(&p, false).join("\n")
    };
    let mangled = built("_ZN4core9panicking5panic17h0123456789abcdefE");
    assert!(
        mangled.contains(
            "built:   Rust, rustc commit 0123456789ab (high: rustc source path at 0x2000; Rust-mangled symbols)"
        ),
        "{mangled}"
    );
    for name in ["panic", "_ZN3foo17hghijklmnopqrstuvE"] {
        let plain = built(name);
        assert!(
            plain.contains(
                "built:   Rust, rustc commit 0123456789ab (medium: rustc source path at 0x2000)"
            ),
            "{name}: {plain}"
        );
    }
}
