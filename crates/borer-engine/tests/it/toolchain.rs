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
        out.contains("built:   Rust, rustc commit 0123456789ab (high: rustc source path at 0x"),
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
        out.contains("built:   Go, go1.22.3 (high: build information at 0x100)"),
        "{out}"
    );
    let empty = Program::raw(vec![0; 0x100], Arch::X86_64, 0, None, Vec::new());
    assert!(lines(&empty, false).is_empty());
}
