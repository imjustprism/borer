//! The Windows `borer-app.exe` as a launched program: a GUI-subsystem binary that opens
//! no console, whose measurement modes still answer on the pipes their caller hands it.

#![cfg(windows)]
#![expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]

use std::io::{BufRead as _, BufReader, Write as _};
use std::path::Path;
use std::process::{Command, Stdio};

use borer_engine::program::{checked_metadata, read_regular};

/// The PE optional header's `Subsystem` value for a Windows GUI program.
const IMAGE_SUBSYSTEM_WINDOWS_GUI: u16 = 2;

/// The built `borer-app` binary under test.
const EXE: &str = env!("CARGO_BIN_EXE_borer-app");

/// Returns the little-endian `u16` at `off` in `bytes`.
///
/// # Arguments
///
/// * `bytes` - The file's bytes.
/// * `off` - Byte offset of the value.
fn u16_at(bytes: &[u8], off: usize) -> u16 {
    u16::from_le_bytes([bytes[off], bytes[off + 1]])
}

/// The binary's PE header names the Windows GUI subsystem, so Windows gives a person who
/// launches it no console window.
#[test]
fn borer_app_is_a_gui_subsystem_binary() {
    let bytes = read_regular(Path::new(EXE), u64::MAX).expect("read borer-app.exe");
    let pe = usize::try_from(u32::from_le_bytes(
        bytes[0x3c..0x40].try_into().expect("e_lfanew"),
    ))
    .expect("e_lfanew fits");
    assert_eq!(&bytes[pe..pe + 4], b"PE\0\0");
    let subsystem = u16_at(&bytes, pe + 4 + 20 + 68);
    assert_eq!(subsystem, IMAGE_SUBSYSTEM_WINDOWS_GUI);
}

/// `--headless`, the memory benchmark's baseline, still writes its `HEADLESS_READY` report
/// to a piped stdout and exits once stdin gives it a line.
#[test]
fn headless_mode_reports_on_a_piped_stdout() {
    let notepad = Path::new(r"C:\Windows\System32\notepad.exe");
    if !checked_metadata(notepad).is_ok_and(|meta| meta.is_some_and(|m| m.is_file())) {
        return;
    }
    let mut child = Command::new(EXE)
        .arg("--headless")
        .arg(notepad)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::null())
        .spawn()
        .expect("spawn borer-app --headless");
    let mut line = String::new();
    BufReader::new(child.stdout.take().expect("piped stdout"))
        .read_line(&mut line)
        .expect("read the report");
    writeln!(child.stdin.take().expect("piped stdin")).expect("release the process");
    let status = child.wait().expect("wait for borer-app");
    assert!(line.starts_with("HEADLESS_READY "), "report was {line:?}");
    assert!(line.contains(" rows="), "report was {line:?}");
    assert!(status.success(), "exit status {status}");
}
