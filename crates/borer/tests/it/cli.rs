//! CLI mode tests: drive the real borer binary (`CARGO_BIN_EXE_borer`).

#![expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]

use std::process::{Command, Output};
use std::sync::{Condvar, Mutex, PoisonError};

/// Children the tests run at once.
///
/// Most commands analyze borer's own debug build: about 400 MB and every
/// core for a few seconds each. Cargo runs the tests on as many threads as
/// the machine has cores, so without a bound a 16-core machine ran sixteen
/// such children at once, and two gates side by side stalled it.
const CHILDREN_MAX: usize = 2;

/// How many children are running now.
static RUNNING: Mutex<usize> = Mutex::new(0);

/// Signalled each time a child finishes.
static FINISHED: Condvar = Condvar::new();

/// A permit to run one child, returned when dropped.
struct Slot;

impl Slot {
    /// Waits until fewer than [`CHILDREN_MAX`] children run, then takes a
    /// permit.
    ///
    /// # Returns
    ///
    /// The permit; hold it until the child has exited.
    fn take() -> Slot {
        let mut running = RUNNING.lock().unwrap_or_else(PoisonError::into_inner);
        while *running >= CHILDREN_MAX {
            running = FINISHED
                .wait(running)
                .unwrap_or_else(PoisonError::into_inner);
        }
        *running += 1;
        Slot
    }
}

impl Drop for Slot {
    /// Returns the permit and wakes one waiting test.
    fn drop(&mut self) {
        let mut running = RUNNING.lock().unwrap_or_else(PoisonError::into_inner);
        *running = running.saturating_sub(1);
        FINISHED.notify_one();
    }
}

/// Runs the borer binary to completion.
///
/// # Arguments
///
/// * `args` - Command-line arguments after the program name.
///
/// # Returns
///
/// The exit status with both output streams.
#[expect(
    clippy::expect_used,
    reason = "a spawn failure has no useful recovery in a test helper"
)]
fn output(args: &[&str]) -> Output {
    // INVARIANT: the tests pin the binary's own facts, and the dev-profile
    // binary always has its PDB beside it (and its recorded path valid), so
    // every run analyzes the image alone.
    let _slot = Slot::take();
    Command::new(env!("CARGO_BIN_EXE_borer"))
        .arg("--no-pdb")
        .args(args)
        .output()
        .expect("spawn borer.exe")
}

/// Runs the borer binary with arguments, with `--no-pdb` prepended for a
/// deterministic baseline (see [`output`]).
///
/// # Arguments
///
/// * `args` - Command-line arguments after the program name.
///
/// # Returns
///
/// `(exit status was success, stdout as lossy UTF-8)`.
fn run(args: &[&str]) -> (bool, String) {
    let out = output(args);
    (
        out.status.success(),
        String::from_utf8_lossy(&out.stdout).to_string(),
    )
}

/// Runs the CLI and returns success plus stdout and stderr joined, for a
/// command whose refusal is what the test reads.
///
/// # Arguments
///
/// * `args` - Command-line arguments after the program name.
fn run_all(args: &[&str]) -> (bool, String) {
    let out = output(args);
    let mut text = String::from_utf8_lossy(&out.stdout).to_string();
    text.push_str(&String::from_utf8_lossy(&out.stderr));
    (out.status.success(), text)
}

/// Runs the borer binary with arguments and no option prepended, for the
/// runs that test what the options change.
///
/// # Arguments
///
/// * `args` - Command-line arguments after the program name.
///
/// # Returns
///
/// `(exit status was success, stdout as lossy UTF-8)`.
#[expect(
    clippy::expect_used,
    reason = "a spawn failure has no useful recovery in a test helper"
)]
fn run_raw(args: &[&str]) -> (bool, String) {
    let _slot = Slot::take();
    let out = Command::new(env!("CARGO_BIN_EXE_borer"))
        .args(args)
        .output()
        .expect("spawn borer.exe");
    (
        out.status.success(),
        String::from_utf8_lossy(&out.stdout).to_string(),
    )
}

/// A reader that stops listening (`borer functions x | head`) ends the
/// command quietly and successfully instead of with a panic.
///
/// # Panics
///
/// When the process cannot be spawned or waited for.
#[test]
#[cfg_attr(
    not(windows),
    ignore = "reads borer's own build, pinned as the Windows x64 PE"
)]
fn cli_ends_quietly_when_stdout_closes() {
    use std::process::{Command, Stdio};
    let exe = env!("CARGO_BIN_EXE_borer");
    let _slot = Slot::take();
    let mut child = Command::new(exe)
        .arg("--no-pdb")
        .args(["functions", exe, "", "0", "2000"])
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("spawn borer.exe");
    drop(child.stdout.take());
    let status = child.wait().expect("wait");
    let mut err = String::new();
    if let Some(mut e) = child.stderr.take() {
        std::io::Read::read_to_string(&mut e, &mut err).ok();
    }
    assert!(status.success(), "closed stdout must not fail: {err}");
    assert!(!err.contains("panicked"), "{err}");
}

/// `info` on the binary itself reports the PE format and its sections.
#[test]
#[cfg_attr(
    not(windows),
    ignore = "reads borer's own build, pinned as the Windows x64 PE"
)]
fn cli_info_on_own_pe() {
    let exe = env!("CARGO_BIN_EXE_borer");
    let (ok, out) = run(&["info", exe]);
    assert!(ok, "info failed:\n{out}");
    assert!(
        out.contains("format:  PE"),
        "no format line:\n{}",
        &out[..200.min(out.len())]
    );
    assert!(out.contains("sections ("));
}

/// The dev-profile binary always has its PDB beside it, so `info` without
/// `--no-pdb` reports the companion as applied.
///
/// # Panics
///
/// When the PDB outcome line is missing.
#[test]
#[cfg_attr(
    not(windows),
    ignore = "reads borer's own build, pinned as the Windows x64 PE"
)]
fn cli_info_applies_the_companion_pdb() {
    let exe = env!("CARGO_BIN_EXE_borer");
    let (ok, out) = run_raw(&["info", exe]);
    assert!(
        ok,
        "info failed:
{out}"
    );
    assert!(
        out.contains("pdb:     "),
        "no pdb line:
{out}"
    );
}

/// `functions` lists discovered functions with default names, and `disasm`
/// at the entry reported by `info` prints addressed instructions.
#[test]
#[cfg_attr(
    not(windows),
    ignore = "reads borer's own build, pinned as the Windows x64 PE"
)]
fn cli_functions_and_disasm() {
    let exe = env!("CARGO_BIN_EXE_borer");
    let (ok, out) = run(&["functions", exe]);
    assert!(ok, "functions failed:\n{out}");
    assert!(out.contains("of"), "no functions header");
    assert!(out.contains("sub_"), "no default function names");
    assert!(
        out.contains("# entry size blocks instrs callers callees src name"),
        "no source column:\n{}",
        &out[..300.min(out.len())]
    );

    let (ok, info) = run(&["info", exe]);
    assert!(ok);
    let entry = info
        .lines()
        .find(|l| l.contains("entry: "))
        .and_then(|l| l.split("entry: ").nth(1))
        .and_then(|e| e.split_whitespace().next())
        .expect("entry in info")
        .to_owned();
    let (ok, dis) = run(&["disasm", exe, &entry, "4"]);
    assert!(ok, "disasm failed:\n{dis}");
    assert!(dis.contains("0x"), "no addresses in disasm output");
}

/// An unknown command exits non-zero.
#[test]
fn cli_unknown_command_fails() {
    let (ok, out) = run(&["frobnicate", "whatever"]);
    assert!(!ok, "unknown command should fail");
    assert!(out.contains("usage:") || out.is_empty());
}

/// An unknown command, option or help topic is refused by name with a
/// non-zero exit.
///
/// Each is refused before any file is loaded and without the whole usage
/// text; a command given no binary says so with its own usage lines.
/// `--bogus info x` loaded `info` as the binary, `bogus` alone said a
/// binary path was missing, and `help nosuch` printed every command and
/// exited 0.
///
/// # Panics
///
/// When a refusal succeeds, words its reason otherwise, or carries the
/// whole usage text.
#[test]
fn cli_refuses_unknown_words_precisely() {
    for (args, reason) in [
        (
            &["--bogus", "info", "x"][..],
            "unknown option '--bogus'; the options are --pack <file>, --no-auto-packs and --no-pdb",
        ),
        (&["info", "--bogus", "x"][..], "unknown option '--bogus'"),
        (
            &["bogus", "x"][..],
            "unknown command 'bogus'; `borer help` lists the commands",
        ),
        (&["bogus"][..], "unknown command 'bogus'"),
        (&["help", "nosuch"][..], "unknown command 'nosuch'"),
        (&["nosuch", "--help"][..], "unknown command 'nosuch'"),
        (
            &["info"][..],
            "info needs a binary path\nusage:\n  info <binary>",
        ),
        (&[][..], "an option was given but no command"),
    ] {
        let (ok, out) = run_all(args);
        assert!(!ok, "{args:?} succeeded: {out}");
        assert!(out.contains(reason), "{args:?}: {out}");
        assert!(!out.contains("loading"), "{args:?} loaded a file: {out}");
        assert!(
            !out.contains("functions <binary>"),
            "{args:?} printed the whole usage: {out}"
        );
    }
}

/// Every command refuses an argument past the ones its usage lists, by
/// name and before it loads the binary, where some answered as if it were
/// not there.
///
/// # Panics
///
/// When an extra argument is accepted or refused with another reason.
#[test]
fn cli_refuses_an_argument_too_many() {
    for (args, reason) in [
        (
            &["info", "x", "junk"][..],
            "info takes nothing after the binary, not 'junk'",
        ),
        (
            &["functions", "x", "", "0", "5", "extra"][..],
            "functions takes at most 3 arguments after the binary, not also 'extra'",
        ),
        (
            &["disasm", "x", "0x1000", "4", "junk"][..],
            "disasm takes at most 2 arguments after the binary, not also 'junk'",
        ),
        (
            &["pack-keys", "extra"][..],
            "pack-keys takes nothing, not 'extra'",
        ),
        (
            &["help", "info", "extra"][..],
            "help takes one command, not also 'extra'",
        ),
    ] {
        let (ok, out) = run_all(args);
        assert!(!ok, "{args:?} succeeded: {out}");
        assert!(out.contains(reason), "{args:?}: {out}");
        assert!(!out.contains("loading"), "{args:?} loaded a file: {out}");
    }
}

/// `hexdump`, `read` and `disasm` take a name where an address goes, as the
/// tools of the same names do, where they took numbers alone.
///
/// # Panics
///
/// When a name is refused, or the three commands read it at different
/// addresses.
#[test]
#[cfg_attr(
    not(windows),
    ignore = "reads borer's own build, pinned as the Windows x64 PE"
)]
fn cli_addresses_take_names() {
    let exe = env!("CARGO_BIN_EXE_borer");
    let (ok, dump) = run(&["hexdump", exe, "GetLastError", "8"]);
    assert!(ok, "{dump}");
    let at = dump
        .strip_prefix("# ")
        .and_then(|l| l.split("..").next())
        .expect("a range header")
        .to_owned();
    let (ok, out) = run(&["read", exe, "GetLastError", "u8", "1"]);
    assert!(ok && out.starts_with(&at), "{at}: {out}");
    let (ok, out) = run(&["disasm", exe, "GetLastError", "1"]);
    assert!(ok && out.lines().any(|l| l.starts_with(&at)), "{at}: {out}");
}

/// `disasm` and `read` refuse a count of zero as `hexdump` refuses a
/// length of zero, where they read one; `snapshot` refuses a device as
/// every other command that writes a file does, before its analysis.
///
/// # Panics
///
/// When a zero count is read, or the device is written.
#[test]
fn cli_counts_and_devices_are_refused_alike() {
    let exe = std::env::current_exe().expect("the test binary has a path");
    let exe = exe.to_string_lossy().to_string();
    let mut cases = vec![
        (
            vec!["disasm", exe.as_str(), "0x0", "0"],
            "disasm count must be at least 1",
        ),
        (
            vec!["read", exe.as_str(), "0x0", "u8", "0"],
            "read count must be at least 1",
        ),
        (
            vec!["hexdump", exe.as_str(), "0x0", "0"],
            "hexdump length must be at least 1",
        ),
    ];
    if cfg!(windows) {
        cases.push((vec!["snapshot", exe.as_str(), "NUL"], "nothing was written"));
    }
    for (args, reason) in cases {
        let (ok, out) = run_all(&args);
        assert!(!ok, "{args:?} succeeded: {out}");
        assert!(out.contains(reason), "{args:?}: {out}");
    }
}

/// An error quotes a 30 KB argument cut short on one row, where it came
/// back whole.
///
/// # Panics
///
/// When an error runs past a row.
#[test]
fn cli_errors_quote_a_long_argument_cut_short() {
    let exe = std::env::current_exe().expect("the test binary has a path");
    let exe = exe.to_string_lossy().to_string();
    let long = "A".repeat(30_000);
    for args in [
        vec!["read", exe.as_str(), "0x0", long.as_str()],
        vec!["search", exe.as_str(), "41", long.as_str()],
        vec!["types", exe.as_str(), long.as_str()],
        vec![
            "set-type",
            exe.as_str(),
            "C:/borer-no-such/p.json",
            long.as_str(),
        ],
        vec![long.as_str(), exe.as_str()],
    ] {
        let (ok, out) = run_all(&args);
        assert!(!ok, "{} succeeded", args[0].len());
        assert!(out.len() < 1500, "{} bytes: {}", out.len(), &out[..120]);
    }
}

/// `--help` lists the commands and mentions the MCP server mode.
#[test]
fn cli_help_lists_commands() {
    let (ok, out) = run(&["--help"]);
    assert!(ok);
    assert!(out.contains("functions"));
    assert!(out.contains("MCP stdio server"));
}

/// `entropy` refuses a threshold outside 0..8 bits per byte as the MCP tool does.
///
/// It scanned for what no window can reach (or every window, below zero);
/// it now refuses, and answers under a `showing` header.
#[test]
fn cli_entropy_checks_its_threshold() {
    let exe = env!("CARGO_BIN_EXE_borer");
    for bad in ["9", "-1", "NaN", "1e308"] {
        let (ok, out) = run_all(&["entropy", exe, bad]);
        assert!(!ok, "{bad} accepted:\n{out}");
        assert!(out.contains("is outside 0..8 bits per byte"), "{out}");
        assert!(out.len() < 400, "{out}");
    }
    let (ok, out) = run(&["entropy", exe, "7.9"]);
    assert!(ok, "{out}");
    assert!(out.starts_with("# showing "), "{out}");
}

/// `symbols` pages the way the MCP tool does.
///
/// It lists 50 rows unless a limit says otherwise, and its header names the
/// next page's offset: it printed every symbol of the binary in one answer.
#[test]
fn cli_symbols_page() {
    let exe = env!("CARGO_BIN_EXE_borer");
    let (ok, out) = run(&["symbols", exe, "", "1", "3"]);
    assert!(ok, "{out}");
    let header = out.lines().next().unwrap_or_default();
    assert!(
        header.starts_with("# showing 3 of ") && header.ends_with("; offset=4 for the next page"),
        "{out}"
    );
    let rows = |text: &str| text.lines().filter(|l| !l.starts_with('#')).count();
    assert_eq!(rows(&out), 3, "{out}");
    let (ok, out) = run(&["symbols", exe]);
    assert!(ok, "{out}");
    assert_eq!(rows(&out), 50, "{out}");
}

/// An architecture with no disassembler still answers what the headers say.
///
/// The symbol table is parsed out of the file, not recovered from its code,
/// so a 32-bit ARM (Thumb-2) image, which borer cannot disassemble, still
/// has imports, exports and locals to list. An arm64 image used to report
/// "locals: N named functions" in its summary and then refuse to name them,
/// because the listing asked for an analysis it only wanted a dead-import
/// marker from.
#[test]
fn cli_symbols_survive_an_unanalyzable_arch() {
    let exe = std::env::current_exe().expect("the test binary has a path");
    let mut bytes = std::fs::read(&exe).expect("the test binary is readable");
    if bytes.first_chunk::<2>() != Some(b"MZ") {
        return;
    }
    let at = |b: &[u8], off: usize, n: usize| -> usize {
        b.iter()
            .skip(off)
            .take(n)
            .enumerate()
            .fold(0, |v, (i, byte)| v | ((*byte as usize) << (8 * i)))
    };
    // SPEC: the COFF machine field is the first u16 after the PE signature.
    let machine = at(&bytes, 0x3c, 4) + 4;
    let field = bytes
        .get_mut(machine..machine + 2)
        .expect("the fixture has a COFF header");
    field.copy_from_slice(&0x01c4u16.to_le_bytes());

    let path = std::env::temp_dir().join(format!("borer_armnt_fixture_{}.bin", std::process::id()));
    std::fs::write(&path, &bytes).expect("the fixture is writable");
    let path = path.to_string_lossy().to_string();

    let (ok, out) = run(&["info", &path]);
    assert!(
        ok,
        "info failed:
{out}"
    );
    assert!(
        out.contains("ARM_NT"),
        "the fixture is not 32-bit ARM:
{out}"
    );

    let (ok, out) = run(&["symbols", &path]);
    assert!(
        ok,
        "symbols refused a 32-bit ARM image:
{out}"
    );
    assert!(
        out.contains("import") || out.contains("export"),
        "no symbols:
{out}"
    );

    // What genuinely needs the code still says so, rather than answering
    // "nothing found" with an empty list.
    let (ok, out) = run(&["functions", &path]);
    assert!(!ok, "functions should refuse an arch it cannot disassemble");
    assert!(out.contains("no code analysis") || out.is_empty(), "{out}");

    drop(std::fs::remove_file(&path));
}

/// An arm64 image disassembles, discovers and decompiles from the command
/// line.
///
/// `disasm` lists one word per row four bytes apart, up to where the
/// discovered function's code ends, and so does a script's `disasm`;
/// `functions` lists what discovery finds, `decompile` answers with the
/// entry's text, `emulate` runs the entry in the arm64 machine, `verify`
/// checks the entry's lifting against it and `verify ... text` its text,
/// and `oracle` refuses, saying what applies.
///
/// The fixture is the test binary with its COFF machine set to arm64, so
/// what decodes is x86 code read as arm64 words, its exception directory
/// read as arm64 `.pdata`: the rows' shape is what is checked, not their
/// text, and that discovery over it answers rather than faults.
#[test]
fn cli_disassembles_and_discovers_an_arm64_image() {
    let exe = std::env::current_exe().expect("the test binary has a path");
    let mut bytes = std::fs::read(&exe).expect("the test binary is readable");
    if bytes.first_chunk::<2>() != Some(b"MZ") {
        return;
    }
    let pe = bytes
        .get(0x3c..0x40)
        .and_then(|b| <[u8; 4]>::try_from(b).ok())
        .map(u32::from_le_bytes)
        .and_then(|at| usize::try_from(at).ok())
        .expect("the fixture names its PE header");
    // SPEC: the COFF machine field is the first u16 after the PE signature.
    bytes
        .get_mut(pe + 4..pe + 6)
        .expect("the fixture has a COFF header")
        .copy_from_slice(&0xaa64u16.to_le_bytes());
    let dir = std::env::temp_dir();
    let id = std::process::id();
    let path = dir.join(format!("borer_arm64_disasm_{id}.bin"));
    std::fs::write(&path, &bytes).expect("the fixture is writable");
    let script = dir.join(format!("borer_arm64_disasm_{id}.rhai"));
    let path = path.to_string_lossy().to_string();

    let (ok, info) = run(&["info", &path]);
    assert!(ok && info.contains("arch: arm64 (64-bit)"), "{info}");
    let entry = info
        .lines()
        .find_map(|l| l.split("entry: ").nth(1))
        .and_then(|e| e.split_whitespace().next())
        .and_then(|e| u64::from_str_radix(e.trim_start_matches("0x"), 16).ok())
        .expect("entry in info");
    let (ok, out) = run(&["disasm", &path, &format!("{entry:#x}"), "4"]);
    assert!(ok, "disasm failed:\n{out}");
    let rows: Vec<&str> = out.lines().filter(|l| l.starts_with("0x")).collect();
    // INVARIANT: the listing stops where the discovered entry function's code
    // ends, which x86 bytes read as arm64 words reach within the four asked.
    assert!(!rows.is_empty() && rows.len() <= 4, "{out}");
    for (row, at) in rows.iter().zip((0u64..).map(|i| entry + 4 * i)) {
        let (va, rest) = row.split_once("  ").expect("an address, then bytes");
        assert_eq!(va, format!("{at:#x}"), "{out}");
        let column = rest.get(..24).unwrap_or(rest);
        assert_eq!(column.split_whitespace().count(), 4, "{out}");
    }

    std::fs::write(&script, format!("print(disasm({entry:#x}, 3).len());\n"))
        .expect("the script is writable");
    let (ok, out) = run(&["script", &path, &script.to_string_lossy()]);
    assert!(ok && out.starts_with("3\n"), "{out}");

    let (ok, out) = run_all(&["functions", &path]);
    assert!(ok && out.starts_with("# showing "), "{out}");
    let (_, out) = run_all(&["decompile", &path, &format!("{entry:#x}")]);
    assert!(!out.contains("does not yet decompile it"), "{out}");
    let (ok, out) = run_all(&["emulate", &path, &format!("{entry:#x},steps=64")]);
    assert!(ok && out.starts_with("# ran "), "{out}");
    let (ok, out) = run_all(&["oracle", &path, &format!("{entry:#x}")]);
    assert!(!ok && out.contains("x86-64 code only for now"), "{out}");
    let (_, out) = run_all(&["verify", &path, &format!("{entry:#x}")]);
    assert!(out.starts_with("# verified 1 functions, "), "{out}");
    assert!(out.contains("\n# vector: "), "{out}");
    let (_, out) = run_all(&["verify", &path, &format!("{entry:#x}"), "1", "1", "text"]);
    assert!(out.starts_with("# replayed 1 functions, "), "{out}");

    drop(std::fs::remove_file(&path));
    drop(std::fs::remove_file(&script));
}

/// A file that is no program, base64 of random bytes as an encrypted wallet
/// stores it, is triaged from its bytes instead of refused, and the code
/// tools name the format and the tools that do read it.
#[test]
fn cli_triages_a_file_with_no_code() {
    const ALPHABET: &[u8; 64] = b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";
    let mut bytes = b"QklFMQ".to_vec();
    let mut x = 0x2545_f491_4f6c_dd1du64;
    for _ in 0..8000 {
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        bytes.push(ALPHABET[usize::try_from(x >> 58).expect("six bits")]);
    }
    let path =
        std::env::temp_dir().join(format!("borer_no_code_fixture_{}.bin", std::process::id()));
    std::fs::write(&path, &bytes).expect("the fixture is writable");
    let path = path.to_string_lossy().to_string();

    let (ok, out) = run_all(&["triage", &path]);
    assert!(ok, "triage refused a file with no code:\n{out}");
    assert!(out.contains("no code analysis applies"), "{out}");
    assert!(out.contains("# magic: Electrum encrypted wallet"), "{out}");
    assert!(
        out.lines()
            .any(|l| l.starts_with("0x0 ") && l.ends_with(" base64")),
        "{out}"
    );

    let (ok, out) = run_all(&["functions", &path]);
    assert!(!ok, "functions should refuse a file with no code");
    assert!(
        out.contains("raw file") && out.contains("triage, entropy and strings"),
        "{out}"
    );

    drop(std::fs::remove_file(&path));
}

/// A file with no sections is read by file offset: `hexdump` and `read` take
/// `off:`, `search` reports its hits as `off=`, and an address is refused
/// with the offset form that reads the same bytes.
#[test]
fn cli_reads_a_file_with_no_sections_by_offset() {
    let mut bytes = vec![0x5au8; 0x40];
    bytes[0x20..0x27].copy_from_slice(b"needle\0");
    let path = std::env::temp_dir().join(format!(
        "borer_raw_reads_fixture_{}.bin",
        std::process::id()
    ));
    std::fs::write(&path, &bytes).expect("the fixture is writable");
    let path = path.to_string_lossy().to_string();

    let (ok, out) = run_all(&["hexdump", &path, "off:0x20", "16"]);
    assert!(ok, "{out}");
    assert!(out.starts_with("# off 0x20..0x30"), "{out}");
    assert!(out.contains("|needle.ZZZZZZZZZ|"), "{out}");

    let (ok, out) = run_all(&["read", &path, "off=0x20", "cstr"]);
    assert!(ok, "{out}");
    assert!(out.contains("\"needle\" (len 6)"), "{out}");

    let (ok, out) = run_all(&["search", &path, "needle", "text"]);
    assert!(ok, "{out}");
    assert!(out.contains("off=0x20"), "{out}");

    let (ok, out) = run_all(&["hexdump", &path, "0x20"]);
    assert!(!ok, "an address in a file with no sections maps nothing");
    assert!(out.contains("off:0x0"), "{out}");

    drop(std::fs::remove_file(&path));
}

/// `--help` after a command, or `help <command>`, prints that command's usage
/// lines alone.
#[test]
fn cli_help_for_one_command() {
    let (ok, out) = run(&["strings", "--help"]);
    assert!(ok);
    assert!(out.contains("strings <binary>"), "{out}");
    assert!(
        !out.contains("info <binary>"),
        "the whole usage was printed:\n{out}"
    );
    let (ok, out) = run(&["help", "search"]);
    assert!(ok && out.contains("search <binary>"), "{out}");
}

/// `fieldrefs` lists the instructions touching an offset with their
/// functions, and an empty paging argument means the default.
#[test]
#[cfg_attr(
    not(windows),
    ignore = "reads borer's own build, pinned as the Windows x64 PE"
)]
fn cli_fieldrefs_names_each_site() {
    let exe = env!("CARGO_BIN_EXE_borer");
    let (ok, out) = run(&["fieldrefs", exe, "0x8", "", "", "5"]);
    assert!(ok, "fieldrefs failed:\n{out}");
    assert!(out.contains("sites touch [reg+0x8]"), "{out}");
    assert_eq!(
        out.lines().nth(1),
        Some("va\tfunction\top\tbase\twidth\tdir\timm"),
        "{out}"
    );
    assert!(out.lines().count() <= 7, "the limit was ignored:\n{out}");
}

/// `search` hits name the function each one lands in.
#[test]
#[cfg_attr(
    not(windows),
    ignore = "reads borer's own build, pinned as the Windows x64 PE"
)]
fn cli_search_hits_carry_functions() {
    let exe = env!("CARGO_BIN_EXE_borer");
    let (ok, out) = run(&["search", exe, "c3"]);
    assert!(ok, "{out}");
    assert!(out.contains("# function: va ..."), "{out}");
}

/// `vslot` answers with the table header even when no class has a literal
/// virtual at the slot, and refuses a slot that is not an index.
#[test]
#[cfg_attr(
    not(windows),
    ignore = "reads borer's own build, pinned as the Windows x64 PE"
)]
fn cli_vslot_lists_constant_virtuals() {
    let exe = env!("CARGO_BIN_EXE_borer");
    let (ok, out) = run(&["vslot", exe, "0"]);
    assert!(ok, "vslot failed:\n{out}");
    assert!(
        out.contains("classes answer virtual 0 with a constant"),
        "{out}"
    );
    assert_eq!(out.lines().nth(1), Some("value\tclass\tfunction"), "{out}");
    let (ok, _) = run(&["vslot", exe, "three"]);
    assert!(!ok, "a slot that is not an index should fail");
}

/// `grep` refuses an empty text before it touches the index, and `index`
/// and `grep` have usage lines of their own.
#[test]
#[cfg_attr(
    not(windows),
    ignore = "reads borer's own build, pinned as the Windows x64 PE"
)]
fn cli_grep_refuses_an_empty_text() {
    let exe = env!("CARGO_BIN_EXE_borer");
    let (ok, _) = run(&["grep", exe, ""]);
    assert!(!ok, "an empty text should be refused");
    let (ok, out) = run(&["help", "grep"]);
    assert!(ok && out.contains("grep <binary> <text>"), "{out}");
    let (ok, out) = run(&["help", "index"]);
    assert!(ok && out.contains("index <binary>"), "{out}");
}

/// `schema` has a usage line, and refuses a name that is neither a function
/// nor a class.
#[test]
#[cfg_attr(
    not(windows),
    ignore = "reads borer's own build, pinned as the Windows x64 PE"
)]
fn cli_schema_refuses_what_reads_nothing() {
    let exe = env!("CARGO_BIN_EXE_borer");
    let (ok, out) = run(&["help", "schema"]);
    assert!(ok && out.contains("schema <binary>"), "{out}");
    let (ok, _) = run(&["schema", exe, "No::Such::Class"]);
    assert!(!ok, "an unknown name should fail");
}

/// `schemas` answers with its table header even when no class carries a
/// constant at the slot, and has a usage line.
#[test]
#[cfg_attr(
    not(windows),
    ignore = "reads borer's own build, pinned as the Windows x64 PE"
)]
fn cli_schemas_lists_a_protocol() {
    let exe = env!("CARGO_BIN_EXE_borer");
    let (ok, out) = run(&["schemas", exe, "0"]);
    assert!(ok, "schemas failed:\n{out}");
    assert!(
        out.contains("classes answer virtual 0 with a constant"),
        "{out}"
    );
    assert_eq!(
        out.lines().nth(1),
        Some("value\tclass\tdecoder\treads\tfields"),
        "{out}"
    );
    let (ok, out) = run(&["help", "schemas"]);
    assert!(ok && out.contains("schemas <binary> <slot>"), "{out}");
}

/// `shape` lists at least the function itself, with the table header.
#[test]
#[cfg_attr(
    not(windows),
    ignore = "reads borer's own build, pinned as the Windows x64 PE"
)]
fn cli_shape_lists_siblings() {
    let exe = env!("CARGO_BIN_EXE_borer");
    let (ok, fns) = run(&["functions", exe, "", "0", "1"]);
    assert!(ok, "{fns}");
    let entry = fns
        .lines()
        .find(|l| l.starts_with("0x"))
        .and_then(|l| l.split_whitespace().next())
        .expect("one function")
        .to_owned();
    let (ok, out) = run(&["shape", exe, &entry, "5"]);
    assert!(ok, "shape failed:\n{out}");
    assert!(out.contains("functions share the shape of"), "{out}");
    assert_eq!(
        out.lines().nth(1),
        Some("entry\tname\tstrings\tdata"),
        "{out}"
    );
}

/// `messages` answers with its table header even when nothing registered a
/// wire id.
#[test]
#[cfg_attr(
    not(windows),
    ignore = "reads borer's own build, pinned as the Windows x64 PE"
)]
fn cli_messages_lists_registered_classes() {
    let exe = env!("CARGO_BIN_EXE_borer");
    let (ok, out) = run(&["messages", exe]);
    assert!(ok, "messages failed:\n{out}");
    assert!(out.contains("classes registered a wire id"), "{out}");
    assert_eq!(
        out.lines().nth(1),
        Some("code\tclass\tfields\tid\thandlers\tregistered_in"),
        "{out}"
    );
}

/// `anchors` re-derives a function anchor to held, reports an unknown name
/// gone, and fails when anything did not hold.
#[test]
#[cfg_attr(
    not(windows),
    ignore = "reads borer's own build, pinned as the Windows x64 PE"
)]
fn cli_anchors_judges_a_manifest() {
    let exe = env!("CARGO_BIN_EXE_borer");
    let (ok, fns) = run(&["functions", exe, "", "0", "1"]);
    assert!(ok, "{fns}");
    let row = fns
        .lines()
        .find(|l| l.starts_with("0x"))
        .expect("one function");
    let mut cols = row.split_whitespace();
    let entry = cols.next().expect("entry");
    let name = cols.last().expect("name");
    let (ok, info) = run(&["info", exe]);
    assert!(ok, "{info}");
    let base = info
        .lines()
        .find_map(|l| l.trim().strip_prefix("base:"))
        .and_then(|b| b.split_whitespace().next())
        .expect("image base in info");
    let va = u64::from_str_radix(entry.trim_start_matches("0x"), 16).expect("hex entry");
    let base = u64::from_str_radix(base.trim_start_matches("0x"), 16).expect("hex base");
    let manifest = std::env::temp_dir().join(format!("borer_anchors_{}.tsv", std::process::id()));
    std::fs::write(
        &manifest,
        format!(
            "# pins\nfunction {name} {:#x}\nfunction no_such_function_xyz 0x1\n",
            va - base
        ),
    )
    .expect("manifest written");
    let (ok, out) = run(&["anchors", exe, &manifest.to_string_lossy()]);
    std::fs::remove_file(&manifest).ok();
    assert!(!ok, "a gone anchor must fail the command:\n{out}");
    assert!(
        out.contains("# 2 anchors: 1 held, 0 moved, 0 changed, 1 gone"),
        "{out}"
    );
    assert!(out.contains("\tgone\n"), "{out}");
}

/// `grep` refuses an expression that does not parse before it analyses or
/// indexes anything, quoting the parser.
#[test]
#[cfg_attr(
    not(windows),
    ignore = "reads borer's own build, pinned as the Windows x64 PE"
)]
fn cli_grep_refuses_a_broken_expression() {
    let exe = env!("CARGO_BIN_EXE_borer");
    let (ok, out) = run_all(&["grep", exe, "re:["]);
    assert!(!ok, "{out}");
    assert!(out.contains("bad regular expression"), "{out}");
}

/// `encode` has a usage line and refuses a name that is neither a
/// function nor a class; `encodes` answers with its table header even when
/// no class carries a constant at the slot.
#[test]
#[cfg_attr(
    not(windows),
    ignore = "reads borer's own build, pinned as the Windows x64 PE"
)]
fn cli_encodes_lists_the_outbound_protocol() {
    let exe = env!("CARGO_BIN_EXE_borer");
    let (ok, out) = run(&["help", "encode"]);
    assert!(ok && out.contains("encode <binary>"), "{out}");
    let (ok, _) = run(&["encode", exe, "No::Such::Class"]);
    assert!(!ok, "an unknown name should fail");
    let (ok, out) = run(&["encodes", exe, "0"]);
    assert!(ok, "encodes failed:\n{out}");
    assert!(
        out.contains("classes answer virtual 0 with a constant"),
        "{out}"
    );
    assert_eq!(
        out.lines().nth(1),
        Some("value\tclass\tencoder\twrites\tbits\tfields"),
        "{out}"
    );
}

/// `senders` answers with its table header even when no class carries a
/// constant at the slot, and has a usage line.
#[test]
#[cfg_attr(
    not(windows),
    ignore = "reads borer's own build, pinned as the Windows x64 PE"
)]
fn cli_senders_lists_who_constructs() {
    let exe = env!("CARGO_BIN_EXE_borer");
    let (ok, out) = run(&["senders", exe, "0"]);
    assert!(ok, "senders failed:\n{out}");
    assert!(
        out.contains("classes answer virtual 0 with a constant"),
        "{out}"
    );
    assert_eq!(
        out.lines().nth(1),
        Some("value\tclass\tfactory\tsenders"),
        "{out}"
    );
    let (ok, out) = run(&["help", "senders"]);
    assert!(ok && out.contains("senders <binary> <slot>"), "{out}");
}

/// `protocol` answers with its table header even when no class carries a
/// constant at the slot, and has a usage line.
#[test]
#[cfg_attr(
    not(windows),
    ignore = "reads borer's own build, pinned as the Windows x64 PE"
)]
fn cli_protocol_joins_the_tables() {
    let exe = env!("CARGO_BIN_EXE_borer");
    let (ok, out) = run(&["protocol", exe, "0"]);
    assert!(ok, "protocol failed:\n{out}");
    assert!(
        out.contains("classes answer virtual 0 with a constant:"),
        "{out}"
    );
    assert_eq!(
        out.lines().nth(1),
        Some("value\tclass\tsenders\thandler\tencodes\tdecodes"),
        "{out}"
    );
    let (ok, out) = run(&["help", "protocol"]);
    assert!(ok && out.contains("protocol <binary> <slot>"), "{out}");
}

/// `hooks` answers with its table header even when no class carries a
/// constant at the slot, and has a usage line.
#[test]
#[cfg_attr(
    not(windows),
    ignore = "reads borer's own build, pinned as the Windows x64 PE"
)]
fn cli_hooks_lists_addresses() {
    let exe = env!("CARGO_BIN_EXE_borer");
    let (ok, out) = run(&["hooks", exe, "0"]);
    assert!(ok, "hooks failed:\n{out}");
    assert!(
        out.contains("classes answer virtual 0 with a constant:"),
        "{out}"
    );
    assert_eq!(
        out.lines().nth(1),
        Some("value\tclass\tencoder\tdecoder\thandler\tsend_sites"),
        "{out}"
    );
    let (ok, out) = run(&["help", "hooks"]);
    assert!(ok && out.contains("hooks <binary> <slot>"), "{out}");
}

/// `attrs` answers with its table header on a binary with no attribute
/// registry, and has a usage line.
#[test]
#[cfg_attr(
    not(windows),
    ignore = "reads borer's own build, pinned as the Windows x64 PE"
)]
fn cli_attrs_lists_the_registry() {
    let exe = env!("CARGO_BIN_EXE_borer");
    let (ok, out) = run(&["attrs", exe]);
    assert!(ok, "attrs failed:\n{out}");
    assert!(out.contains("attributes registered through"), "{out}");
    assert!(
        out.contains("code\tname\ttype\taccess\tdefault\tusers\n"),
        "{out}"
    );
    let (ok, out) = run(&["help", "attrs"]);
    assert!(ok && out.contains("attrs <binary>"), "{out}");
}

/// `ports` answers with its table header on a binary with no message
/// ports, and has a usage line.
#[test]
#[cfg_attr(
    not(windows),
    ignore = "reads borer's own build, pinned as the Windows x64 PE"
)]
fn cli_ports_lists_routes() {
    let exe = env!("CARGO_BIN_EXE_borer");
    let (ok, out) = run(&["ports", exe]);
    assert!(ok, "ports failed:\n{out}");
    assert!(out.contains("ports accept"), "{out}");
    assert_eq!(
        out.lines().nth(1),
        Some("port\tmessage\thandler\tdispatch"),
        "{out}"
    );
    let (ok, out) = run(&["help", "ports"]);
    assert!(ok && out.contains("ports <binary>"), "{out}");
}

/// A pack in a pack directory loads by itself for a program its `[match]`
/// lines fit, `packs` says which do and why, and `--no-auto-packs` keeps
/// the directory out.
#[test]
#[cfg_attr(
    not(windows),
    ignore = "reads borer's own build, pinned as the Windows x64 PE"
)]
fn cli_packs_load_themselves_by_their_match() {
    let exe = env!("CARGO_BIN_EXE_borer");
    let dir = std::env::temp_dir().join(format!("borer_packdir_{}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("makes the directory");
    std::fs::write(
        dir.join("fits.borer"),
        "pack fits 2\n[match]\nsection .text\n[naming]\nsingleton Only\n",
    )
    .expect("writes the pack");
    std::fs::write(
        dir.join("misses.borer"),
        "pack misses 1\n[match]\nsection .no_such_section\n",
    )
    .expect("writes the pack");
    let run_in = |args: &[&str]| {
        let _slot = Slot::take();
        let out = Command::new(exe)
            .arg("--no-pdb")
            .args(args)
            .env("BORER_PACK_DIRS", &dir)
            .env_remove("BORER_AUTO_PACKS")
            .output()
            .expect("spawn borer.exe");
        (
            out.status.success(),
            String::from_utf8_lossy(&out.stdout).to_string(),
            String::from_utf8_lossy(&out.stderr).to_string(),
        )
    };
    let (ok, out, _) = run_in(&["packs", exe]);
    assert!(ok, "packs failed:\n{out}");
    assert!(out.contains("pack\tversion\tfile\tloads\tmatch\n"), "{out}");
    assert!(out.contains("\tyes\tsection .text\n"), "{out}");
    assert!(
        out.contains("\tno\tfails section .no_such_section\n"),
        "{out}"
    );
    let (ok, _, err) = run_in(&["info", exe]);
    assert!(ok, "info failed:\n{err}");
    assert!(err.contains("pack fits 2 from"), "{err}");
    assert!(!err.contains("pack misses"), "{err}");
    let (ok, _, err) = run_in(&["info", exe, "--no-auto-packs"]);
    assert!(ok && !err.contains("pack fits"), "{err}");
    let (ok, out) = run(&["help", "packs"]);
    assert!(ok && out.contains("packs <binary>"), "{out}");
}

/// `export-pack` writes a project's names as a pack of signatures, and the
/// pack loaded back names the same functions.
///
/// Which functions the project names is incidental — the first unnamed ones
/// the listing happens to offer — and a signature is only written when the
/// function's first bytes are unique in the program, so a batch of three can
/// come back unsigned when this build's first candidates share a prologue
/// with something else. The picker therefore works through the candidates in
/// batches of three until a batch exports; the round trip it then asserts is
/// the same one.
#[test]
#[cfg_attr(
    not(windows),
    ignore = "reads borer's own build, pinned as the Windows x64 PE"
)]
fn cli_export_pack_round_trips() {
    let exe = env!("CARGO_BIN_EXE_borer");
    let (ok, out) = run(&["functions", exe, "", "0", "400"]);
    assert!(ok, "functions failed:\n{out}");
    let mut sizes = std::collections::BTreeSet::new();
    let candidates: Vec<&str> = out
        .lines()
        .filter(|l| !l.starts_with('#'))
        .filter_map(|l| {
            let mut words = l.split_whitespace();
            let entry = words.next()?;
            let size = words.next()?.parse::<u64>().ok()?;
            let unnamed = words.last().is_some_and(|n| n.starts_with("sub_"));
            (unnamed && size >= 64 && sizes.insert(size)).then_some(entry)
        })
        .take(24)
        .collect();
    assert!(candidates.len() >= 3, "{out}");
    let dir = std::env::temp_dir();
    let project = dir.join(format!("borer_export_{}.json", std::process::id()));
    let mut pack = String::new();
    for batch in candidates.chunks(3) {
        let names: Vec<String> = batch
            .iter()
            .enumerate()
            .map(|(i, e)| format!("\"{e}\": \"Exported::f{i}\""))
            .collect();
        std::fs::write(
            &project,
            format!(
                "{{\"program\": \"x\", \"names\": {{{}}}, \"comments\": {{}}}}",
                names.join(", ")
            ),
        )
        .expect("writes the project");
        let project = project.to_string_lossy().to_string();
        let (ok, out) = run(&["export-pack", exe, "roundtrip", &project]);
        assert!(ok, "export-pack failed:\n{out}");
        assert!(out.contains("\npack roundtrip 1\n"), "{out}");
        if out.lines().any(|l| l.starts_with("fn ")) {
            pack = out;
            break;
        }
    }
    assert!(
        !pack.is_empty(),
        "no batch of candidates exported a signature"
    );
    let signed = pack.lines().filter(|l| l.starts_with("fn ")).count();
    assert!(signed >= 1, "{pack}");
    let file = dir.join(format!("borer_export_{}.borer", std::process::id()));
    std::fs::write(&file, &pack).expect("writes the pack");
    let file = file.to_string_lossy().to_string();
    let (ok, out) = run(&["packs", exe, "--pack", &file]);
    assert!(ok, "packs failed:\n{out}");
    assert!(
        out.contains(&format!(
            "# pack names: {signed} of {signed} named a function"
        )),
        "{out}"
    );
    let (ok, out) = run(&["functions", exe, "Exported::", "0", "10", "--pack", &file]);
    assert!(ok, "functions failed:\n{out}");
    assert!(out.contains(" pack Exported::f"), "{out}");
}

/// `script` runs the shipped example scripts over borer.exe: one lists an
/// import's callers, one groups imports for triage and comments their
/// users, and `--save` writes the proposals as a project.
#[test]
#[cfg_attr(
    not(windows),
    ignore = "reads borer's own build, pinned as the Windows x64 PE"
)]
fn cli_script_runs_the_examples() {
    let exe = env!("CARGO_BIN_EXE_borer");
    let root = concat!(env!("CARGO_MANIFEST_DIR"), "/../../packs/scripts/");
    let (ok, out) = run(&[
        "script",
        exe,
        &format!("{root}callers_of.rhai"),
        "GetProcAddress",
    ]);
    assert!(ok, "script failed:\n{out}");
    assert!(out.contains("GetProcAddress at 0x"), "{out}");
    assert!(
        out.contains("# script: 0 names and 0 comments proposed"),
        "{out}"
    );
    let project = std::env::temp_dir().join(format!("borer_script_{}.json", std::process::id()));
    let project = project.to_string_lossy().to_string();
    let (ok, out) = run(&[
        "script",
        exe,
        &format!("{root}suspicious_apis.rhai"),
        "--save",
        &project,
    ]);
    assert!(ok, "script failed:\n{out}");
    assert!(out.contains("run-time loading: "), "{out}");
    assert!(out.contains("\ncomment\t0x"), "{out}");
    let saved = std::fs::read_to_string(&project).expect("the project was written");
    assert!(saved.contains("uses run-time loading APIs"), "{saved}");
    let (ok, out) = run(&["script", exe, &format!("{root}name_by_strings.rhai")]);
    assert!(ok, "script failed:\n{out}");
    assert!(out.contains("functions by the one qualified name"), "{out}");
    let (ok, out) = run_all(&["script", exe, &format!("{root}no_such.rhai")]);
    assert!(!ok && out.contains("no_such.rhai"), "{out}");
}

/// A directory pack's script runs with the analysis: it names the entry
/// function, `functions` lists the name, and `packs` reports the run.
#[test]
#[cfg_attr(
    not(windows),
    ignore = "reads borer's own build, pinned as the Windows x64 PE"
)]
fn cli_a_pack_script_names_with_the_analysis() {
    let exe = env!("CARGO_BIN_EXE_borer");
    let dir = std::env::temp_dir().join(format!("borer_scriptpack_{}", std::process::id()));
    std::fs::create_dir_all(dir.join("rules")).expect("makes the directory");
    std::fs::write(
        dir.join("self.borer"),
        "pack selfnamer 1\n[match]\nsection .text\n[scripts]\nrun rules/entry.rhai\n",
    )
    .expect("writes the pack");
    std::fs::write(
        dir.join("rules").join("entry.rhai"),
        "let e = program().entry;\nrename(e, \"Borer::EntryFromScript\");\nprint(`named ${hex(e)}`);\n",
    )
    .expect("writes the script");
    let run_in = |args: &[&str]| {
        let _slot = Slot::take();
        let out = Command::new(exe)
            .arg("--no-pdb")
            .args(args)
            .env("BORER_PACK_DIRS", &dir)
            .env_remove("BORER_AUTO_PACKS")
            .output()
            .expect("spawn borer.exe");
        (
            out.status.success(),
            String::from_utf8_lossy(&out.stdout).to_string(),
        )
    };
    let (ok, out) = run_in(&["packs", exe]);
    assert!(ok, "packs failed:\n{out}");
    assert!(
        out.contains("# pack scripts: 1 ran, 0 failed, 1 functions named"),
        "{out}"
    );
    assert!(out.contains("rules"), "{out}");
    let (ok, out) = run_in(&["functions", exe, "EntryFromScript"]);
    assert!(ok, "functions failed:\n{out}");
    assert!(out.contains(" pack Borer::EntryFromScript"), "{out}");
}

/// `scenario` decompiles under assumptions and says what it cut, and
/// refuses a scenario that names no parameter.
#[test]
#[cfg_attr(
    not(windows),
    ignore = "reads borer's own build, pinned as the Windows x64 PE"
)]
fn cli_scenario_states_its_assumptions() {
    let exe = env!("CARGO_BIN_EXE_borer");
    let (ok, info) = run(&["info", exe]);
    assert!(ok, "info failed:\n{info}");
    let entry = info
        .lines()
        .find_map(|l| l.split("entry: ").nth(1))
        .and_then(|e| e.split_whitespace().next())
        .unwrap_or_default()
        .to_owned();
    let (ok, out) = run(&["scenario", exe, &entry, "a1=0"]);
    assert!(ok, "scenario failed:\n{out}");
    assert!(out.starts_with("// scenario: a1 = 0; "), "{out}");
    assert!(out.contains("blocks cannot run"), "{out}");
    let (ok, out) = run_all(&["scenario", exe, &entry, "x=1"]);
    assert!(!ok && out.contains("is not a parameter"), "{out}");
    let (ok, out) = run(&["scenarios", exe, &entry, "a1=0..3"]);
    assert!(ok, "scenarios failed:\n{out}");
    assert!(out.starts_with("# a1 over 3 values: "), "{out}");
    assert!(out.contains("\nvalues\tkept\tcalls\treturns\n"), "{out}");
}

/// `verify` checks functions' blocks against the emulator and reports
/// what it compared, with a row per disagreement.
#[test]
#[cfg_attr(
    not(windows),
    ignore = "reads borer's own build, pinned as the Windows x64 PE"
)]
fn cli_verify_checks_the_lifter() {
    let exe = env!("CARGO_BIN_EXE_borer");
    let (ok, out) = run(&["verify", exe, "all", "40"]);
    assert!(
        ok,
        "verify failed:
{out}"
    );
    assert!(out.starts_with("# verified 40 functions, "), "{out}");
    assert!(
        out.contains(
            "
function	block	fact	place	emulated	lifted	bits	expression
"
        ),
        "{out}"
    );
    let (ok, out) = run(&["help", "verify"]);
    assert!(ok && out.contains("verify <binary>"), "{out}");
}

/// `verify ... text` replays the text's statements against the emulator
/// and reports what it compared, with a row per disagreement; it fails
/// only on a disagreement, and says so.
#[test]
#[cfg_attr(
    not(windows),
    ignore = "reads borer's own build, pinned as the Windows x64 PE"
)]
fn cli_verify_text_checks_the_statements() {
    let exe = env!("CARGO_BIN_EXE_borer");
    let (ok, out) = run(&["verify", exe, "all", "40", "1", "text"]);
    assert!(
        ok || out.contains("the text and the emulator disagree"),
        "{out}"
    );
    assert!(out.starts_with("# replayed 40 functions, "), "{out}");
    assert!(out.contains("\n# branch: "), "{out}");
    assert!(
        out.contains(
            "\nfunction\tblock\tat\tclaim\tplace\ttext\tmachine\tbits\tlane\texpression\n"
        ),
        "{out}"
    );
}

/// `map` answers with its overview header, a column per role found, and
/// has a usage line.
#[test]
#[cfg_attr(
    not(windows),
    ignore = "reads borer's own build, pinned as the Windows x64 PE"
)]
fn cli_map_lays_out_namespaces() {
    let exe = env!("CARGO_BIN_EXE_borer");
    let (ok, out) = run(&["map", exe]);
    assert!(ok, "map failed:\n{out}");
    assert!(out.contains("namespaces, showing"), "{out}");
    let header = out.lines().nth(1).unwrap_or_default();
    assert!(
        header.starts_with("namespace\tclasses\t") && header.ends_with("\tsingletons\tmethods"),
        "{out}"
    );
    let (ok, out) = run(&["help", "map"]);
    assert!(ok && out.contains("map <binary>"), "{out}");
}

/// `about` finds a function by its name and says so, says when nothing has
/// the name, and has a usage line.
#[test]
#[cfg_attr(
    not(windows),
    ignore = "reads borer's own build, pinned as the Windows x64 PE"
)]
fn cli_about_answers_one_name() {
    let exe = env!("CARGO_BIN_EXE_borer");
    let (ok, out) = run(&["about", exe, "no_such_name_xyz"]);
    assert!(ok, "about failed:\n{out}");
    assert!(out.starts_with("# nothing is named"), "{out}");
    let (ok, fns) = run(&["functions", exe, "", "0", "1"]);
    assert!(ok, "{fns}");
    let row = fns
        .lines()
        .find(|l| l.starts_with("0x"))
        .expect("one function");
    let name = row.split_whitespace().last().expect("name");
    let (ok, out) = run(&["about", exe, name]);
    assert!(ok, "{out}");
    assert!(out.contains("## function "), "{out}");
    let (ok, out) = run(&["help", "about"]);
    assert!(ok && out.contains("about <binary> <name>"), "{out}");
}

/// `set-type` writes a struct into a project and applies it at a data
/// global.
///
/// `types` lists both, a type the language does not spell and one naming
/// nothing defined are refused with nothing written, and each command has
/// a usage line.
#[test]
#[cfg_attr(
    not(windows),
    ignore = "reads borer's own build, pinned as the Windows x64 PE"
)]
fn cli_set_type_defines_applies_and_refuses() {
    let exe = env!("CARGO_BIN_EXE_borer");
    let dir = std::env::temp_dir().join(format!("borer-settype-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let project = dir.join("p.json");
    let project = project.to_str().unwrap();
    let _ = std::fs::remove_file(project);

    let (ok, out) = run(&[
        "set-type",
        exe,
        project,
        "struct",
        "Player",
        "0x18:hp:u32",
        "0x1c:mp:u32",
        "0x20:target:Player *",
    ]);
    assert!(ok, "set-type failed:\n{out}");
    assert!(
        out.contains("defined struct Player: 3 field(s), 0x28 byte(s)"),
        "{out}"
    );

    // An import slot is a data global: applying there types it.
    let (ok, out) = run(&["symbols", exe]);
    assert!(ok, "{out}");
    let slot = out
        .lines()
        .find_map(|l| l.strip_prefix("import 0x"))
        .and_then(|r| r.split(' ').next())
        .unwrap_or_default();
    assert!(!slot.is_empty(), "no import listed:\n{out}");
    let applied = format!("0x{slot}");
    let (ok, out) = run(&["set-type", exe, project, "apply", &applied, "Player *"]);
    assert!(ok, "apply failed:\n{out}");
    assert!(out.contains("applied Player *"), "{out}");

    let (ok, out) = run(&["types", exe, project]);
    assert!(ok, "types failed:\n{out}");
    assert!(out.contains("struct\tPlayer\t0x28"), "{out}");
    assert!(out.contains("0x18 hp u32"), "{out}");
    assert!(
        out.contains(&format!("applied\t{applied}\t-\tPlayer *")),
        "{out}"
    );

    let (ok, out) = run_all(&["set-type", exe, project, "typedef", "Bad", "three words"]);
    assert!(!ok, "garbage accepted:\n{out}");
    assert!(out.contains("is not one"), "{out}");
    let (ok, out) = run_all(&["set-type", exe, project, "struct", "S", "0x0:f:Missing *"]);
    assert!(!ok, "unknown field type accepted:\n{out}");
    assert!(out.contains("resolves to no size"), "{out}");
    let (ok, out) = run_all(&["set-type", exe, project, "apply", &applied, "Nope *"]);
    assert!(!ok, "unknown applied type accepted:\n{out}");
    assert!(out.contains("names nothing defined"), "{out}");

    // The refusals wrote nothing: the listing still holds what did land.
    let (ok, out) = run(&["types", exe, project, "", "0", "1"]);
    assert!(ok, "{out}");
    assert!(out.contains("2 rows"), "{out}");

    let (ok, out) = run(&["help", "set-type"]);
    assert!(ok && out.contains("set-type <binary> <project>"), "{out}");
    let (ok, out) = run(&["help", "types"]);
    assert!(ok && out.contains("types <binary> [project]"), "{out}");

    drop(std::fs::remove_file(project));
}

/// `set-type enum` writes an enum into a project and applies it at a data
/// global.
///
/// `types` lists its values in value order; duplicate names, duplicate
/// values and a width that is not 4 or 8 are refused with nothing written.
#[test]
#[cfg_attr(
    not(windows),
    ignore = "reads borer's own build, pinned as the Windows x64 PE"
)]
fn cli_set_type_defines_enums_and_refuses() {
    let exe = env!("CARGO_BIN_EXE_borer");
    let dir = std::env::temp_dir().join(format!("borer-setenum-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let project = dir.join("p.json");
    let project = project.to_str().unwrap();
    let _ = std::fs::remove_file(project);

    let (ok, out) = run(&[
        "set-type", exe, project, "enum", "State", "4", "Run:1", "Done:2", "Idle:0",
    ]);
    assert!(ok, "set-type failed:\n{out}");
    assert!(
        out.contains("defined enum State: 3 value(s), 0x4 byte(s)"),
        "{out}"
    );

    let (ok, out) = run(&["symbols", exe]);
    assert!(ok, "{out}");
    let slot = out
        .lines()
        .find_map(|l| l.strip_prefix("import 0x"))
        .and_then(|r| r.split(' ').next())
        .unwrap_or_default();
    assert!(!slot.is_empty(), "no import listed:\n{out}");
    let applied = format!("0x{slot}");
    let (ok, out) = run(&["set-type", exe, project, "apply", &applied, "State"]);
    assert!(ok, "apply failed:\n{out}");
    assert!(
        out.contains("applied State at") && out.contains("decompile names its values"),
        "{out}"
    );

    let (ok, out) = run(&["types", exe, project]);
    assert!(ok, "types failed:\n{out}");
    assert!(out.contains("enum\tState\t0x4"), "{out}");
    assert!(out.contains("Idle = 0, Run = 1, Done = 2"), "{out}");

    let (ok, out) = run_all(&["set-type", exe, project, "enum", "Bad", "A:0", "B:0"]);
    assert!(!ok, "a duplicate value accepted:\n{out}");
    assert!(out.contains("names value 0 twice"), "{out}");
    let (ok, out) = run_all(&["set-type", exe, project, "enum", "Bad", "A:0", "A:1"]);
    assert!(!ok, "a duplicate name accepted:\n{out}");
    assert!(out.contains("two values named A"), "{out}");
    let (ok, out) = run_all(&["set-type", exe, project, "enum", "Bad", "3", "A:0"]);
    assert!(!ok, "an odd width accepted:\n{out}");
    assert!(out.contains("4 or 8 wide"), "{out}");

    // The refusals wrote nothing: the listing still holds what did land.
    let (ok, out) = run(&["types", exe, project, "", "0", "1"]);
    assert!(ok, "types failed:\n{out}");
    assert!(out.contains("2 rows"), "{out}");

    drop(std::fs::remove_file(project));
}

/// A snapshot of a binary compared with the same binary changes nothing,
/// and a file that is not a snapshot is refused.
#[test]
#[cfg_attr(
    not(windows),
    ignore = "reads borer's own build, pinned as the Windows x64 PE"
)]
fn cli_snapshot_compares_to_itself() {
    let exe = env!("CARGO_BIN_EXE_borer");
    let file = std::env::temp_dir().join(format!("borer_snapshot_{}.tsv", std::process::id()));
    let path = file.to_string_lossy().to_string();
    let (ok, out) = run(&["snapshot", exe, &path]);
    assert!(ok, "snapshot failed:\n{out}");
    assert!(out.starts_with("wrote "), "{out}");
    let (ok, out) = run(&["changes", exe, &path]);
    std::fs::remove_file(&file).ok();
    assert!(ok, "changes failed:\n{out}");
    assert!(out.starts_with("# 0 changes across"), "{out}");
    let (ok, _) = run(&["changes", exe, exe]);
    assert!(!ok, "a binary is not a snapshot");
}

/// A pack reads back its name, keys and warnings; `pack-keys` lists what a
/// pack can set; `--pack` loads one for any command and a file that is not
/// a pack is refused.
#[test]
#[cfg_attr(
    not(windows),
    ignore = "reads borer's own build, pinned as the Windows x64 PE"
)]
fn cli_packs_read_list_and_load() {
    let exe = env!("CARGO_BIN_EXE_borer");
    let dir = std::env::temp_dir();
    let good = dir.join(format!("borer_pack_{}.borer", std::process::id()));
    let bad = dir.join(format!("borer_notpack_{}.borer", std::process::id()));
    std::fs::write(
        &good,
        "pack testpack 3\nabout a test\n[naming]\nsingleton Only\n[roles]\nclass A::B thing\nunknown x\n",
    )
    .expect("writes the pack");
    std::fs::write(&bad, "[naming]\nsingleton x\n").expect("writes the file");
    let good_path = good.to_string_lossy().to_string();
    let bad_path = bad.to_string_lossy().to_string();
    let (ok, out) = run(&["pack", &good_path]);
    assert!(ok, "pack failed:\n{out}");
    assert!(
        out.starts_with("# pack testpack 3: 3 lines in 3 keys, 1 warnings"),
        "{out}"
    );
    assert!(out.contains("naming\tsingleton\t1"), "{out}");
    let (ok, out) = run(&["pack-keys"]);
    assert!(ok, "pack-keys failed:\n{out}");
    assert!(
        out.contains("naming\tsingleton\tsingle\tinstance\t"),
        "{out}"
    );
    let (ok, out) = run(&["info", exe, "--pack", &good_path]);
    assert!(ok, "info with a pack failed:\n{out}");
    let (ok, _) = run(&["info", exe, "--pack", &bad_path]);
    std::fs::remove_file(&good).ok();
    std::fs::remove_file(&bad).ok();
    assert!(!ok, "a file that is not a pack loads");
}

/// `--arch` with `--regions` maps a two-part dump where the command line
/// says.
///
/// The queries then read it like any image; without `--arch` the same
/// file has no code, and a region past the end of the file or a layout
/// flag on a command that reads no binary is refused.
#[test]
fn cli_maps_a_dump_at_stated_regions() {
    let mut bytes = vec![0xcc_u8; 0x30];
    // ASM: mov eax, dword ptr [0x20000]; ret
    bytes[..8].copy_from_slice(&[0x8b, 0x04, 0x25, 0x00, 0x00, 0x02, 0x00, 0xc3]);
    bytes[0x20..0x24].copy_from_slice(&42u32.to_le_bytes());
    let path = std::env::temp_dir().join(format!("borer_dump_fixture_{}.bin", std::process::id()));
    std::fs::write(&path, &bytes).expect("the fixture is writable");
    let path = path.to_string_lossy().to_string();
    let regions = "0x10000@0:0x20:rx,0x20000@0x20:0x10:rw";

    let (ok, info) = run_all(&["info", &path, "--arch", "x64", "--regions", regions]);
    let (emulated, ran) = run_all(&[
        "emulate",
        &path,
        "0x10000",
        "--arch=x64",
        "--regions",
        regions,
    ]);
    let (plain, unmapped) = run_all(&["functions", &path]);
    let (past, refusal) = run_all(&["info", &path, "--arch", "x64", "--regions", "0@0:0x31"]);
    let (stray, stray_refusal) = run_all(&["pack-keys", "--arch", "x64"]);
    drop(std::fs::remove_file(&path));

    assert!(ok, "{info}");
    assert!(info.contains("region1        0x20000"), "{info}");
    assert!(info.contains("kind stated layout"), "{info}");
    assert!(emulated && ran.contains("rax=0x2a "), "{ran}");
    assert!(!plain && unmapped.contains("raw file"), "{unmapped}");
    assert!(
        !past && refusal.contains("runs past the end of the file at 0x30"),
        "{refusal}"
    );
    assert!(
        !stray && stray_refusal.contains("pack-keys maps none"),
        "{stray_refusal}"
    );
}
