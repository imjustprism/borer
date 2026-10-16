//! CLI contract tests: an input that cannot be answered exits 1 with
//! `Error: <message>`, the same message the MCP resource refuses with, and
//! never a `#` line on a successful exit.

use std::process::{Command, Output};

/// Where the fixture is loaded.
const IMAGE_BASE: u64 = 0x1_4000_0000;

/// The fixture's one function, `ret`, as the CLI spells its address.
const ENTRY: &str = "0x140001000";

/// Writes `bytes` into `b` at `at`.
///
/// # Arguments
///
/// * `b` - The image.
/// * `at` - The file offset.
/// * `bytes` - What to write.
///
/// # Panics
///
/// When the bytes run past the image.
fn put(b: &mut [u8], at: usize, bytes: &[u8]) {
    b[at..at + bytes.len()].copy_from_slice(bytes);
}

/// A PE32+ whose `.text` at RVA 0x1000 starts with `ret`, entered there:
/// small enough that each run analyses it at once.
///
/// # Panics
///
/// When a header field falls outside the header page.
pub(crate) fn tiny_pe() -> Vec<u8> {
    /// The PE signature's file offset.
    const PE_AT: usize = 0x80;
    /// The optional header's file offset, after the signature and COFF header.
    const OPT: usize = PE_AT + 24;
    /// The section table's file offset, after a PE32+ optional header.
    const ROW: usize = OPT + 0xf0;
    let mut b = vec![0u8; 0x200];
    put(&mut b, 0, b"MZ");
    put(&mut b, 0x3c, &0x80u32.to_le_bytes());
    put(&mut b, PE_AT, b"PE\0\0");
    put(&mut b, PE_AT + 4, &0x8664u16.to_le_bytes());
    put(&mut b, PE_AT + 6, &1u16.to_le_bytes());
    put(&mut b, PE_AT + 20, &0xf0u16.to_le_bytes());
    put(&mut b, PE_AT + 22, &0x22u16.to_le_bytes());
    put(&mut b, OPT, &0x20bu16.to_le_bytes());
    put(&mut b, OPT + 16, &0x1000u32.to_le_bytes());
    put(&mut b, OPT + 24, &IMAGE_BASE.to_le_bytes());
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
    b.push(0xc3);
    b.resize(0x400, 0xcc);
    b
}

/// Runs the borer binary to completion.
///
/// # Arguments
///
/// * `args` - Command-line arguments after the program name.
///
/// # Errors
///
/// When the process cannot be spawned.
fn borer(args: &[&str]) -> std::io::Result<Output> {
    Command::new(env!("CARGO_BIN_EXE_borer"))
        .args(args)
        .output()
}

/// An input the CLI cannot answer exits 1 with `Error: ` and the message.
///
/// Each case is one the matrix found answered as a success, or refused
/// without saying which argument it meant; a run that answers still exits
/// 0 and reads its stop in words.
///
/// # Panics
///
/// When a refusal exits 0, says something else, or an answer fails.
#[test]
fn cli_refuses_what_it_cannot_answer() {
    let file = std::env::temp_dir().join(format!("borer_contract_{}.exe", std::process::id()));
    std::fs::write(&file, tiny_pe()).expect("the fixture is writable");
    let pe = file.to_string_lossy().to_string();
    let out_file = std::env::temp_dir().join(format!("borer_contract_{}.out", std::process::id()));
    let out = out_file.to_string_lossy().to_string();
    let steps = format!("{ENTRY},steps=abc");
    let directive = format!("{ENTRY},foo");
    let bytes = format!("{ENTRY},w0x1=zz");
    let zeroth = format!("{ENTRY},a0=1");
    let budget = format!("{ENTRY},budget=abc");
    let strict = format!("{ENTRY},strict");
    let unreadable = format!("{ENTRY}/zz");
    let unspecified = format!("{ENTRY},steps=0/1");
    let cases: Vec<(Vec<&str>, &str)> = vec![
        (vec!["why", &pe, "nowhere"], "cannot resolve nowhere"),
        (vec!["taint", &pe, "nowhere"], "cannot resolve nowhere"),
        (vec!["layout", &pe, "nowhere"], "cannot resolve nowhere"),
        (vec!["solve", &pe, "nowhere"], "cannot resolve nowhere"),
        (vec!["flat", &pe, "nowhere"], "cannot resolve nowhere"),
        (
            vec!["oracle", &pe, "nowhere"],
            "no discovered function at 'nowhere'",
        ),
        (vec!["emulate", &pe, "nowhere"], "cannot resolve nowhere"),
        (vec!["emulate", &pe, "0x1"], "nothing is mapped at 0x1;"),
        (vec!["emulate", &pe, &steps], "bad step count in steps=abc"),
        (
            vec!["emulate", &pe, &directive],
            "cannot read the directive foo",
        ),
        (vec!["emulate", &pe, &bytes], "bad write bytes in w0x1=zz"),
        (
            vec!["emulate", &pe, &zeroth],
            "a0=1: arguments count from one as the decompiler names them; a1 is the first",
        ),
        (vec!["run", &pe, "nowhere/1"], "cannot resolve nowhere"),
        (
            vec!["run", &pe, ENTRY],
            "run takes <function>[,steps=N]/<input>",
        ),
        (
            vec!["run", &pe, &unreadable],
            "cannot read the argument zz; use a number",
        ),
        (vec!["run", &pe, &unspecified], "steps is 1 to "),
        (vec!["unpack", &pe, "nowhere"], "no start address nowhere"),
        (vec!["unpack", &pe, &budget], "bad budget in budget=abc"),
        (
            vec!["unpack", &pe, &budget, &out],
            "bad budget in budget=abc",
        ),
        (
            vec!["unpack", &pe, &strict, &out],
            "writing the image runs best-effort",
        ),
        (
            vec!["about", &pe, ""],
            "about needs a name: an attribute, a class, or a function",
        ),
        (vec!["search", &pe, ""], "search needs a non-empty pattern"),
        (
            vec!["hexdump", &pe, ENTRY, "abc"],
            "hexdump length 'abc' is not a number",
        ),
        (
            vec!["entropy", &pe, "abc"],
            "entropy threshold 'abc' is not a number",
        ),
        (vec!["decompile", &pe], "decompile needs an address or name"),
        (
            vec!["snapshot", &pe, ""],
            "snapshot needs a file to write; the path is empty",
        ),
        (
            vec!["changes", &pe, ""],
            "changes needs a snapshot file; the path is empty",
        ),
        (
            vec!["script", &pe, ""],
            "script needs a script file; the path is empty",
        ),
        (
            vec!["index", &pe, "extra"],
            "index takes nothing after the binary, not 'extra'",
        ),
    ];
    for (args, message) in &cases {
        let run = borer(args).expect("borer runs");
        let stdout = String::from_utf8_lossy(&run.stdout);
        let stderr = String::from_utf8_lossy(&run.stderr);
        assert_eq!(run.status.code(), Some(1), "{args:?}: {stdout}{stderr}");
        assert!(
            stderr.contains(&format!("Error: {message}")),
            "{args:?}: {stderr}"
        );
        assert!(!stdout.starts_with('#'), "{args:?} answered: {stdout}");
    }
    let answered = borer(&["run", &pe, &format!("{ENTRY}/1;2")]).expect("borer runs");
    let rows = String::from_utf8_lossy(&answered.stdout);
    assert!(answered.status.success(), "{rows}");
    assert!(
        rows.contains(
            "
1	void	returned	1	-	agrees"
        ),
        "{rows}"
    );
    let run = borer(&["emulate", &pe, ENTRY]).expect("borer runs");
    let stdout = String::from_utf8_lossy(&run.stdout);
    std::fs::remove_file(&file).ok();
    assert!(!out_file.exists(), "a refused unpack wrote its image");
    assert!(run.status.success(), "{stdout}");
    assert!(stdout.contains(": returned after "), "{stdout}");
}

/// `doctor` answers one line per item of the setup without a binary, and
/// `offline` keeps it off the network; a word it does not take is refused.
///
/// # Panics
///
/// When the report has another shape, or the refusal exits 0.
#[test]
fn doctor_reports_the_setup_one_line_each() {
    let run = borer(&["doctor", "offline"]).expect("borer runs");
    let stdout = String::from_utf8_lossy(&run.stdout);
    assert!(run.status.success(), "{stdout}");
    let labels: Vec<&str> = stdout
        .lines()
        .filter_map(|l| l.split_whitespace().next())
        .collect();
    assert_eq!(
        labels,
        ["version", "toolchain", "symbols", "index", "mcp"],
        "{stdout}"
    );
    assert!(stdout.contains(", commit "), "{stdout}");
    assert!(stdout.contains("not checked (offline)"), "{stdout}");
    let refused = borer(&["doctor", "online"]).expect("borer runs");
    assert_eq!(refused.status.code(), Some(1));
    assert!(
        String::from_utf8_lossy(&refused.stderr)
            .contains("Error: doctor takes `offline` or nothing, not 'online'"),
        "{}",
        String::from_utf8_lossy(&refused.stderr)
    );
}

/// `setup` takes `--apply` or nothing, and refuses any other word before
/// it reads or writes a client's configuration.
///
/// # Panics
///
/// When the refusal exits 0, says something else, or reports a plan.
#[test]
fn setup_refuses_a_word_it_does_not_take() {
    let refused = borer(&["setup", "--yes"]).expect("borer runs");
    assert_eq!(refused.status.code(), Some(1));
    let stderr = String::from_utf8_lossy(&refused.stderr);
    assert!(
        stderr.contains("Error: setup takes `--apply` or nothing, not '--yes'"),
        "{stderr}"
    );
    assert!(refused.stdout.is_empty(), "it reported a plan: {stderr}");
}
