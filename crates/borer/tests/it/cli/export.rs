//! CLI tests for `export`, through the real argument path.

/// `export <binary> --split <dir>`, the usage `borer help` gives, writes
/// the split and its `MAP.tsv`.
///
/// The CLI's option filter held a list of the words beginning `--` that
/// queries read, apart from the parsers that read them; `--split` was
/// missing from it, so the documented line was refused as an unknown
/// option before `export` saw it. The parser's own tests called it
/// directly and never met the filter.
#[test]
fn cli_export_split_writes_the_split_and_its_map() {
    let pid = std::process::id();
    let pe = std::env::temp_dir().join(format!("borer_split_{pid}.exe"));
    let dir = std::env::temp_dir().join(format!("borer_split_{pid}"));
    std::fs::write(&pe, crate::contract::tiny_pe()).expect("pe");
    std::fs::remove_dir_all(&dir).ok();
    let (pe_s, dir_s) = (pe.to_string_lossy(), dir.to_string_lossy());
    let (ok, said) = super::run_all(&["export", &pe_s, "--split", &dir_s]);
    let mapped = dir.join("MAP.tsv").is_file();
    let (ok_eq, said_eq) = super::run_all(&["export", &pe_s, &format!("--split={dir_s}")]);
    let (ok_last, said_last) = super::run_all(&["export", &pe_s, "--split"]);
    std::fs::remove_file(&pe).ok();
    std::fs::remove_dir_all(&dir).ok();
    assert!(ok && mapped, "{said}");
    assert!(!ok_eq && said_eq.contains("export takes"), "{said_eq}");
    assert!(
        !ok_last && said_last.contains("--split needs the file to write"),
        "{said_last}"
    );
}

/// A split directory that holds anything is refused before the analysis.
///
/// The whole analysis ran first, so `export big.exe --split full_dir`
/// analysed everything and then refused. A raw file, whose analysis is
/// refused, shows the order: the directory's refusal comes first.
#[test]
fn cli_export_refuses_an_occupied_split_dir_before_the_analysis() {
    let pid = std::process::id();
    let raw = std::env::temp_dir().join(format!("borer_split_full_{pid}.bin"));
    let dir = std::env::temp_dir().join(format!("borer_split_full_{pid}"));
    std::fs::write(&raw, [0x5a_u8; 0x40]).expect("raw");
    std::fs::create_dir_all(&dir).expect("dir");
    std::fs::write(dir.join("kept.c"), "kept").expect("kept");
    let (raw_s, dir_s) = (raw.to_string_lossy(), dir.to_string_lossy());
    let (ok, said) = super::run_all(&["export", &raw_s, "--split", &dir_s]);
    let kept = std::fs::read_to_string(dir.join("kept.c")).unwrap_or_default();
    std::fs::remove_file(&raw).ok();
    std::fs::remove_dir_all(&dir).ok();
    assert!(!ok && said.contains("is not empty"), "{said}");
    assert_eq!(kept, "kept");
}

/// `export` with no binary, or with a flag in the binary's place, says it
/// needs the binary, with its own usage, before anything loads.
///
/// Reading export's flags early answered a bare `export` with "export needs
/// --c <out.c>, ...", and following that led to "unknown option '--c'".
#[test]
fn cli_export_needs_its_binary_before_its_flags() {
    for (args, reason) in [
        (
            &["export"][..],
            "export needs a binary path\nusage:\n  export",
        ),
        (
            &["export", "--split", "d"][..],
            "export needs a binary path before '--split'\nusage:\n  export",
        ),
    ] {
        let (ok, said) = super::run_all(args);
        assert!(!ok && said.contains(reason), "{args:?}: {said}");
        assert!(!said.contains("functions <binary>"), "{args:?}: {said}");
    }
}

/// A word beginning `--` that `export` does not read is refused before the
/// binary loads, with the words `export` takes.
#[test]
fn cli_export_refuses_an_unknown_flag_with_its_own_words() {
    let (ok, said) = super::run_all(&["export", "no_such_file.exe", "--bogus", "x"]);
    assert!(!ok, "{said}");
    assert!(
        said.contains("export takes") && said.contains("--split <dir>"),
        "{said}"
    );
    assert!(!said.contains("no_such_file"), "{said}");
}
