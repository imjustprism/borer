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
