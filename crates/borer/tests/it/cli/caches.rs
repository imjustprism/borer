//! CLI tests for the symbol cache a load looks in.

/// A load that cannot use the symbol cache `BORER_SYMCACHE` names says
/// so, when the program names a companion PDB, and still loads.
///
/// The refusal was dropped, so a PDB cached for the build did not apply
/// and nothing said why.
#[test]
fn cli_load_notes_a_refused_symbol_cache() {
    if !cfg!(windows) {
        return;
    }
    let pe = std::env::temp_dir().join(format!("borer_symnote_{}.exe", std::process::id()));
    std::fs::write(&pe, crate::contract::tiny_pe_with_pdb("app.pdb")).expect("writable");
    let pe_s = pe.to_string_lossy();
    let share = r"\\host.invalid\s";
    let (ok, said) = crate::contract::run_env(None, &[("BORER_SYMCACHE", share)], &["info", &pe_s]);
    std::fs::remove_file(&pe).ok();
    assert!(ok, "{said}");
    assert!(
        said.contains("skipped the symbol cache: BORER_SYMCACHE: ")
            && said.contains("names a network share"),
        "{said}"
    );
}
