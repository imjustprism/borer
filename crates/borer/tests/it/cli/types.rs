//! CLI tests for the types `set-type` writes into a project.

use super::{run, run_all};

/// `set-type typedef` refuses the typedef that takes a chain past the cap
/// and leaves the project as it was, so the next command still loads it.
///
/// Only a name already defined was checked, so the 17th link of a chain
/// was written, and every later command refused the project.
#[test]
#[cfg_attr(
    not(windows),
    ignore = "reads borer's own build, pinned as the Windows x64 PE"
)]
fn cli_set_type_refuses_a_chain_of_typedefs_past_the_cap() {
    let exe = env!("CARGO_BIN_EXE_borer");
    let dir = std::env::temp_dir().join(format!("borer-chain-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let project = dir.join("p.json");
    let project = project.to_str().unwrap();
    drop(std::fs::remove_file(project));
    let (ok, out) = run(&["set-type", exe, project, "typedef", "T0", "u32"]);
    assert!(ok, "{out}");
    for k in 1..16 {
        let (name, to) = (format!("T{k}"), format!("T{}", k - 1));
        let (ok, out) = run(&["set-type", exe, project, "typedef", &name, &to]);
        assert!(ok, "{name}: {out}");
    }
    let (ok, out) = run_all(&["set-type", exe, project, "typedef", "T16", "T15"]);
    assert!(!ok, "a chain of 17 typedefs was written:\n{out}");
    assert!(
        out.contains("typedef 'T16' starts a chain of 17 typedefs; 16 is the most"),
        "{out}"
    );
    let (ok, out) = run(&["set-type", exe, project, "typedef", "U", "u8"]);
    assert!(ok, "the project no longer loads:\n{out}");
    drop(std::fs::remove_file(project));
}
