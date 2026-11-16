//! Project files in the engine: which binary one belongs to, what a binary
//! admits of it, and the JSON a project file holds.

#![expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]

use std::cell::Cell;
use std::sync::Arc;

use borer_engine::analysis::edit::commit;
use borer_engine::analysis::project::{Project, admit, identity, program_identity};
use borer_engine::analysis::{Analysis, Overlay};
use borer_engine::program::{Arch, Program};

/// A project file stating names, comments, a struct, an enum and a
/// variable's type, as `save_project` wrote it before the file's form
/// moved into the engine.
const SAVED: &str = r#"{
  "program": "bin",
  "sha256": "ab",
  "names": {
    "0x140001000": "main"
  },
  "comments": {
    "0x140001004": "hi"
  },
  "types": {
    "E": {
      "Enum": {
        "size": 4,
        "values": [
          [
            1,
            "ONE"
          ]
        ]
      }
    },
    "S": {
      "Struct": {
        "size": 8,
        "fields": {
          "0": {
            "name": "a",
            "ty": "U32"
          },
          "4": {
            "name": "b",
            "ty": "U16"
          }
        }
      }
    }
  },
  "applied": {},
  "vars": {
    "0x140001000": {
      "a1": "S *p"
    }
  }
}"#;

/// A project file's JSON reads into an overlay and spells back from it
/// byte for byte as `save_project` wrote it.
#[test]
fn a_project_round_trips_through_its_json_byte_for_byte() {
    let read = Project::from_json(SAVED.as_bytes()).expect("the file reads");
    let overlay = read.to_overlay().expect("the overlay holds it");
    assert_eq!(
        overlay.names.get(&0x1_4000_1000).map(String::as_str),
        Some("main")
    );
    assert_eq!(overlay.types.len(), 2);
    assert_eq!(overlay.vars.len(), 1);
    let spelled = Project::from_overlay("bin", Some("ab".to_owned()), &overlay)
        .to_json()
        .expect("the file spells");
    assert_eq!(String::from_utf8_lossy(&spelled), SAVED);
}

/// A program of `bytes` loaded from `a.exe`.
///
/// # Arguments
///
/// * `bytes` - The file.
fn at_a(bytes: Vec<u8>) -> Program {
    let mut p = Program::raw(bytes, Arch::X86_64, 0, None, Vec::new());
    p.path = "a.exe".into();
    p
}

/// A project saved for another build is admitted only when forced.
///
/// Refused, it says what is wrong without the server's way out and never
/// asks for the analysis, even when it states fields; forced, it is said
/// to be forced, and commits.
#[test]
fn another_builds_project_is_admitted_only_when_forced() {
    let program = at_a(vec![0xc3; 64]);
    let other = identity(&[0x90; 64]);
    let file = Project {
        program: "a.exe".to_owned(),
        sha256: Some(other.clone()),
        ..Project::default()
    };
    let empty = || Ok(Arc::new(Analysis::default()));
    let fielded = Project {
        fields: [("C".to_owned(), [("0x0".to_owned(), "a".to_owned())].into())].into(),
        ..Project::from_overlay("a.exe", Some(other.clone()), &Overlay::default())
    };
    let asked = Cell::new(false);
    let analysis = || {
        asked.set(true);
        Ok(Arc::new(Analysis::default()))
    };
    let refused = admit(&program, analysis, &Overlay::default(), &fielded, false)
        .expect_err("another build's project was admitted")
        .to_string();
    assert!(!asked.get(), "a refused file asked for the analysis");
    assert!(!refused.contains("force=true"), "{refused}");
    assert_eq!(
        refused,
        format!(
            "the project was saved for another build (sha-256 {}... at a.exe), but a.exe is sha-256 {}...; nothing was loaded",
            &other[..12],
            &program_identity(&program)[..12]
        )
    );
    let forced = admit(&program, empty, &Overlay::default(), &file, true).expect("forced");
    assert_eq!(
        forced.said(),
        "loaded 0 names + 0 comments + 0 types + 0 applied\n# forced: the project was saved for a.exe, so its names may sit on other code here\n"
    );
    let mut overlay = Overlay::default();
    let (plan, _, _) = forced.into_parts();
    commit(&program, &Analysis::default(), &mut overlay, &plan).expect("it commits");
}

/// A file whose classes state no field is admitted without the analysis:
/// only fields to hold to the code need it.
#[test]
fn a_file_stating_no_field_never_asks_for_the_analysis() {
    let program = at_a(vec![0xc3; 64]);
    let file =
        Project::from_json(br#"{"program":"a.exe","names":{},"comments":{},"fields":{"C":{}}}"#)
            .expect("the file reads");
    let asked = Cell::new(false);
    let analysis = || {
        asked.set(true);
        Ok(Arc::new(Analysis::default()))
    };
    admit(&program, analysis, &Overlay::default(), &file, false).expect("admitted");
    assert!(!asked.get(), "the analysis was asked for");
}
