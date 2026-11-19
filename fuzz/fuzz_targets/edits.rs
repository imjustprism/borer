//! Reads arbitrary text as what a person types into each form of edit a
//! referent takes, and plans the edit through the catalog row that makes
//! it over a small image: the path every inline rename, comment, type,
//! prototype, declaration, enum and typedef takes before its plan is shown;
//! and reads each line as a chat reply's C code block is colored.

#![no_main]

use std::sync::{Arc, OnceLock};

use borer_engine::analysis::edit::{Form, VarValue};
use borer_engine::analysis::{Analysis, Overlay};
use borer_engine::program::{Arch, Program, Section};
use borer_engine::view::c_kinds;
use borer_front::tools::{Loaded, propose};
use libfuzzer_sys::fuzz_target;

/// Where the image's one function enters.
const ENTRY: u64 = 0x1000;

/// Where its page of data starts.
const DATA: u64 = ENTRY + 0x100;

/// Returns the face the edits are planned on, built once: a function
/// returning its argument plus one, beside a page of data.
fn face() -> &'static Loaded {
    static FACE: OnceLock<Loaded> = OnceLock::new();
    FACE.get_or_init(|| {
        let mut bytes = vec![0u8; 0x200];
        bytes[..4].copy_from_slice(&[0x8d, 0x41, 0x01, 0xc3]); // ASM: lea eax,[rcx+1]; ret
        let sections = vec![
            Section::mapped(".text", ENTRY, 0, 0x100, false, true),
            Section::mapped(".data", DATA, 0x100, 0x100, true, false),
        ];
        let program = Program::raw(bytes, Arch::X86_64, ENTRY, Some(ENTRY), sections);
        Loaded {
            analysis: Arc::new(Analysis::compute(&program)),
            program: Arc::new(program),
            overlay: Arc::new(Overlay::default()),
        }
    })
}

fuzz_target!(|data: &[u8]| {
    let text = String::from_utf8_lossy(data);
    let var = |value| Form::Var {
        entry: ENTRY,
        var: "a1".to_owned(),
        value,
    };
    let forms = [
        Form::Name { at: ENTRY },
        Form::Name { at: DATA },
        Form::Comment { at: ENTRY },
        var(VarValue::Declaration { kept_type: None }),
        var(VarValue::Type {
            kept_name: "count".to_owned(),
        }),
        Form::Proto { entry: ENTRY },
        Form::Apply { at: DATA },
        Form::Field {
            ty: "Player".to_owned(),
            offset: 4,
            keep: None,
        },
        Form::Declare,
        Form::Enum,
        Form::Alias,
    ];
    for form in forms {
        _ = propose(face(), &form, &text);
    }
    for line in text.lines() {
        let mut at = 0;
        for (span, _) in c_kinds(line) {
            assert!(span.start == at && span.end > at, "{line:?}");
            assert!(line.is_char_boundary(span.end), "{line:?}");
            at = span.end;
        }
        assert_eq!(at, line.len(), "{line:?}");
    }
});
