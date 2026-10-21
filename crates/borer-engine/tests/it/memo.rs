//! The memo of derived results ([`borer_engine::analysis::Derived`]): what
//! one caller's build hands another, and what keys a result.

#![expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]

use crate::common::fixture;

use borer_engine::analysis::decompile::decompile_named;
use borer_engine::analysis::{Analysis, Derived, Overlay};
use borer_engine::cancel::Cancel;

/// A result one request's deadline cut short reaches no other request.
///
/// The cancel flag is the caller's own: a build that ends after its flag
/// was raised may hold an emulation stopped at the time limit. A second
/// request asking for the same result meanwhile waits for that build, and
/// must then build the result itself rather than take the cut one, or
/// memoize what it builds from it for every request after.
#[test]
fn a_result_one_request_cut_short_reaches_no_other() {
    let derived = Derived::default();
    let flag = Cancel::new();
    let building = std::sync::Barrier::new(2);
    std::thread::scope(|scope| {
        let cut = scope.spawn(|| {
            flag.within(|| {
                derived.get_or_build("inner", (), || {
                    building.wait();
                    while !Cancel::raised() {
                        std::thread::yield_now();
                    }
                    "cut"
                })
            })
        });
        building.wait();
        let whole = scope.spawn(|| {
            derived.get_or_build("outer", (), || {
                *derived.get_or_build("inner", (), || "whole")
            })
        });
        std::thread::sleep(std::time::Duration::from_millis(200));
        flag.raise();
        assert_eq!(*cut.join().expect("the cut request ends"), "cut");
        assert_eq!(
            *whole.join().expect("the other request ends"),
            "whole",
            "the request whose deadline did not pass took a result cut short"
        );
    });
    assert_eq!(
        *derived.get_or_build("outer", (), || "rebuilt"),
        "whole",
        "a result built from a cut one was kept"
    );
}

/// Overlays that hold different facts fingerprint apart, so a text read
/// under one is never handed to a caller holding the other.
///
/// The fingerprint keys every memoized result read under the names. A name
/// and a comment of the same text at the same address folded to the same
/// bytes, so the text with the name was handed to the overlay with the
/// comment.
#[test]
fn overlays_holding_different_facts_fingerprint_apart() {
    let p = fixture();
    let entry = Analysis::compute(&p).functions[0].entry;
    let mut named = Overlay::default();
    named.names.insert(entry, "parse_header".to_owned());
    let mut commented = Overlay::default();
    commented.comments.insert(entry, "parse_header".to_owned());
    assert_ne!(named.fingerprint(), commented.fingerprint());
    let shared = Analysis::compute(&p);
    let fresh = Analysis::compute(&p);
    decompile_named(&p, &shared, &named, entry);
    assert_eq!(
        decompile_named(&p, &shared, &commented, entry),
        decompile_named(&p, &fresh, &commented, entry),
        "the text read under the name was handed to the overlay with the comment"
    );
}
