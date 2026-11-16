//! Edits as values: the changes an edit writes replay it and their
//! inverses take it back.

#![expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]

use borer_engine::analysis::Overlay;
use borer_engine::analysis::edit::{Change, Key, Value};
use borer_engine::analysis::protos::{Proto, Var, VarKey};
use borer_engine::analysis::stated::Field;
use borer_engine::analysis::utypes::{UserType, parse_type};

/// The changes between two overlays, one per entry of every kind that
/// differs, applied to the first give the second, and their inverses
/// applied in reverse order give the first again.
#[test]
fn changes_replay_an_edit_and_their_inverses_take_it_back() {
    let ty = parse_type("u32").expect("a type");
    let mut before = Overlay::default();
    before.names.insert(0x1000, "old".to_owned());
    before.names.insert(0x1040, "same".to_owned());
    before.comments.insert(0x1010, "kept".to_owned());
    before
        .types
        .insert("T".to_owned(), UserType::Alias(ty.clone()));
    let mut after = before.clone();
    after.names.insert(0x1000, "new".to_owned());
    after.comments.remove(&0x1010);
    after.applied.insert(0x2000, ty);
    let proto = Proto::parse("int f(int a)").expect("a prototype");
    after.prototypes.insert(0x1000, proto);
    let var = Var::parse("int count").expect("a variable");
    after
        .vars
        .entry(0x1000)
        .or_default()
        .insert(VarKey::Param(0), var);
    let field = Field {
        name: "hp".to_owned(),
        ty: None,
    };
    after
        .fields
        .entry("C".to_owned())
        .or_default()
        .insert(8, field);
    let changes = before.changes(&after);
    assert_eq!(changes.len(), 6, "{changes:?}");
    assert_eq!(
        changes.first(),
        Some(&Change {
            key: Key::Name(0x1000),
            old: Some(Value::Text("old".to_owned())),
            new: Some(Value::Text("new".to_owned())),
        })
    );
    assert!(
        changes
            .iter()
            .any(|c| c.key == Key::Comment(0x1010) && c.new.is_none()),
        "{changes:?}"
    );
    let mut replayed = before.clone();
    replayed.apply(&changes);
    assert_eq!(replayed.fingerprint(), after.fingerprint());
    assert!(replayed.changes(&after).is_empty());
    let back: Vec<Change> = changes.iter().rev().map(Change::inverse).collect();
    replayed.apply(&back);
    assert_eq!(replayed.fingerprint(), before.fingerprint());
    assert!(replayed.changes(&before).is_empty());
}
