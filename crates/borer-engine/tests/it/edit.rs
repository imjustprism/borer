//! Edits as values: the changes an edit writes replay it and their
//! inverses take it back, and a plan commits to the overlay it was made
//! over and to no other.

#![expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]

use crate::common::fixture;
use borer_engine::analysis::edit::{
    Change, Edit, Force, Laid, Line, Refused, Stale, commit, plan, revert,
};
use borer_engine::analysis::project::NAMES_MAX;
use borer_engine::analysis::protos::{Proto, Var, VarKey};
use borer_engine::analysis::stated::{Field, Mode};
use borer_engine::analysis::utypes::{UserType, parse_type};
use borer_engine::analysis::{Analysis, Overlay};
use borer_engine::num::from_usize;
use borer_engine::program::{Arch, Program};

/// A project put in place of the overlay changes one entry of every kind
/// that differs, and its changes taken back give the overlay again.
#[test]
fn changes_replay_an_edit_and_their_inverses_take_it_back() {
    let p = fixture();
    let a = Analysis::compute(&p);
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
    let mut o = before.clone();
    let edits = [Edit::Project(Box::new(after.clone()))];
    let made = plan(&p, &a, &o, &edits, Force::Refuse).expect("planned");
    let changes = made.changes();
    assert_eq!(changes.len(), 6, "{changes:?}");
    assert!(
        matches!(changes.first(), Some(Change::Name(0x1000, s))
            if s.before().map(String::as_str) == Some("old")
                && s.after().map(String::as_str) == Some("new")),
        "{changes:?}"
    );
    assert!(
        changes
            .iter()
            .any(|c| matches!(c, Change::Comment(0x1010, s) if s.after().is_none())),
        "{changes:?}"
    );
    commit(&p, &a, &mut o, &made).expect("committed");
    assert_eq!(o.fingerprint(), after.fingerprint());
    let back = revert(&p, &a, &o, made.changes()).expect("a revert");
    commit(&p, &a, &mut o, &back).expect("taken back");
    assert_eq!(o.fingerprint(), before.fingerprint());
}

/// A rename planned and committed names the function as `set_name` did:
/// the plan says what the function went by and takes, and the change
/// names the entry with what it held and holds.
#[test]
fn a_planned_rename_commits_the_name_and_its_change() {
    let p = fixture();
    let a = Analysis::compute(&p);
    let entry = a.functions.first().expect("a function").entry;
    let mut o = Overlay::default();
    o.names.insert(entry, "first".to_owned());
    let edits = [Edit::Name {
        at: entry,
        name: "second".to_owned(),
    }];
    let made = plan(&p, &a, &o, &edits, Force::Refuse).expect("planned");
    assert_eq!(
        made.lines(),
        vec![Line::Named {
            target: entry,
            function: true,
            old: "first".to_owned(),
            new: "second".to_owned(),
            number: None,
        }]
    );
    commit(&p, &a, &mut o, &made).expect("committed");
    let changes = made.changes();
    assert!(
        matches!(changes, [Change::Name(at, s)]
            if *at == entry
                && s.before().map(String::as_str) == Some("first")
                && s.after().map(String::as_str) == Some("second")),
        "{changes:?}"
    );
    let mut named = Overlay::default();
    named.names.insert(entry, "second".to_owned());
    assert_eq!(o.fingerprint(), named.fingerprint());
}

/// Two renames to one name planned over one overlay cannot both land.
///
/// The second commit finds the overlay changed and is refused as stale,
/// and planned again it is refused as `set_name` refuses a taken name.
///
/// Before plans were values the server checked a rename against a copy of
/// the overlay taken before its write lock, so two calls at once could
/// both pass the check and leave two addresses of one name.
#[test]
fn a_plan_made_before_another_commit_is_stale() {
    let p = fixture();
    let a = Analysis::compute(&p);
    let (first, second) = match a.functions.as_slice() {
        [f, g, ..] => (f.entry, g.entry),
        _ => panic!("two functions"),
    };
    let mut o = Overlay::default();
    let rename = |at: u64| {
        [Edit::Name {
            at,
            name: "shared".to_owned(),
        }]
    };
    let made_a = plan(&p, &a, &o, &rename(first), Force::Refuse).expect("planned");
    let made_b = plan(&p, &a, &o, &rename(second), Force::Refuse).expect("planned");
    commit(&p, &a, &mut o, &made_a).expect("committed");
    let stale = commit(&p, &a, &mut o, &made_b).expect_err("stale");
    assert!(stale.is::<Stale>(), "{stale}");
    assert_eq!(o.names.len(), 1, "the stale plan wrote nothing");
    let again = plan(&p, &a, &o, &rename(second), Force::Refuse).expect_err("taken");
    let refused = again.downcast_ref::<Refused>().expect("an edit refused");
    assert_eq!(refused.edit, 0);
    assert!(
        refused.why.starts_with("'shared' ")
            && refused.why.contains(&format!("{first:#x}"))
            && refused
                .why
                .ends_with("pick another name, or force=true to take it"),
        "{}",
        refused.why
    );
}

/// A plan that would take the overlay past a project's cap is refused by
/// the commit, which leaves the overlay as it was.
///
/// Here a project's load taken back after a rename brings back a name the
/// cap has no room for.
#[test]
fn a_commit_past_a_cap_writes_nothing() {
    let p = fixture();
    let a = Analysis::compute(&p);
    let mut o = Overlay::default();
    o.names
        .extend((0..NAMES_MAX).map(|i| (0x10_0000 + from_usize(i), format!("n{i}"))));
    let mut fewer = o.clone();
    fewer.names.remove(&0x10_0000);
    let load = [Edit::Project(Box::new(fewer))];
    let loaded = plan(&p, &a, &o, &load, Force::Refuse).expect("planned");
    commit(&p, &a, &mut o, &loaded).expect("committed");
    let edits = [Edit::Name {
        at: 0x1000,
        name: "one_more".to_owned(),
    }];
    let named = plan(&p, &a, &o, &edits, Force::Take).expect("planned");
    commit(&p, &a, &mut o, &named).expect("committed");
    let before = o.fingerprint();
    let back = revert(&p, &a, &o, loaded.changes()).expect("a revert");
    let refused = commit(&p, &a, &mut o, &back).expect_err("past the cap");
    assert!(refused.to_string().contains("names"), "{refused}");
    assert_eq!(o.fingerprint(), before, "the overlay changed");
    let edits = [Edit::Name {
        at: 0x7000_0000,
        name: "two_more".to_owned(),
    }];
    plan(&p, &a, &o, &edits, Force::Take).expect_err("the plan refuses it too");
}

/// Returns the first function's entry of an analysis and an overlay
/// naming that function's first parameter `x`.
///
/// # Arguments
///
/// * `a` - The analysis.
#[expect(clippy::expect_used, reason = "a test's setup")]
fn stating_x(a: &Analysis) -> (u64, Overlay) {
    let entry = a.functions.first().expect("a function").entry;
    let mut o = Overlay::default();
    let x = Var::parse("x").expect("a variable");
    o.vars.entry(entry).or_default().insert(VarKey::Param(0), x);
    (entry, o)
}

/// Returns the edit that renames a function's variable, keeping its type.
///
/// # Arguments
///
/// * `entry` - The function.
/// * `var` - The variable as stated.
/// * `name` - Its new name.
fn renaming(entry: u64, var: &str, name: &str) -> [Edit; 1] {
    [Edit::Var {
        entry,
        var: var.to_owned(),
        field: None,
        name: Some(name.to_owned()),
        ty: None,
    }]
}

/// The inverses of a mixed plan's changes, a name, a comment, a struct
/// and a variable's type, applied in reverse order give back the overlay
/// the plan was committed to.
#[test]
fn the_inverse_of_a_mixed_plan_restores_the_overlay() {
    let p = fixture();
    let a = Analysis::compute(&p);
    let (entry, mut o) = stating_x(&a);
    let before = o.fingerprint();
    let word = parse_type("u32").expect("a type");
    let field = |name: &str| Field {
        name: name.to_owned(),
        ty: Some(word.clone()),
    };
    let edits = [
        Edit::Name {
            at: entry,
            name: "mixed".to_owned(),
        },
        Edit::Comment {
            at: entry,
            text: "? a guess".to_owned(),
        },
        Edit::Fields {
            name: "Pair".to_owned(),
            size: None,
            fields: vec![(0, field("lo")), (4, field("hi"))],
            mode: Mode::Merge,
        },
        Edit::Var {
            entry,
            var: "x".to_owned(),
            field: None,
            name: Some("count".to_owned()),
            ty: Some("int".to_owned()),
        },
    ];
    let made = plan(&p, &a, &o, &edits, Force::Refuse).expect("planned");
    commit(&p, &a, &mut o, &made).expect("committed");
    assert_eq!(made.changes().len(), 4, "{made:?}");
    assert_ne!(o.fingerprint(), before);
    let back = revert(&p, &a, &o, made.changes()).expect("a revert");
    commit(&p, &a, &mut o, &back).expect("taken back");
    assert_eq!(o.fingerprint(), before, "{made:?}");
}

/// Loading a project is an edit too: its plan leaves the project's
/// annotations in place of the overlay's, and its inverse brings the
/// overlay's back.
#[test]
fn a_project_put_in_place_is_taken_back_by_its_inverse() {
    let p = fixture();
    let a = Analysis::compute(&p);
    let mut o = Overlay::default();
    o.names.insert(0x1000, "kept_before".to_owned());
    o.comments.insert(0x1000, "a note".to_owned());
    let mut loaded = Overlay::default();
    loaded.names.insert(0x1000, "from_project".to_owned());
    loaded.names.insert(0x1010, "also".to_owned());
    let before = o.fingerprint();
    let edits = [Edit::Project(Box::new(loaded.clone()))];
    let made = plan(&p, &a, &o, &edits, Force::Refuse).expect("planned");
    commit(&p, &a, &mut o, &made).expect("committed");
    assert_eq!(o.fingerprint(), loaded.fingerprint());
    let back = revert(&p, &a, &o, made.changes()).expect("a revert");
    commit(&p, &a, &mut o, &back).expect("taken back");
    assert_eq!(o.fingerprint(), before);
}

/// Every change a plan writes says what its entry holds once committed:
/// a change's key and its values are of one kind, so none can claim a
/// value its entry does not take.
#[test]
fn every_change_says_what_its_entry_holds() {
    let p = fixture();
    let a = Analysis::compute(&p);
    let (entry, mut o) = stating_x(&a);
    let word = parse_type("u32").expect("a type");
    let edits = [
        Edit::Name {
            at: entry,
            name: "kinds".to_owned(),
        },
        Edit::Comment {
            at: entry,
            text: "a note".to_owned(),
        },
        Edit::Alias {
            name: "word_t".to_owned(),
            ty: word,
        },
        Edit::Proto {
            entry,
            proto: Proto::parse("int f(int a)").expect("a prototype"),
        },
        Edit::Var {
            entry,
            var: "x".to_owned(),
            field: None,
            name: Some("count".to_owned()),
            ty: None,
        },
    ];
    let made = plan(&p, &a, &o, &edits, Force::Refuse).expect("planned");
    commit(&p, &a, &mut o, &made).expect("committed");
    assert_eq!(made.changes().len(), edits.len(), "{made:?}");
    for change in made.changes() {
        let holds = match change {
            Change::Name(at, s) => o.names.get(at) == s.after(),
            Change::Comment(at, s) => o.comments.get(at) == s.after(),
            Change::Type(name, s) => o.types.get(name) == s.after(),
            Change::Applied(at, s) => o.applied.get(at) == s.after(),
            Change::Proto(at, s) => o.prototypes.get(at) == s.after(),
            Change::Var(at, key, s) => o.vars.get(at).and_then(|v| v.get(key)) == s.after(),
            Change::Field(class, off, s) => {
                o.fields.get(class).and_then(|f| f.get(off)) == s.after()
            }
        };
        assert!(holds, "{change:?}");
    }
}

/// A layout planned again after another edit landed reads the overlay as
/// that edit left it: a prototype stated meanwhile for one of the class's
/// methods keeps its parameters, and only its object is typed.
#[test]
fn a_layout_planned_again_reads_the_prototypes_stated_meanwhile() {
    /// `Cls::Has`, a method of the fixture's class `Cls`.
    const HAS: u64 = 0x1660;
    let p = fixture();
    let a = Analysis::compute(&p);
    let mut o = Overlay::default();
    let layout = [Edit::Layout {
        from: Laid::Class("Cls".to_owned()),
        name: "ClsS".to_owned(),
    }];
    let stated = [Edit::Proto {
        entry: HAS,
        proto: Proto::parse("bool f(void *self, int key, char *why)").expect("a prototype"),
    }];
    let made_layout = plan(&p, &a, &o, &layout, Force::Refuse).expect("planned");
    let made_proto = plan(&p, &a, &o, &stated, Force::Refuse).expect("planned");
    commit(&p, &a, &mut o, &made_proto).expect("committed");
    let stale = commit(&p, &a, &mut o, &made_layout).expect_err("stale");
    assert!(stale.is::<Stale>(), "{stale}");
    let again = plan(&p, &a, &o, &layout, Force::Refuse).expect("planned again");
    commit(&p, &a, &mut o, &again).expect("committed");
    let has = o.prototypes.get(&HAS).expect("a prototype");
    assert_eq!(has.params.len(), 3, "{}", has.spell());
    assert_eq!(
        has.params.first().map(|q| q.ty.spell()).as_deref(),
        Some("ClsS *"),
        "{}",
        has.spell()
    );
}

/// Taking back one rename of a function's variables keeps a later rename
/// of another, and taking back what a later edit changed again, or a type
/// a later edit applies, is refused with nothing written.
#[test]
fn taking_an_edit_back_keeps_and_refuses_what_came_after() {
    let p = fixture();
    let a = Analysis::compute(&p);
    let entry = a.functions.first().expect("a function").entry;
    let mut o = Overlay::default();
    let stated = o.vars.entry(entry).or_default();
    stated.insert(VarKey::Param(0), Var::parse("x").expect("a variable"));
    stated.insert(VarKey::Param(1), Var::parse("y").expect("a variable"));
    let first = plan(&p, &a, &o, &renaming(entry, "x", "count"), Force::Refuse).expect("planned");
    commit(&p, &a, &mut o, &first).expect("committed");
    let second = plan(&p, &a, &o, &renaming(entry, "y", "total"), Force::Refuse).expect("planned");
    commit(&p, &a, &mut o, &second).expect("committed");
    let back = revert(&p, &a, &o, first.changes()).expect("a revert");
    commit(&p, &a, &mut o, &back).expect("taken back");
    let named = |key| {
        o.vars
            .get(&entry)
            .and_then(|v| v.get(&key))
            .map(|v| v.name.clone())
    };
    assert_eq!(named(VarKey::Param(0)).as_deref(), Some("x"));
    assert_eq!(
        named(VarKey::Param(1)).as_deref(),
        Some("total"),
        "the later rename went"
    );
    let name = |n: &str| {
        [Edit::Name {
            at: entry,
            name: n.to_owned(),
        }]
    };
    let one = plan(&p, &a, &o, &name("one"), Force::Refuse).expect("planned");
    commit(&p, &a, &mut o, &one).expect("committed");
    let two = plan(&p, &a, &o, &name("two"), Force::Refuse).expect("planned");
    commit(&p, &a, &mut o, &two).expect("committed");
    let before = o.fingerprint();
    let changed = revert(&p, &a, &o, one.changes()).expect_err("renamed since");
    assert!(changed.to_string().contains("changed since"), "{changed}");
    assert_eq!(o.fingerprint(), before, "a refused take-back wrote");
    let word = parse_type("u32").expect("a type");
    let define = [Edit::Alias {
        name: "Word".to_owned(),
        ty: word,
    }];
    let defined = plan(&p, &a, &o, &define, Force::Refuse).expect("planned");
    commit(&p, &a, &mut o, &defined).expect("committed");
    let applied = [Edit::Apply {
        at: 0x2040,
        ty: parse_type("Word").expect("a type"),
    }];
    let made = plan(&p, &a, &o, &applied, Force::Refuse).expect("planned");
    commit(&p, &a, &mut o, &made).expect("committed");
    let before = o.fingerprint();
    let back = revert(&p, &a, &o, defined.changes()).expect("a revert");
    let dropped = commit(&p, &a, &mut o, &back).expect_err("still applied");
    assert!(dropped.to_string().contains("0x2040"), "{dropped}");
    assert_eq!(o.fingerprint(), before, "a refused take-back wrote");
}

/// A plan made over one program's overlay does not commit to another's,
/// even where the two overlays state the same and the plan's own
/// analysis is the one passed.
#[test]
fn a_plan_does_not_commit_to_another_programs_overlay() {
    let p = fixture();
    let a = Analysis::compute(&p);
    let other = Program::raw(
        vec![0xc3; 16],
        Arch::X86_64,
        0x1000,
        Some(0x1000),
        Vec::new(),
    );
    let edits = [Edit::Comment {
        at: 0x1000,
        text: "a note".to_owned(),
    }];
    let made = plan(&p, &a, &Overlay::default(), &edits, Force::Refuse).expect("planned");
    let mut theirs = Overlay::default();
    let stale = commit(&other, &a, &mut theirs, &made).expect_err("another program");
    assert!(stale.is::<Stale>(), "{stale}");
    assert!(
        theirs.comments.is_empty(),
        "the other program's overlay changed"
    );
}

/// Taking an edit back is held to what a plan is: it does not leave a
/// name two functions answer to, nor two variables of one function of
/// one name, and a revert says what it does as a plan does.
#[test]
fn a_revert_leaves_nothing_a_plan_refuses() {
    let p = fixture();
    let a = Analysis::compute(&p);
    let (f1, f2) = match a.functions.as_slice() {
        [f, g, ..] => (f.entry, g.entry),
        _ => panic!("two functions"),
    };
    let name = |at: u64, n: &str| {
        [Edit::Name {
            at,
            name: n.to_owned(),
        }]
    };
    let mut o = Overlay::default();
    o.names.insert(f1, "foo".to_owned());
    let first = plan(&p, &a, &o, &name(f1, "bar"), Force::Refuse).expect("planned");
    commit(&p, &a, &mut o, &first).expect("committed");
    let second = plan(&p, &a, &o, &name(f2, "foo"), Force::Refuse).expect("planned");
    commit(&p, &a, &mut o, &second).expect("committed");
    let taken = revert(&p, &a, &o, first.changes()).expect_err("foo names f2 now");
    assert!(taken.to_string().contains("'foo'"), "{taken}");
    let (entry, mut o) = stating_x(&a);
    o.vars
        .entry(entry)
        .or_default()
        .insert(VarKey::Param(1), Var::parse("y").expect("a variable"));
    let first = plan(&p, &a, &o, &renaming(entry, "x", "count"), Force::Refuse).expect("planned");
    commit(&p, &a, &mut o, &first).expect("committed");
    let second = plan(&p, &a, &o, &renaming(entry, "y", "x"), Force::Refuse).expect("planned");
    commit(&p, &a, &mut o, &second).expect("committed");
    let twice = revert(&p, &a, &o, first.changes()).expect_err("x names the second now");
    assert!(twice.to_string().contains("x already names"), "{twice}");
}

/// A revert says what it does as a plan does: the name a function goes
/// back to, and what else it takes back.
#[test]
fn a_revert_says_what_it_takes_back() {
    let p = fixture();
    let a = Analysis::compute(&p);
    let entry = a.functions.first().expect("a function").entry;
    let mut o = Overlay::default();
    o.names.insert(entry, "foo".to_owned());
    let edits = [
        Edit::Name {
            at: entry,
            name: "bar".to_owned(),
        },
        Edit::Comment {
            at: entry,
            text: "a note".to_owned(),
        },
    ];
    let made = plan(&p, &a, &o, &edits, Force::Refuse).expect("planned");
    commit(&p, &a, &mut o, &made).expect("committed");
    let back = revert(&p, &a, &o, made.changes()).expect("a revert");
    assert_eq!(
        back.lines(),
        [
            Line::Stated {
                would: format!("take back the comment at {entry:#x}"),
                done: format!("took back the comment at {entry:#x}"),
            },
            Line::Named {
                target: entry,
                function: true,
                old: "bar".to_owned(),
                new: "foo".to_owned(),
                number: None,
            },
        ]
    );
}
