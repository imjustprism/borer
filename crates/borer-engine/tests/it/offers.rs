//! Which edit a referent takes is the edit path's fact.
//!
//! Each referent a view links is offered the forms that address it, and
//! each refusal is the one the plan gives or says why the plan would edit
//! something else.

#![expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]

use std::collections::BTreeMap;

use crate::view::{TEXT, filling, tokens};
use borer_engine::analysis::decompile::view::view;
use borer_engine::analysis::edit::{Edit, Force, Form, Kind, Line, Refused, VarValue, offer, plan};
use borer_engine::analysis::protos::VarKey;
use borer_engine::analysis::utypes::{TypeExpr, UserField, UserStruct, UserType};
use borer_engine::analysis::{Analysis, Overlay};
use borer_engine::program::Program;
use borer_engine::view::Ref;

/// Plans one edit over `o`, returning its lines or why it was refused.
///
/// # Arguments
///
/// * `(p, a, o)` - The image, its analysis and the overlay.
/// * `edit` - The edit.
///
/// # Errors
///
/// The plan's refusal, as the agent reads it.
fn planned((p, a, o): (&Program, &Analysis, &Overlay), edit: Edit) -> Result<Vec<Line>, String> {
    plan(p, a, o, &[edit], Force::Refuse)
        .map(|made| made.lines().to_vec())
        .map_err(|e| match e.downcast_ref::<Refused>() {
            Some(refused) => refused.why.clone(),
            None => e.to_string(),
        })
}

/// Returns [`crate::view::filling`]'s image, its analysis, and an overlay
/// stating a user struct `Player` with `hp` at offset 4.
fn fixture() -> (Program, Analysis, Overlay) {
    let p = filling(false);
    let a = Analysis::compute(&p);
    let mut o = Overlay::default();
    let hp = UserField {
        name: "hp".to_owned(),
        ty: TypeExpr::U32,
    };
    let player = UserStruct {
        size: 8,
        fields: BTreeMap::from([(4, hp)]),
    };
    o.types
        .insert("Player".to_owned(), UserType::Struct(player));
    (p, a, o)
}

/// The field [`fixture`] states.
fn hp() -> Ref {
    Ref::Field {
        ty: "Player".into(),
        offset: 4,
    }
}

/// Returns the form each kind of edit offers `r`, `None` for a kind
/// refused.
///
/// # Arguments
///
/// * `(p, a, o)` - The image, its analysis and the overlay.
/// * `r` - The referent.
fn forms((p, a, o): (&Program, &Analysis, &Overlay), r: &Ref) -> [Option<Form>; 3] {
    [Kind::Rename, Kind::Retype, Kind::Comment]
        .map(|kind| offer(p, a, o, r, kind).ok().map(|o| o.form))
}

/// Each referent a view links is offered the forms that address it.
///
/// A function and a call to another take their name, their prototype and a comment at
/// its entry; a local a declaration; a global its name, an applied type
/// and a comment; a field its name and its type under the name it keeps;
/// an import, a string and a comment only a comment.
#[test]
fn every_referent_is_offered_the_forms_that_address_it() {
    let (p, a, o) = fixture();
    let ctx = (&p, &a, &o);
    let v = view(&p, &a, &o, TEXT).expect("a view");
    let linked: Vec<Ref> = tokens(&v).into_iter().filter_map(|t| t.3).collect();
    let first = |pick: &dyn Fn(&Ref) -> bool| {
        linked
            .iter()
            .find(|r| pick(r))
            .cloned()
            .expect("the view links one")
    };
    let Ref::Function(callee) = first(&|r| matches!(r, Ref::Function(e) if *e != TEXT)) else {
        panic!("a call")
    };
    let Ref::Global(global) = first(&|r| matches!(r, Ref::Global(_))) else {
        panic!("a global")
    };
    let local = first(&|r| matches!(r, Ref::Variable { name, .. } if name.starts_with("local_")));
    let Ref::Variable { name: spelled, .. } = &local else {
        panic!("a local")
    };
    let Ref::Import(slot) = first(&|r| matches!(r, Ref::Import(_))) else {
        panic!("an import")
    };
    let declared = Form::Var {
        entry: TEXT,
        var: spelled.to_string(),
        value: VarValue::Declaration { kept_type: None },
    };
    let string = TEXT + 0x2040;
    let field = |keep: Option<&str>| Form::Field {
        ty: "Player".to_owned(),
        offset: 4,
        keep: keep.map(str::to_owned),
    };
    for (r, want) in [
        (
            Ref::Function(TEXT),
            [
                Some(Form::Name { at: TEXT }),
                Some(Form::Proto { entry: TEXT }),
                Some(Form::Comment { at: TEXT }),
            ],
        ),
        (
            Ref::Function(callee),
            [
                Some(Form::Name { at: callee }),
                Some(Form::Proto { entry: callee }),
                Some(Form::Comment { at: callee }),
            ],
        ),
        (
            local.clone(),
            [Some(declared.clone()), Some(declared), None],
        ),
        (
            Ref::Global(global),
            [
                Some(Form::Name { at: global }),
                Some(Form::Apply { at: global }),
                Some(Form::Comment { at: global }),
            ],
        ),
        (hp(), [Some(field(None)), Some(field(Some("hp"))), None]),
        (
            Ref::Import(slot),
            [None, None, Some(Form::Comment { at: slot })],
        ),
        (
            Ref::String(string),
            [None, None, Some(Form::Comment { at: string })],
        ),
        (
            Ref::Comment(TEXT),
            [None, None, Some(Form::Comment { at: TEXT })],
        ),
        (Ref::Type("Player".into()), [None, None, None]),
    ] {
        assert_eq!(forms(ctx, &r), want, "{r:?}");
    }
    let now = offer(&p, &a, &o, &hp(), Kind::Retype).expect("a field takes a type");
    assert_eq!(now.now, "u32");
}

/// A refusal is the plan's own refusal of the same edit, or says why the
/// plan would edit something else: a label's name names its function.
#[test]
fn a_refusal_is_the_plans_own_or_says_what_the_plan_would_edit() {
    let (p, a, o) = fixture();
    let ctx = (&p, &a, &o);
    let nosuch = Ref::Variable {
        function: TEXT,
        name: "nosuch".into(),
        key: None,
    };
    let edit = Edit::Var {
        entry: TEXT,
        var: "nosuch".to_owned(),
        field: None,
        name: Some("fresh".to_owned()),
        ty: None,
    };
    assert_eq!(
        offer(&p, &a, &o, &nosuch, Kind::Rename),
        Err(planned(ctx, edit).expect_err("refused"))
    );
    let label = TEXT + 0x10;
    let why = offer(&p, &a, &o, &Ref::Address(label), Kind::Rename).expect_err("a label");
    let rename = Edit::Name {
        at: label,
        name: "fresh".to_owned(),
    };
    let named = planned(ctx, rename);
    assert!(
        matches!(named.as_deref(), Ok([Line::Named { target, .. }]) if *target == TEXT),
        "{named:?}: {why}"
    );
    assert!(why.contains("label"), "{why}");
}

/// Asking a function for its name or a comment reads no text: only its
/// prototype, prefilled from its signature line, decompiles it.
#[test]
fn a_name_or_a_comment_offered_decompiles_nothing() {
    let (p, a, o) = fixture();
    let before = a.derived.builds();
    for kind in [Kind::Rename, Kind::Comment] {
        offer(&p, &a, &o, &Ref::Function(TEXT), kind).expect("offered");
    }
    assert_eq!(a.derived.builds(), before);
    offer(&p, &a, &o, &Ref::Function(TEXT), Kind::Retype).expect("offered");
    assert!(a.derived.builds() > before);
}

/// A variable token read as one variable whose name now reads as another,
/// as after an undo before the view is built again, is refused: the edit
/// would land on the other variable.
#[test]
fn a_variable_the_view_read_as_another_is_refused() {
    let (p, a, o) = fixture();
    let v = view(&p, &a, &o, TEXT).expect("a view");
    let local = tokens(&v)
        .into_iter()
        .filter_map(|t| t.3)
        .find(
            |r| matches!(r, Ref::Variable { name, key: Some(_), .. } if name.starts_with("local_")),
        )
        .expect("the view links a local");
    assert!(offer(&p, &a, &o, &local, Kind::Rename).is_ok());
    let Ref::Variable { function, name, .. } = local else {
        panic!("a local")
    };
    let stale = Ref::Variable {
        function,
        name,
        key: Some(VarKey::Param(7)),
    };
    let why = offer(&p, &a, &o, &stale, Kind::Rename).expect_err("read as another");
    assert!(why.contains("names another variable"), "{why}");
}

/// A field read through a typedef of a struct holds that struct's field.
#[test]
fn a_field_through_a_typedef_holds_the_structs_field() {
    let (p, a, mut o) = fixture();
    o.types.insert(
        "PlayerT".to_owned(),
        UserType::Alias(TypeExpr::Named("Player".to_owned())),
    );
    let field = Ref::Field {
        ty: "PlayerT".into(),
        offset: 4,
    };
    let now = offer(&p, &a, &o, &field, Kind::Rename).expect("a field takes a name");
    assert_eq!(now.now, "hp");
}

/// A function's prototype is offered as one a person can state as it opens: its text's
/// signature with the parameter names the text makes up left out.
#[test]
fn an_inferred_prototype_is_offered_as_one_that_states() {
    use borer_engine::analysis::protos::Proto;
    let (p, a, o) = fixture();
    let shown = offer(&p, &a, &o, &Ref::Function(TEXT), Kind::Retype).expect("a prototype");
    assert!(!shown.now.is_empty());
    let parsed = Proto::parse(&shown.now);
    assert!(parsed.is_ok(), "{}: {parsed:?}", shown.now);
}
