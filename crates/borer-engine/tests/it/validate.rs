//! User types held to what an overlay holds, as a hand-edited project
//! states them: the counts, the chains of typedefs and the deadline.

#![expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]

use std::collections::BTreeMap;

use borer_engine::analysis::utypes::{
    ALIAS_DEPTH_MAX, TYPES_MAX, TypeExpr, UserEnum, UserField, UserStruct, UserType, validate,
};
use borer_engine::cancel::Cancel;

/// Returns typedefs `{prefix}0` to `{prefix}{n-1}`, each naming the next
/// through `via`, the last a `u32`.
///
/// # Arguments
///
/// * `prefix` - The names' stem.
/// * `n` - How many typedefs.
/// * `via` - Wraps the name each typedef states (a pointer, an array).
fn chain(prefix: &str, n: usize, via: impl Fn(TypeExpr) -> TypeExpr) -> BTreeMap<String, UserType> {
    (0..n)
        .map(|k| {
            let next = if k + 1 == n {
                TypeExpr::U32
            } else {
                via(TypeExpr::Named(format!("{prefix}{}", k + 1)))
            };
            (format!("{prefix}{k}"), UserType::Alias(next))
        })
        .collect()
}

/// A chain of typedefs past [`ALIAS_DEPTH_MAX`] is refused naming the one
/// it starts at, through pointers and arrays as by name; one at the cap
/// validates, and of two chains the longer is named.
#[test]
fn a_chain_of_typedefs_past_the_cap_is_refused_naming_its_head() {
    let max = ALIAS_DEPTH_MAX;
    let applied = BTreeMap::new();
    assert!(validate(&chain("A", max, |t| t), &applied).is_ok());
    let vias: [fn(TypeExpr) -> TypeExpr; 3] = [
        |t| t,
        |t| TypeExpr::Ptr(Box::new(t)),
        |t| TypeExpr::Array(Box::new(t), 2),
    ];
    for via in vias {
        let err = validate(&chain("A", max + 1, via), &applied).expect_err("a long chain");
        let says = format!(
            "typedef 'A0' starts a chain of {} typedefs; {max} is the most",
            max + 1
        );
        assert!(err.to_string().contains(&says), "{err}");
    }
    let mut two = chain("Z", max + 1, |t| t);
    two.extend(chain("B", max + 3, |t| t));
    let err = validate(&two, &applied).expect_err("two long chains");
    assert!(err.to_string().contains("typedef 'B0' starts"), "{err}");
}

/// Every count is held to its cap before anything is sized: the types, a
/// struct's fields, an enum's values and the applications.
#[test]
fn counts_past_their_caps_are_refused() {
    let none = BTreeMap::new();
    let many = chain("T", TYPES_MAX + 1, |t| t);
    let err = validate(&many, &none).expect_err("too many types");
    assert!(err.to_string().contains("states 4097 types"), "{err}");
    let fields = (0..0x101u64)
        .map(|k| {
            let name = format!("f{k}");
            (
                k,
                UserField {
                    name,
                    ty: TypeExpr::U8,
                },
            )
        })
        .collect();
    let wide = UserStruct {
        size: 0x101,
        fields,
    };
    let types = [("Wide".to_owned(), UserType::Struct(wide))].into();
    let err = validate(&types, &none).expect_err("too many fields");
    let says = "struct 'Wide' states 257 fields; 256 is the most";
    assert!(err.to_string().contains(says), "{err}");
    let values = (0..0x101u64).map(|v| (v, format!("V{v}"))).collect();
    let many = UserEnum { size: 4, values };
    let types = [("Many".to_owned(), UserType::Enum(many))].into();
    let err = validate(&types, &none).expect_err("too many values");
    assert!(
        err.to_string().contains("enum 'Many' states 257 values"),
        "{err}"
    );
    let applied = (0..0x1_0001u64).map(|k| (k, TypeExpr::U32)).collect();
    let err = validate(&BTreeMap::new(), &applied).expect_err("too many applied");
    let says = "applies 65537 types; 65536 is the most";
    assert!(err.to_string().contains(says), "{err}");
}

/// A field counting a typedef's arrays of a struct no bytes wide past
/// every count resolves to no size, as `set_type` sizes it.
///
/// Sized once, the typedef was no bytes wide, and the field's count
/// multiplied that afterwards, so the field took no bytes.
#[test]
fn counts_past_every_count_through_a_typedef_resolve_to_no_size() {
    let empty = UserType::Struct(UserStruct {
        size: 0,
        fields: BTreeMap::new(),
    });
    let array = |of: TypeExpr| TypeExpr::Array(Box::new(of), 1 << 24);
    let many = UserType::Alias(array(array(TypeExpr::Named("E".to_owned()))));
    let field = UserField {
        name: "f".to_owned(),
        ty: array(TypeExpr::Named("Z".to_owned())),
    };
    let holder = UserType::Struct(UserStruct {
        size: 8,
        fields: [(0, field)].into(),
    });
    let types = [
        ("E".to_owned(), empty),
        ("H".to_owned(), holder),
        ("Z".to_owned(), many),
    ]
    .into();
    let err = validate(&types, &BTreeMap::new()).expect_err("the counts pass every count");
    let says = "field f at 0x0 has type Z[16777216], which resolves to no size";
    assert!(err.to_string().contains(says), "{err}");
}

/// Types checked under a raised flag are refused, saying the deadline
/// passed, so a cut load answers that it was cut.
#[test]
fn types_checked_past_the_deadline_are_refused() {
    let flag = Cancel::new();
    flag.raise();
    let types = chain("A", 2, |t| t);
    let err = flag
        .within(|| validate(&types, &BTreeMap::new()))
        .expect_err("a cut check passed");
    assert!(err.to_string().contains("deadline passed"), "{err}");
    assert!(validate(&types, &BTreeMap::new()).is_ok());
}
