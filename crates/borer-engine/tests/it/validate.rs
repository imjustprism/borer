//! User types held to what an overlay holds, as a hand-edited project
//! states them: the counts, the chains of typedefs, the types holding
//! themselves and the deadline.
//!
//! C declarations are read over types that nest deep in bounded time.

#![expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]

use std::collections::BTreeMap;
use std::time::Duration;

use borer_engine::analysis::cdecl::{Abi, parse};
use borer_engine::analysis::utypes::{
    ALIAS_DEPTH_MAX, TYPES_MAX, TypeExpr, UserEnum, UserField, UserStruct, UserType, parse_type,
    validate,
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

/// A type holding itself by value is refused naming the cycle: through its
/// own field, an array of itself, another struct or a typedef; two holding
/// each other through pointers validate.
#[test]
fn a_type_holding_itself_by_value_is_refused() {
    let holding = |name: &str, ty: &str| {
        let x = UserField {
            name: "x".to_owned(),
            ty: parse_type(ty).expect("a type"),
        };
        let fields = [(0, x)].into_iter().collect();
        (
            name.to_owned(),
            UserType::Struct(UserStruct { size: 8, fields }),
        )
    };
    let alias = |name: &str, ty: &str| {
        (
            name.to_owned(),
            UserType::Alias(parse_type(ty).expect("a type")),
        )
    };
    let none = BTreeMap::new();
    for (types, cycle) in [
        (vec![holding("A", "A")], "(A -> A)"),
        (vec![holding("A", "A[3]")], "(A -> A)"),
        (vec![holding("A", "B"), holding("B", "A")], "(A -> B -> A)"),
        (vec![holding("A", "T"), alias("T", "A[2]")], "(A -> T -> A)"),
    ] {
        let types: BTreeMap<_, _> = types.into_iter().collect();
        let err = validate(&types, &none).expect_err("a type holding itself validated");
        let says = format!("holds itself by value {cycle}");
        assert!(err.to_string().contains(&says), "{err}");
    }
    let linked = [holding("A", "B *"), holding("B", "A *")].into();
    assert!(validate(&linked, &none).is_ok());
}

/// A ring of 4096 structs of long names, each holding the next by value,
/// is refused in a line: the refusal named every type around the ring, a
/// megabyte of text.
#[test]
fn a_long_ring_of_types_is_refused_in_a_short_message() {
    let name = |k: usize| format!("S{k:04}{}", "x".repeat(251));
    let types: BTreeMap<String, UserType> = (0..TYPES_MAX)
        .map(|k| {
            let ty = TypeExpr::Named(name((k + 1) % TYPES_MAX));
            let f = UserField {
                name: "f".to_owned(),
                ty,
            };
            let fields = [(0, f)].into();
            (name(k), UserType::Struct(UserStruct { size: 8, fields }))
        })
        .collect();
    let err = validate(&types, &BTreeMap::new())
        .expect_err("a ring holds itself")
        .to_string();
    assert!(
        err.contains("holds itself by value") && err.contains("... 4088 more ->"),
        "{err}"
    );
    assert!(err.len() < 4096, "{} bytes", err.len());
}

/// A declaration embedding the first of seven structs, each holding the
/// next 256 times, is read in bounded time.
///
/// Its alignment walked every field of every level below it, `256^7`
/// steps; a chain of structs holds no cycle, so it validates.
#[test]
fn a_declaration_over_structs_nested_deep_is_read_in_bounded_time() {
    let known: BTreeMap<String, UserType> = (0..7u32)
        .map(|k| {
            let ty = if k == 6 {
                TypeExpr::U8
            } else {
                TypeExpr::Named(format!("S{}", k + 1))
            };
            let stride = 256u64.pow(6 - k);
            let fields = (0..256u64)
                .map(|f| {
                    (
                        f * stride,
                        UserField {
                            name: format!("f{f}"),
                            ty: ty.clone(),
                        },
                    )
                })
                .collect();
            let size = 256 * stride;
            (
                format!("S{k}"),
                UserType::Struct(UserStruct { size, fields }),
            )
        })
        .collect();
    assert!(validate(&known, &BTreeMap::new()).is_ok());
    let abi = Abi {
        word: 8,
        windows: true,
    };
    let (tx, rx) = std::sync::mpsc::channel();
    std::thread::spawn(move || {
        tx.send(parse("struct B { S0 x; };", &known, abi).map(|d| d.types.len()))
    });
    let read = rx
        .recv_timeout(Duration::from_secs(10))
        .expect("the declaration is read within ten seconds");
    assert_eq!(read.ok(), Some(1));
}

/// A typedef a declaration text states over a struct the overlay holds
/// lays out the structs after it by the type it names.
///
/// The struct's alignment, recorded before the text was read, was read
/// back for the typedef, so a byte after it moved to the struct's
/// alignment.
#[test]
fn a_typedef_over_a_known_struct_aligns_as_the_type_it_names() {
    let q = UserField {
        name: "q".to_owned(),
        ty: TypeExpr::U64,
    };
    let wide = UserStruct {
        size: 8,
        fields: [(0, q)].into(),
    };
    let known = [("S".to_owned(), UserType::Struct(wide))].into();
    let abi = Abi {
        word: 8,
        windows: true,
    };
    let text = "typedef unsigned char S; struct T { char a; S b; };";
    let read = parse(text, &known, abi).expect("the text reads");
    let t = read.types.iter().find(|(name, ..)| name == "T");
    let Some((_, UserType::Struct(t), align)) = t else {
        panic!("T is no struct: {:?}", read.types);
    };
    assert_eq!(t.fields.keys().copied().collect::<Vec<_>>(), [0, 1]);
    assert_eq!((t.size, *align), (2, 1));
    let s = read.types.iter().find(|(name, ..)| name == "S");
    assert_eq!(s.map(|(_, _, align)| *align), Some(1));
}
