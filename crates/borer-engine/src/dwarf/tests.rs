use super::Strings;

/// Runs [`super::read_in`] with a fresh [`super::Text`] budget for a test.
fn read_in(info: &[u8], abbrev: &[u8], strings: &Strings<'_>) -> super::Debug {
    super::read_in(info, abbrev, strings, &mut super::Text::new(strings))
}

/// Builds an abbreviation table declaring a function and a parameter.
fn abbrev() -> Vec<u8> {
    vec![
        0x01, 0x2e, 0x01, 0x03, 0x08, 0x11, 0x01, 0x00, 0x00, 0x02, 0x05, 0x00, 0x03, 0x08, 0x00,
        0x00, 0x00,
    ]
}

/// Wraps `dies` in a DWARF 5 unit header.
fn unit(dies: &[u8]) -> Vec<u8> {
    let mut body: Vec<u8> = Vec::new();
    body.extend_from_slice(&5u16.to_le_bytes());
    body.push(0x01);
    body.push(8);
    body.extend_from_slice(&0u32.to_le_bytes());
    body.extend_from_slice(dies);
    let mut out = u32::try_from(body.len())
        .expect("fits")
        .to_le_bytes()
        .to_vec();
    out.extend_from_slice(&body);
    out
}

/// A named function with its parameters is read out of a unit.
#[test]
fn a_named_function_is_read() {
    let mut dies: Vec<u8> = Vec::new();
    dies.push(0x01);
    dies.extend_from_slice(b"main\0");
    dies.extend_from_slice(&0x0001_4000u64.to_le_bytes());
    dies.push(0x02);
    dies.extend_from_slice(b"argc\0");
    dies.push(0x02);
    dies.extend_from_slice(b"argv\0");
    dies.push(0x00);
    let info = unit(&dies);
    let strings = Strings {
        text: &[],
        lines: &[],
    };
    let found = read_in(&info, &abbrev(), &strings).subprograms;
    assert_eq!(found.len(), 1, "{found:?}");
    assert_eq!(found[0].low_pc, 0x0001_4000);
    assert_eq!(found[0].name, "main");
    let names: Vec<&str> = found[0]
        .parameters
        .iter()
        .map(|p| p.name.as_str())
        .collect();
    assert_eq!(names, vec!["argc", "argv"]);
}

/// The parameters of a call inlined into a function are the inlined
/// callee's, not the function's: `sgr_dbname` took none, and the
/// `__dest` of the `memcpy` inlined into it read as its parameter.
#[test]
fn an_inlined_call_s_parameters_are_not_the_function_s() {
    let mut abbrev = abbrev();
    abbrev.pop();
    abbrev.extend_from_slice(&[0x03, 0x1d, 0x01, 0x00, 0x00, 0x00]);
    let mut dies: Vec<u8> = Vec::new();
    dies.push(0x01);
    dies.extend_from_slice(b"f\0");
    dies.extend_from_slice(&0x1000u64.to_le_bytes());
    dies.push(0x02);
    dies.extend_from_slice(b"argc\0");
    dies.push(0x03);
    dies.push(0x02);
    dies.extend_from_slice(b"__dest\0");
    dies.push(0x00);
    dies.push(0x00);
    let info = unit(&dies);
    let strings = Strings {
        text: &[],
        lines: &[],
    };
    let found = read_in(&info, &abbrev, &strings).subprograms;
    assert_eq!(found.len(), 1, "{found:?}");
    let names: Vec<&str> = found[0]
        .parameters
        .iter()
        .map(|p| p.name.as_str())
        .collect();
    assert_eq!(names, vec!["argc"]);
}

/// A typedef reads as the C type it stands for, and one of an unnamed
/// structure as that structure under the typedef's own name.
#[test]
fn a_typedef_reads_as_what_it_stands_for() {
    let abbrev: Vec<u8> = vec![
        0x01, 0x16, 0x00, 0x03, 0x08, 0x49, 0x13, 0x00, 0x00, 0x02, 0x24, 0x00, 0x03, 0x08, 0x00,
        0x00, 0x03, 0x13, 0x00, 0x00, 0x00, 0x00,
    ];
    let mut dies: Vec<u8> = vec![0x01];
    dies.extend_from_slice(b"uLong\0");
    dies.extend_from_slice(&33u32.to_le_bytes());
    dies.push(0x01);
    dies.extend_from_slice(b"Bits\0");
    dies.extend_from_slice(&52u32.to_le_bytes());
    let base_at = 12 + dies.len();
    dies.push(0x02);
    dies.extend_from_slice(b"long unsigned int\0");
    let struct_at = 12 + dies.len();
    dies.push(0x03);
    assert_eq!(
        (base_at, struct_at),
        (33, 52),
        "the offsets the references assume"
    );
    let info = unit(&dies);
    let strings = Strings {
        text: &[],
        lines: &[],
    };
    let typedefs = read_in(&info, &abbrev, &strings).typedefs;
    let got: Vec<(&str, &str)> = typedefs
        .iter()
        .map(|(n, t)| (n.as_str(), t.as_str()))
        .collect();
    assert_eq!(
        got,
        vec![("Bits", "struct Bits"), ("uLong", "long unsigned int")]
    );
}

/// A name held in `.debug_str` is resolved through the offset.
#[test]
fn a_name_resolves_through_the_string_section() {
    let abbrev: Vec<u8> = vec![0x01, 0x2e, 0x00, 0x03, 0x0e, 0x11, 0x01, 0x00, 0x00, 0x00];
    let mut dies: Vec<u8> = vec![0x01];
    dies.extend_from_slice(&4u32.to_le_bytes());
    dies.extend_from_slice(&0x2000u64.to_le_bytes());
    let info = unit(&dies);
    let strings = Strings {
        text: b"one\0resolved\0",
        lines: &[],
    };
    let found = read_in(&info, &abbrev, &strings).subprograms;
    assert_eq!(found.len(), 1, "{found:?}");
    assert_eq!(found[0].name, "resolved");
}

/// A type is read by following the chain of entries that build it.
///
/// A parameter points at a pointer, which points at a const, which points
/// at a base type, and only the whole chain says `const char *`.
#[test]
fn a_type_chain_reads_as_c_source() {
    let abbrev: Vec<u8> = vec![
        0x01, 0x2e, 0x01, 0x03, 0x08, 0x11, 0x01, 0x49, 0x13, 0x00, 0x00, 0x02, 0x05, 0x00, 0x03,
        0x08, 0x49, 0x13, 0x00, 0x00, 0x03, 0x0f, 0x00, 0x49, 0x13, 0x00, 0x00, 0x04, 0x26, 0x00,
        0x49, 0x13, 0x00, 0x00, 0x05, 0x24, 0x00, 0x03, 0x08, 0x00, 0x00, 0x00,
    ];
    let mut dies: Vec<u8> = Vec::new();
    dies.push(0x01);
    dies.extend_from_slice(b"f\0");
    dies.extend_from_slice(&0x1000u64.to_le_bytes());
    dies.extend_from_slice(&45u32.to_le_bytes());
    let param_at = 12 + dies.len();
    dies.push(0x02);
    dies.extend_from_slice(b"s\0");
    dies.extend_from_slice(&35u32.to_le_bytes());
    dies.push(0x00);
    let pointer_at = 12 + dies.len();
    dies.push(0x03);
    dies.extend_from_slice(&40u32.to_le_bytes());
    let const_at = 12 + dies.len();
    dies.push(0x04);
    dies.extend_from_slice(&45u32.to_le_bytes());
    let base_at = 12 + dies.len();
    dies.push(0x05);
    dies.extend_from_slice(b"char\0");
    assert_eq!(
        (param_at, pointer_at, const_at, base_at),
        (27, 35, 40, 45),
        "the offsets the references assume"
    );
    let info = unit(&dies);
    let strings = Strings {
        text: &[],
        lines: &[],
    };
    let found = read_in(&info, &abbrev, &strings).subprograms;
    assert_eq!(found.len(), 1, "{found:?}");
    assert_eq!(found[0].return_type.as_deref(), Some("char"));
    assert_eq!(found[0].parameters.len(), 1);
    assert_eq!(
        found[0].parameters[0].type_name.as_deref(),
        Some("const char *")
    );
}

/// Builds an abbreviation table declaring subprograms that state a
/// frame base, variables that state a location, and a lexical block.
fn locals_abbrev() -> Vec<u8> {
    vec![
        0x01, 0x2e, 0x01, 0x03, 0x08, 0x11, 0x01, 0x40, 0x09, 0x00, 0x00, 0x02, 0x34, 0x00, 0x03,
        0x08, 0x02, 0x09, 0x00, 0x00, 0x03, 0x0b, 0x01, 0x00, 0x00, 0x00,
    ]
}

/// Appends a variable's entry: code, name, then an exprloc.
fn variable(dies: &mut Vec<u8>, code: u8, name: &str, expr: &[u8]) {
    dies.push(code);
    dies.extend_from_slice(name.as_bytes());
    dies.push(0);
    dies.push(u8::try_from(expr.len()).expect("fits"));
    dies.extend_from_slice(expr);
}

/// A frame-relative variable lands on the slot its subprogram's frame
/// base states, whatever base the compiler chose.
///
/// The caller's frame base sits a word above the entry stack pointer,
/// the frame pointer's a word under it, so the same `DW_OP_fbreg`
/// offset names a different slot under each. A variable inside a
/// lexical block still lives in its function's frame, and a name the
/// text synthesizes for itself, a slot past the span a frame holds, the
/// return address's own slot, a location no whole `DW_OP_fbreg` states,
/// another local's slot, and a frame base this reader does not reduce
/// all leave the map without their name.
#[test]
fn fbreg_locals_land_by_their_frame_base() {
    let mut dies: Vec<u8> = Vec::new();
    dies.push(0x01);
    dies.extend_from_slice(b"cfa_fn\0");
    dies.extend_from_slice(&0x1000u64.to_le_bytes());
    dies.push(1);
    dies.extend_from_slice(&[0x9c]);
    variable(&mut dies, 0x02, "a", &[0x91, 0x68]);
    dies.push(0x03);
    variable(&mut dies, 0x02, "b", &[0x91, 0x70]);
    dies.push(0x00);
    variable(&mut dies, 0x02, "local_8", &[0x91, 0x60]);
    variable(&mut dies, 0x02, "at_zero", &[0x91, 0x78]);
    variable(&mut dies, 0x02, "far", &[0x91, 0x80, 0x80, 0x04]);
    variable(&mut dies, 0x02, "reg", &[0x50]);
    variable(&mut dies, 0x02, "empty", &[]);
    variable(&mut dies, 0x02, "again", &[0x91, 0x68]);
    dies.push(0x00);
    dies.push(0x01);
    dies.extend_from_slice(b"bp_fn\0");
    dies.extend_from_slice(&0x2000u64.to_le_bytes());
    dies.push(1);
    dies.extend_from_slice(&[0x56]);
    variable(&mut dies, 0x02, "c", &[0x91, 0x70]);
    dies.push(0x00);
    dies.push(0x01);
    dies.extend_from_slice(b"odd_fn\0");
    dies.extend_from_slice(&0x3000u64.to_le_bytes());
    dies.push(2);
    dies.extend_from_slice(&[0x77, 0x00]);
    variable(&mut dies, 0x02, "h", &[0x91, 0x70]);
    dies.push(0x00);
    let info = unit(&dies);
    let strings = Strings {
        text: &[],
        lines: &[],
    };
    let found = read_in(&info, &locals_abbrev(), &strings).subprograms;
    assert_eq!(found.len(), 3, "{found:?}");
    let locals = |name: &str| {
        found
            .iter()
            .find(|f| f.name == name)
            .unwrap_or_else(|| panic!("no {name}"))
            .locals
            .clone()
    };
    assert_eq!(
        locals("cfa_fn"),
        [(-0x10, "a".to_owned()), (-0x08, "b".to_owned())]
            .into_iter()
            .collect::<std::collections::BTreeMap<_, _>>()
    );
    assert_eq!(
        locals("bp_fn"),
        [(-0x18i64, "c".to_owned())].into_iter().collect()
    );
    assert!(locals("odd_fn").is_empty(), "an unread base names nothing");
}

/// A 32-bit unit's frame pointer is `ebp`, register 5, and its caller
/// base crosses by the four-byte word.
#[test]
fn a_32_bit_frame_pointer_is_ebp() {
    let abbrev: Vec<u8> = vec![
        0x01, 0x2e, 0x01, 0x03, 0x08, 0x11, 0x01, 0x40, 0x09, 0x00, 0x00, 0x02, 0x34, 0x00, 0x03,
        0x08, 0x02, 0x09, 0x00, 0x00, 0x00,
    ];
    let mut body: Vec<u8> = Vec::new();
    body.extend_from_slice(&5u16.to_le_bytes());
    body.push(0x01);
    body.push(4);
    body.extend_from_slice(&0u32.to_le_bytes());
    body.push(0x01);
    body.extend_from_slice(b"fn32\0");
    body.extend_from_slice(&0x4000u32.to_le_bytes());
    body.push(1);
    body.extend_from_slice(&[0x55]);
    variable(&mut body, 0x02, "d", &[0x91, 0x70]);
    body.push(0x00);
    let mut info = u32::try_from(body.len())
        .expect("fits")
        .to_le_bytes()
        .to_vec();
    info.extend_from_slice(&body);
    let strings = Strings {
        text: &[],
        lines: &[],
    };
    let found = read_in(&info, &abbrev, &strings).subprograms;
    assert_eq!(found.len(), 1, "{found:?}");
    assert_eq!(
        found[0].locals,
        [(-0x14i64, "d".to_owned())].into_iter().collect()
    );
}

/// Builds an abbreviation table declaring the entries a stated type
/// walks: structures, members, base types, pointers, enumerations and
/// enumerators.
fn types_abbrev() -> Vec<u8> {
    vec![
        0x01, 0x13, 0x01, 0x03, 0x08, 0x0b, 0x0b, 0x00, 0x00, 0x02, 0x0d, 0x00, 0x03, 0x08, 0x38,
        0x0b, 0x49, 0x13, 0x00, 0x00, 0x03, 0x24, 0x00, 0x03, 0x08, 0x0b, 0x0b, 0x3e, 0x0b, 0x00,
        0x00, 0x04, 0x0f, 0x00, 0x49, 0x13, 0x00, 0x00, 0x05, 0x04, 0x01, 0x03, 0x08, 0x0b, 0x0b,
        0x00, 0x00, 0x06, 0x28, 0x00, 0x03, 0x08, 0x1c, 0x0b, 0x00, 0x00, 0x07, 0x13, 0x01, 0x0b,
        0x0b, 0x00, 0x00, 0x00,
    ]
}

/// Appends a `DW_FORM_string` name to the entries under construction.
fn named(dies: &mut Vec<u8>, name: &str) {
    dies.extend_from_slice(name.as_bytes());
    dies.push(0);
}

/// A struct's members and an enum's constants land as the types the
/// user-type language spells.
///
/// A member resolves through its whole chain - a base type by its
/// encoding, a pointer to what it points at, a named enum by its name -
/// while one that repeats another's offset, one whose reference points
/// at nothing, and one inside an anonymous struct contribute nothing,
/// because none states a field an agent could state back.
#[test]
fn struct_members_and_enum_constants_land_as_types() {
    use crate::analysis::utypes::{TypeExpr, UserStruct, UserType};
    use std::collections::BTreeMap;
    let mut dies: Vec<u8> = Vec::new();
    let die_at = |dies: &[u8]| u32::try_from(12 + dies.len()).expect("fits");
    let u32_at = die_at(&dies);
    dies.push(0x03);
    named(&mut dies, "unsigned int");
    dies.push(4);
    dies.push(0x07);
    let char_at = die_at(&dies);
    dies.push(0x03);
    named(&mut dies, "char");
    dies.push(1);
    dies.push(0x06);
    let ptr_at = die_at(&dies);
    dies.push(0x04);
    dies.extend_from_slice(&char_at.to_le_bytes());
    let enum_at = die_at(&dies);
    dies.push(0x05);
    named(&mut dies, "E");
    dies.push(4);
    for (name, value) in [("A", 0u8), ("B", 3u8)] {
        dies.push(0x06);
        named(&mut dies, name);
        dies.push(value);
    }
    dies.push(0x00);
    dies.push(0x01);
    named(&mut dies, "Point");
    dies.push(16);
    for (name, off, ty) in [
        ("x", 0u8, u32_at),
        ("text", 8, ptr_at),
        ("kind", 12, enum_at),
        ("dup", 0, u32_at),
        ("lost", 20, u32_at + 1),
    ] {
        dies.push(0x02);
        named(&mut dies, name);
        dies.push(off);
        dies.extend_from_slice(&ty.to_le_bytes());
    }
    dies.push(0x07);
    dies.push(4);
    dies.push(0x02);
    named(&mut dies, "inner");
    dies.push(0);
    dies.extend_from_slice(&u32_at.to_le_bytes());
    dies.push(0x00);
    dies.push(0x00);
    let info = unit(&dies);
    let strings = Strings {
        text: &[],
        lines: &[],
    };
    let read = read_in(&info, &types_abbrev(), &strings);
    assert!(read.subprograms.is_empty());
    let e = read.types.get("E").expect("the enum is stated");
    assert_eq!(
        e,
        &UserType::Enum(crate::analysis::utypes::UserEnum {
            size: 4,
            values: vec![(0, "A".to_owned()), (3, "B".to_owned())],
        })
    );
    let point = read.types.get("Point").expect("the struct is stated");
    let UserStruct { size, fields } = match point {
        UserType::Struct(s) => s,
        other => panic!("Point is not a struct: {other:?}"),
    };
    assert_eq!(*size, 16);
    assert_eq!(
        fields,
        &BTreeMap::from([
            (
                0u64,
                crate::analysis::utypes::UserField {
                    name: "x".to_owned(),
                    ty: TypeExpr::U32,
                }
            ),
            (
                8,
                crate::analysis::utypes::UserField {
                    name: "text".to_owned(),
                    ty: TypeExpr::Ptr(Box::new(TypeExpr::Char)),
                }
            ),
            (
                12,
                crate::analysis::utypes::UserField {
                    name: "kind".to_owned(),
                    ty: TypeExpr::Named("E".to_owned()),
                }
            ),
        ])
    );
}

/// The variables of static storage land with their addresses and
/// types: a scalar, an array of its stated length, and a declaration of
/// one another unit defines, found by its name and ordered first.
#[test]
fn globals_land_with_their_addresses_and_types() {
    use super::Global;
    use crate::analysis::utypes::TypeExpr;
    let abbrev: Vec<u8> = vec![
        0x01, 0x24, 0x00, 0x03, 0x08, 0x0b, 0x0b, 0x3e, 0x0b, 0x00, 0x00, 0x02, 0x34, 0x00, 0x03,
        0x08, 0x49, 0x13, 0x02, 0x18, 0x00, 0x00, 0x03, 0x34, 0x00, 0x03, 0x08, 0x49, 0x13, 0x00,
        0x00, 0x04, 0x01, 0x01, 0x49, 0x13, 0x00, 0x00, 0x05, 0x21, 0x00, 0x2f, 0x0b, 0x00, 0x00,
        0x06, 0x0f, 0x00, 0x49, 0x13, 0x00, 0x00, 0x00,
    ];
    let mut dies: Vec<u8> = Vec::new();
    let die_at = |dies: &[u8]| u32::try_from(12 + dies.len()).expect("fits");
    let int_at = die_at(&dies);
    dies.push(0x01);
    named(&mut dies, "int");
    dies.extend_from_slice(&[4, 0x05]);
    let char_at = die_at(&dies);
    dies.push(0x01);
    named(&mut dies, "char");
    dies.extend_from_slice(&[1, 0x06]);
    let ptr_at = die_at(&dies);
    dies.push(0x06);
    dies.extend_from_slice(&char_at.to_le_bytes());
    let array_at = die_at(&dies);
    dies.push(0x04);
    dies.extend_from_slice(&int_at.to_le_bytes());
    dies.extend_from_slice(&[0x05, 9, 0x00]);
    for (name, ty, addr) in [("count", int_at, 0x4010u64), ("table", array_at, 0x4020)] {
        dies.push(0x02);
        named(&mut dies, name);
        dies.extend_from_slice(&ty.to_le_bytes());
        dies.extend_from_slice(&[9, 0x03]);
        dies.extend_from_slice(&addr.to_le_bytes());
    }
    dies.push(0x03);
    named(&mut dies, "optarg");
    dies.extend_from_slice(&ptr_at.to_le_bytes());
    let info = unit(&dies);
    let strings = Strings {
        text: &[],
        lines: &[],
    };
    let globals = read_in(&info, &abbrev, &strings).globals;
    assert_eq!(
        globals,
        vec![
            Global {
                name: "optarg".to_owned(),
                addr: None,
                type_name: Some("char *".to_owned()),
                ty: Some(TypeExpr::Ptr(Box::new(TypeExpr::Char))),
            },
            Global {
                name: "count".to_owned(),
                addr: Some(0x4010),
                type_name: Some("int".to_owned()),
                ty: Some(TypeExpr::I32),
            },
            Global {
                name: "table".to_owned(),
                addr: Some(0x4020),
                type_name: Some("int[]".to_owned()),
                ty: Some(TypeExpr::Array(Box::new(TypeExpr::I32), 10)),
            },
        ]
    );
}

/// A typedef of a struct lands as an alias of it, so a pointer to the
/// typedef (`ARRAY *`) reaches the struct's fields.
#[test]
fn a_typedef_of_a_struct_is_its_alias() {
    use crate::analysis::utypes::{TypeExpr, UserType};
    let abbrev: Vec<u8> = vec![
        0x01, 0x13, 0x01, 0x03, 0x08, 0x0b, 0x0b, 0x00, 0x00, 0x02, 0x0d, 0x00, 0x03, 0x08, 0x38,
        0x0b, 0x49, 0x13, 0x00, 0x00, 0x03, 0x24, 0x00, 0x03, 0x08, 0x0b, 0x0b, 0x3e, 0x0b, 0x00,
        0x00, 0x04, 0x16, 0x00, 0x03, 0x08, 0x49, 0x13, 0x00, 0x00, 0x00,
    ];
    let mut dies: Vec<u8> = Vec::new();
    let die_at = |dies: &[u8]| u32::try_from(12 + dies.len()).expect("fits");
    let int_at = die_at(&dies);
    dies.push(0x03);
    named(&mut dies, "int");
    dies.extend_from_slice(&[4, 0x05]);
    let struct_at = die_at(&dies);
    dies.push(0x01);
    named(&mut dies, "array");
    dies.push(8);
    dies.push(0x02);
    named(&mut dies, "num");
    dies.push(0);
    dies.extend_from_slice(&int_at.to_le_bytes());
    dies.push(0x00);
    dies.push(0x04);
    named(&mut dies, "ARRAY");
    dies.extend_from_slice(&struct_at.to_le_bytes());
    let info = unit(&dies);
    let strings = Strings {
        text: &[],
        lines: &[],
    };
    let types = read_in(&info, &abbrev, &strings).types;
    assert_eq!(
        types.get("ARRAY"),
        Some(&UserType::Alias(TypeExpr::Named("array".to_owned())))
    );
    assert!(matches!(types.get("array"), Some(UserType::Struct(_))));
}

/// An enum a value names twice is refused whole, and one whose width
/// the language does not spell lands not at all.
#[test]
fn enums_the_language_cannot_state_land_nowhere() {
    let mut dies: Vec<u8> = Vec::new();
    for (name, size) in [("Twice", 4u8), ("Narrow", 1u8)] {
        dies.push(0x05);
        named(&mut dies, name);
        dies.push(size);
        for (member, value) in [("A", 0u8), ("Also", 0u8)] {
            dies.push(0x06);
            named(&mut dies, member);
            dies.push(value);
        }
        dies.push(0x00);
    }
    let info = unit(&dies);
    let strings = Strings {
        text: &[],
        lines: &[],
    };
    let read = read_in(&info, &types_abbrev(), &strings);
    assert!(read.types.is_empty(), "{:?}", read.types.keys());
}

/// Arbitrary bytes are read without panicking, and name nothing.
///
/// A reader of a rebuilt or damaged image is handed whatever the file
/// holds, so every path out of it has to be a `None`, not a panic.
#[test]
fn arbitrary_bytes_name_nothing() {
    let strings = Strings {
        text: &[],
        lines: &[],
    };
    assert!(read_in(&[], &[], &strings).subprograms.is_empty());
    let noise: Vec<u8> = (0..4096u32).map(|k| (k * 31 % 253) as u8).collect();
    let _ = read_in(&noise, &noise, &strings);
    let truncated = unit(&[0x01]);
    let _ = read_in(&truncated, &abbrev(), &strings);
    for cut in 0..truncated.len() {
        let _ = read_in(&truncated[..cut], &abbrev(), &strings);
    }
}

/// A name longer than [`super::STRING_MAX`] names nothing, inline or
/// out of the string section, and a section with no NUL is not read
/// past the cap.
#[test]
fn a_name_past_the_string_cap_names_nothing() {
    let long = "n".repeat(super::STRING_MAX + 1);
    let mut dies: Vec<u8> = vec![0x01];
    dies.extend_from_slice(long.as_bytes());
    dies.push(0);
    dies.extend_from_slice(&0x1000u64.to_le_bytes());
    dies.push(0x00);
    dies.push(0x01);
    dies.extend_from_slice(b"kept\0");
    dies.extend_from_slice(&0x2000u64.to_le_bytes());
    dies.push(0x00);
    let strings = Strings {
        text: &[],
        lines: &[],
    };
    let found = read_in(&unit(&dies), &abbrev(), &strings).subprograms;
    let names: Vec<&str> = found.iter().map(|f| f.name.as_str()).collect();
    assert_eq!(names, vec!["kept"]);
    let abbrev: Vec<u8> = vec![0x01, 0x2e, 0x00, 0x03, 0x0e, 0x11, 0x01, 0x00, 0x00, 0x00];
    let mut section = long.into_bytes();
    section.push(0);
    let mut dies: Vec<u8> = vec![0x01];
    dies.extend_from_slice(&0u32.to_le_bytes());
    dies.extend_from_slice(&0x2000u64.to_le_bytes());
    let strings = Strings {
        text: &section,
        lines: &[],
    };
    assert!(
        read_in(&unit(&dies), &abbrev, &strings)
            .subprograms
            .is_empty()
    );
}

/// Entries that all name one long string stop at the copy budget.
///
/// The string is not copied once per entry past it, and offsets into
/// the middle of one string read no more than the budget for distinct
/// strings allows.
#[test]
fn one_long_name_named_everywhere_stops_at_the_budget() {
    let abbrev: Vec<u8> = vec![0x01, 0x2e, 0x00, 0x03, 0x0e, 0x11, 0x01, 0x00, 0x00, 0x00];
    let name_len = super::STRING_MAX;
    let mut section = vec![b'n'; name_len];
    section.push(0);
    let entries = super::TEXT_MAX / name_len + 16;
    let mut info = Vec::new();
    let mut dies: Vec<u8> = Vec::new();
    for k in 0..entries {
        if dies.len() > 1 << 20 {
            info.extend_from_slice(&unit(&dies));
            dies.clear();
        }
        dies.push(0x01);
        dies.extend_from_slice(&0u32.to_le_bytes());
        dies.extend_from_slice(&u64::try_from(k).expect("fits").to_le_bytes());
    }
    info.extend_from_slice(&unit(&dies));
    let strings = Strings {
        text: &section,
        lines: &[],
    };
    let found = read_in(&info, &abbrev, &strings).subprograms;
    assert!(!found.is_empty());
    assert!(
        found.len() <= super::TEXT_MAX / name_len,
        "{} entries copied a {name_len}-byte name",
        found.len()
    );
    let mut dies: Vec<u8> = Vec::new();
    for k in 0..name_len {
        dies.push(0x01);
        dies.extend_from_slice(&u32::try_from(k).expect("fits").to_le_bytes());
        dies.extend_from_slice(&u64::try_from(k).expect("fits").to_le_bytes());
    }
    let mut text = super::Text::new(&strings);
    let budget = text.intern_left;
    let mut read = 0usize;
    for k in 0..name_len {
        read += text.at(&strings, false, k).map_or(0, |s| s.len());
    }
    assert!(read <= budget, "{read} bytes read past {budget}");
    let tails = read_in(&unit(&dies), &abbrev, &strings).subprograms;
    assert!(tails.len() < name_len, "{} tails read", tails.len());
}

/// Units that share one large abbreviation table parse it once, and
/// units pointing into its middle stop parsing at the budget, so the
/// walk costs the table's size, not units times the table.
#[test]
fn a_shared_abbreviation_table_is_parsed_once() {
    let entries = 1usize << 14;
    let mut abbrev: Vec<u8> = Vec::new();
    for code in 1..=entries {
        let mut n = code;
        loop {
            let byte = u8::try_from(n & 0x7f).expect("seven bits");
            n >>= 7;
            if n == 0 {
                abbrev.push(byte);
                break;
            }
            abbrev.push(byte | 0x80);
        }
        abbrev.extend_from_slice(&[0x2e, 0x00, 0x03, 0x08, 0x11, 0x01, 0x00, 0x00]);
    }
    abbrev.push(0);
    let mut tables = super::Abbrevs::new(&abbrev);
    let first = tables.at(0).expect("the table parses");
    assert_eq!(first.len(), entries);
    let left = tables.left;
    for _ in 0..1000 {
        assert!(tables.at(0).is_some());
    }
    assert_eq!(tables.left, left, "a second unit parses nothing again");
    let mut parsed = 0usize;
    for offset in (1..abbrev.len()).step_by(3) {
        parsed += tables.at(offset).map_or(0, |t| t.len());
    }
    assert!(
        parsed <= 2 * entries,
        "{parsed} abbreviations parsed from tails of one table"
    );
    let mut info = Vec::new();
    let die: Vec<u8> = {
        let mut d = vec![0x01];
        d.extend_from_slice(b"f\0");
        d.extend_from_slice(&0x1000u64.to_le_bytes());
        d
    };
    for _ in 0..4000 {
        info.extend_from_slice(&unit(&die));
    }
    let strings = Strings {
        text: &[],
        lines: &[],
    };
    let found = read_in(&info, &abbrev, &strings).subprograms;
    assert_eq!(found.len(), 1, "every unit names f at one address");
}

/// A unit whose stated length runs to the top of the offset space
/// names nothing and ends the walk, rather than adding its offset to
/// the minimum-unit bound and overflowing.
#[test]
fn a_huge_stated_length_ends_the_walk() {
    let mut info = Vec::new();
    info.extend_from_slice(&u32::MAX.to_le_bytes());
    info.extend_from_slice(&(u64::MAX - 12).to_le_bytes());
    info.extend_from_slice(&5u16.to_le_bytes());
    info.push(0x01);
    info.push(8);
    info.extend_from_slice(&[0; 8]);
    let strings = Strings {
        text: &[],
        lines: &[],
    };
    assert!(read_in(&info, &abbrev(), &strings).subprograms.is_empty());
}
