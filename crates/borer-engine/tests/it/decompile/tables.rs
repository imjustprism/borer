//! Name tables: constants printed by the names a value-to-name function
//! pairs them with, and only where C reads the name as that value.

use std::collections::BTreeMap;

use super::*;
use borer_engine::analysis::decompile::{EnumTable, apply_enums};
use borer_engine::analysis::utypes::{build_enum, parse_type};

/// Where [`program64_with_data`] maps `.text`.
const TEXT: u64 = 0x1_4000_1000;

/// Where [`program64_with_data`] maps `.rdata`.
const RDATA: u64 = 0x1_4000_2000;

/// Appends `lea rax,[rip+target]; ret` to `.text` bytes that start at
/// [`TEXT`].
///
/// # Arguments
///
/// * `code` - The bytes so far.
/// * `target` - The address the `lea` loads.
#[expect(
    clippy::unwrap_used,
    reason = "a fixture builder: every target is within 2 GB of the code"
)]
fn lea_ret(code: &mut Vec<u8>, target: u64) {
    let end = TEXT + u64::try_from(code.len()).unwrap() + 7;
    let disp = i32::try_from(target.cast_signed() - end.cast_signed()).unwrap();
    code.extend_from_slice(&[0x48, 0x8d, 0x05]);
    code.extend_from_slice(&disp.to_le_bytes());
    code.push(0xc3);
}

/// A program whose value-to-name function compares `ecx` with each case's
/// value and returns the address of that case's text, else of
/// `"Unknown value"`, after `prefix` (a caller, or nothing).
///
/// # Arguments
///
/// * `prefix` - Code before the function, from [`TEXT`].
/// * `cases` - `(value, text)` per case; each text at most 15 bytes.
#[expect(clippy::unwrap_used, reason = "a fixture builder: offsets are small")]
fn named_values(prefix: &[u8], cases: [(u8, &str); 3]) -> borer_engine::program::Program {
    let mut code = prefix.to_vec();
    for (i, (value, _)) in cases.iter().enumerate() {
        let skip = 15 + 8 + 8 * i - 5 * (i + 1);
        code.extend_from_slice(&[0x83, 0xf9, *value, 0x74, u8::try_from(skip).unwrap()]);
    }
    lea_ret(&mut code, RDATA);
    let mut data = vec![0u8; 0x40];
    data[..13].copy_from_slice(b"Unknown value");
    for (i, (_, text)) in cases.iter().enumerate() {
        let at = 0x10 * (i + 1);
        lea_ret(&mut code, RDATA + u64::try_from(at).unwrap());
        data[at..at + text.len()].copy_from_slice(text.as_bytes());
    }
    program64_with_data(&code, &data)
}

/// A table member that is no identifier stays a number, in the function's
/// own body and in a caller's argument.
///
/// The function returns `".STRUCT"` for 3, `".ENUM"` for 4 and
/// `"Undefined"` for 5, the shape of cc65's `GetScopeType`, so its table
/// pairs each value with its literal. `case .STRUCT:` is no C. The caller
/// passes 3 and 5 to it, decompiled with the tables of the functions it
/// calls.
#[test]
fn a_table_member_that_is_no_identifier_stays_a_number() {
    let cases = [(3, ".STRUCT"), (4, ".ENUM"), (5, "Undefined")];
    let text = decompiled(&named_values(&[], cases), TEXT);
    assert!(text.contains("switch (a1)"), "{text}");
    assert!(!text.contains("case ."), "{text}");
    for label in ["case 3:", "case 4:", "case Undefined:"] {
        assert!(text.contains(label), "{label}\n{text}");
    }
    let mut caller = vec![
        0x48, 0x83, 0xec, 0x28, // ASM: sub rsp,0x28
        0xb9, 0x03, 0x00, 0x00, 0x00, // ASM: mov ecx,3
        0xe8, 0x12, 0x00, 0x00, 0x00, // ASM: call named
        0xb9, 0x05, 0x00, 0x00, 0x00, // ASM: mov ecx,5
        0xe8, 0x08, 0x00, 0x00, 0x00, // ASM: call named
        0x48, 0x83, 0xc4, 0x28, // ASM: add rsp,0x28
        0xc3, // ASM: ret
    ];
    caller.resize(0x20, 0xcc);
    let p = named_values(&caller, cases);
    let a = Analysis::compute(&p);
    let o = Overlay {
        enum_source: EnumSource::Binary,
        ..Overlay::default()
    };
    let text = decompile(&p, &a, &o, TEXT).unwrap_or_default();
    assert!(text.contains("sub_140001020(3)"), "{text}");
    assert!(text.contains("sub_140001020(Undefined)"), "{text}");
}

/// A member C reads as something else stays a number: a keyword of any C
/// standard, a name two values share, or a name the function already uses.
///
/// `case true:` would read as 1, `case inline:` does not parse, two `case
/// Foo:` labels are ambiguous, and `case a1:` in `switch (a1)` names the
/// parameter.
#[test]
fn a_member_c_reads_otherwise_stays_a_number() {
    for (cases, labels) in [
        (
            [(3, "true"), (4, "false"), (5, "inline")],
            ["case 3:", "case 4:", "case 5:"],
        ),
        (
            [(3, "Foo"), (4, "Foo"), (5, "Bar")],
            ["case 3:", "case 4:", "case Bar:"],
        ),
        (
            [(3, "a1"), (4, "Foo"), (5, "Bar")],
            ["case 3:", "case Foo:", "case Bar:"],
        ),
    ] {
        let text = decompiled(&named_values(&[], cases), TEXT);
        assert!(text.contains("switch (a1)"), "{text}");
        for label in labels {
            assert!(text.contains(label), "{label}\n{text}");
        }
    }
}

/// A parser's result carries its table: its `case` labels, its compares
/// and a compare of the call itself name the members C can read, and no
/// others.
#[test]
fn a_parser_result_names_only_the_members_c_reads() {
    let members = [
        (1, "Red"),
        (2, "Green"),
        (3, ".x"),
        (4, "v"),
        (5, "Blue"),
        (6, "Blue"),
    ];
    let table = EnumTable {
        name: "by strcmp compare".to_owned(),
        members: members.iter().map(|&(k, n)| (k, n.to_owned())).collect(),
        param: None,
    };
    let tables = BTreeMap::from([("parse".to_owned(), table)]);
    let body = "v = parse(a1);\nif (v == 2) {\n  return 0;\n}\nswitch (v) {\ncase 1:\n  break;\ncase 3:\n  break;\ncase 4:\n  break;\ncase 5:\n  break;\n}\nif (parse(a2) == 1) {\n  return 1;\n}\n";
    let out = apply_enums(body, &tables);
    for said in [
        "if (v == Green) {",
        "case Red:",
        "case 3:",
        "case 4:",
        "case 5:",
        "if (parse(a2) == Red) {",
    ] {
        assert!(out.contains(said), "{said}\n{out}");
    }
}

/// A user's enum on a global names a compared value C reads as its
/// member, and no other: the user states the names, but `inline` is a
/// keyword and `g32_140003000` the global itself.
#[test]
fn a_user_enum_names_only_the_members_c_reads() {
    let code = [
        0x8b, 0x05, 0xfa, 0x1f, 0x00, 0x00, // ASM: mov eax,[rip+global]
        0x83, 0xf8, 0x02, // ASM: cmp eax,2
        0x74, 0x03, // ASM: je two
        0x31, 0xc0, // ASM: xor eax,eax
        0xc3, // ASM: ret
        0xb8, 0x14, 0x00, 0x00, 0x00, // ASM: mov eax,20
        0xc3, // ASM: ret
    ];
    let p = program64_with_globals(&code, false, &[]);
    let a = Analysis::compute(&p);
    for (member, said) in [
        ("Run", "g32_140003000 == Run"),
        ("inline", "g32_140003000 == 2"),
        ("g32_140003000", "g32_140003000 == 2"),
    ] {
        let mut o = Overlay::default();
        let state = build_enum("State", 4, &[(2, member.to_owned())]).expect("an enum");
        o.types.insert("State".to_owned(), state);
        o.applied
            .insert(0x1_4000_3000, parse_type("State").expect("a type"));
        let text = decompile(&p, &a, &o, TEXT).unwrap_or_default();
        assert!(
            text.contains(said),
            "{said}
{text}"
        );
    }
}
