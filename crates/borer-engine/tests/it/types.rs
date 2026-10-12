//! User types over data at rest: a typed read of a table of records.
//!
//! A record type stated once reads every record of a table with its fields
//! named, a nested struct's fields under a dotted path, an enum by its
//! member, a `char` array and a `char` pointer as quoted text, under the
//! caps every listing keeps.

#![expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]

use borer_engine::analysis::Overlay;
use borer_engine::analysis::render::typed_tsv;
use borer_engine::analysis::utypes::{build_enum, build_struct, parse_type};
use borer_engine::program::{Arch, Program, Section};

/// A 64-bit image whose `.rdata` at 0x403000 holds two 0x28-byte records,
/// then their names as C strings at 0x403100.
///
/// Each record is `{ char *name; u32 id; State state; Vec pos; char
/// tag[8]; Rec *next; }`: the first `alpha`, id 1, state 1, pos (1.5,
/// -2.0), tag `ab\x01`, next the second; the second `beta`, id 2, state 5
/// (no member), pos (0.0, 0.25), tag `zzzzzzzz` (no NUL), next null.
fn table() -> Program {
    let mut data = vec![0u8; 0x200];
    let mut put = |at: usize, bytes: &[u8]| data[at..at + bytes.len()].copy_from_slice(bytes);
    put(0x00, &0x403100u64.to_le_bytes());
    put(0x08, &1u32.to_le_bytes());
    put(0x0c, &1u32.to_le_bytes());
    put(0x10, &1.5f32.to_le_bytes());
    put(0x14, &(-2.0f32).to_le_bytes());
    put(0x18, b"ab\x01\0\0\0\0\0");
    put(0x20, &0x403028u64.to_le_bytes());
    put(0x28, &0x403106u64.to_le_bytes());
    put(0x30, &2u32.to_le_bytes());
    put(0x34, &5u32.to_le_bytes());
    put(0x38, &0.0f32.to_le_bytes());
    put(0x3c, &0.25f32.to_le_bytes());
    put(0x40, b"zzzzzzzz");
    put(0x100, b"alpha\0beta\0");
    Program::raw(
        data,
        Arch::X86_64,
        0x400_000,
        None,
        vec![Section::mapped(".rdata", 0x403_000, 0, 0x200, false, false)],
    )
}

/// An overlay stating `Rec`, the `Vec` it embeds and the `State` it holds.
///
/// # Errors
///
/// When a type is refused, which a test then reports.
fn types() -> anyhow::Result<Overlay> {
    let mut o = Overlay::default();
    let vec = build_struct(
        "Vec",
        None,
        &[
            (0, "x".to_owned(), parse_type("f32")?),
            (4, "y".to_owned(), parse_type("f32")?),
        ],
        &o.types,
        8,
    )?;
    o.types.insert("Vec".to_owned(), vec);
    let state = build_enum("State", 4, &[(0, "Idle".to_owned()), (1, "Run".to_owned())])?;
    o.types.insert("State".to_owned(), state);
    let rec = build_struct(
        "Rec",
        None,
        &[
            (0x00, "name".to_owned(), parse_type("char *")?),
            (0x08, "id".to_owned(), parse_type("u32")?),
            (0x0c, "state".to_owned(), parse_type("State")?),
            (0x10, "pos".to_owned(), parse_type("Vec")?),
            (0x18, "tag".to_owned(), parse_type("char[8]")?),
            (0x20, "next".to_owned(), parse_type("Rec *")?),
        ],
        &o.types,
        8,
    )?;
    o.types.insert("Rec".to_owned(), rec);
    Ok(o)
}

/// The rows of a rendering with each run of spaces folded to one, so a
/// test reads a row without counting its column padding.
///
/// # Arguments
///
/// * `text` - The rendering.
fn folded(text: &str) -> Vec<String> {
    text.lines()
        .map(|l| l.split_whitespace().collect::<Vec<_>>().join(" "))
        .collect()
}

/// `Rec[2]` reads both records with their fields named, nested, enumerated
/// and quoted, and twice reads byte for byte alike.
#[test]
fn a_typed_read_names_every_field_of_every_record() {
    let p = table();
    let o = types().unwrap();
    let ty = parse_type("Rec[2]").unwrap();
    let text = typed_tsv(&p, None, &o, 0x403_000, &ty).unwrap();
    assert_eq!(
        typed_tsv(&p, None, &o, 0x403_000, &ty).unwrap(),
        text,
        "twice alike"
    );
    let rows = folded(&text);
    assert_eq!(
        rows[0], "# showing 14 of 14 rows: Rec[2] at 0x403000 in .rdata, 0x50 bytes",
        "{text}"
    );
    for want in [
        "0x403000 [0].name char * 0x403100 -> \"alpha\"",
        "0x403008 [0].id u32 0x1",
        "0x40300c [0].state State Run",
        "0x403010 [0].pos.x f32 1.5",
        "0x403014 [0].pos.y f32 -2.0",
        "0x403018 [0].tag char[8] \"ab\\x01\"",
        "0x403020 [0].next Rec * 0x403028 -> .rdata",
        "0x403028 [1].name char * 0x403106 -> \"beta\"",
        "0x403034 [1].state State 0x5 (no member)",
        "0x40303c [1].pos.y f32 0.25",
        "0x403040 [1].tag char[8] \"zzzzzzzz\"",
        "0x403048 [1].next Rec * 0x0",
    ] {
        assert!(rows.iter().any(|r| r == want), "{want} missing:\n{text}");
    }
}

/// The caps hold: rows past the row cap are counted, not printed; a type
/// running past the mapped bytes is read for the bytes there and says
/// where to read on; a type naming nothing is refused.
#[test]
fn a_typed_read_keeps_its_caps() {
    let p = table();
    let o = types().unwrap();
    let many = typed_tsv(&p, None, &o, 0x403_000, &parse_type("u8 *[100]").unwrap()).unwrap();
    assert!(
        many.starts_with("# showing 64 of 64 rows: u8 *[100] at 0x403000 in .rdata, 0x320 bytes; read 0x200 (where the mapped bytes end), read at 0x403200 for the rest\n"),
        "{many}"
    );
    let signed = typed_tsv(&p, None, &o, 0x403_000, &parse_type("i8[300]").unwrap()).unwrap();
    assert!(
        signed
            .starts_with("# showing 256 of 300 rows: i8[300] at 0x403000 in .rdata, 0x12c bytes\n"),
        "{signed}"
    );
    assert_eq!(signed.lines().count(), 257, "{signed}");
    let bytes = typed_tsv(&p, None, &o, 0x403_100, &parse_type("u8[6]").unwrap()).unwrap();
    assert!(
        folded(&bytes).contains(&"0x403100 - u8[6] 61 6c 70 68 61 00".to_owned()),
        "{bytes}"
    );
    let err = typed_tsv(&p, None, &o, 0x403_000, &parse_type("Missing").unwrap()).unwrap_err();
    assert!(err.contains("names nothing defined"), "{err}");
    let err = typed_tsv(&p, None, &o, 0x9000, &parse_type("Rec").unwrap()).unwrap_err();
    assert!(err.contains("not mapped"), "{err}");
}
