//! Who stated each name a view links: the overlay, the file, the engine's
//! findings, or nothing, read from the fact the name was spelled with.

#![expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]

use std::collections::BTreeMap;
use std::sync::Arc;

use borer_engine::analysis::decompile::decompile_named;
use borer_engine::analysis::decompile::view::{view, view_of};
use borer_engine::analysis::edit::{Edit, Force, commit, plan};
use borer_engine::analysis::render::{Bytes, FunctionRow, RowSource, disasm_view};
use borer_engine::analysis::utypes::{TypeExpr, UserField, UserStruct, UserType};
use borer_engine::analysis::{Analysis, EnumSource, NameSource, Overlay};
use borer_engine::dwarf::{Parameter, Subprogram};
use borer_engine::headers::{ImportName, ImportOrigins, OrdinalName};
use borer_engine::program::{Arch, BinaryFormat, Program, Symbol, SymbolKind};
use borer_engine::view::{Kind, Ref, Said, SaidCounts, View};

/// Where [`callers`] enters: the function that calls the four others.
const CALLER: u64 = 0x40_1000;

/// The callee a symbol names, `named_by_file`.
const SYMBOL: u64 = 0x40_1040;

/// The callee the overlay names, `load_settings`.
const USER: u64 = 0x40_1050;

/// The callee named for its shape, `release_ref`.
const HELPER: u64 = 0x40_1060;

/// The callee nothing names.
const UNNAMED: u64 = 0x40_1070;

/// A function nothing calls, named by a symbol.
const APART: u64 = 0x40_1080;

/// Builds an x64 image whose [`CALLER`] calls [`SYMBOL`], [`USER`],
/// [`HELPER`] and [`UNNAMED`] in turn, each returning a constant, beside
/// [`APART`].
///
/// # Returns
///
/// The image, its analysis with [`HELPER`] named for a helper's shape, and
/// an overlay naming [`USER`].
fn callers() -> (Program, Analysis, Overlay) {
    let mut code = vec![0xcc; 0x90];
    let caller: &[u8] = &[
        0x48, 0x83, 0xec, 0x28, // ASM: sub rsp,0x28
        0xe8, 0x37, 0, 0, 0, // ASM: call SYMBOL
        0xe8, 0x42, 0, 0, 0, // ASM: call USER
        0xe8, 0x4d, 0, 0, 0, // ASM: call HELPER
        0xe8, 0x58, 0, 0, 0, // ASM: call UNNAMED
        0x48, 0x83, 0xc4, 0x28, 0xc3, // ASM: add rsp,0x28; ret
    ];
    code[..caller.len()].copy_from_slice(caller);
    for (n, at) in (1u8..).zip([SYMBOL, USER, HELPER, UNNAMED, APART]) {
        let at = usize::try_from(at - CALLER).unwrap_or(0);
        code[at..at + 6].copy_from_slice(&[0xb8, n, 0, 0, 0, 0xc3]); // ASM: mov eax,n; ret
    }
    let mut p = crate::raw::image(Arch::X86_64, &code, &[]);
    p.symbols = [("named_by_file", SYMBOL), ("apart", APART)]
        .map(|(name, addr)| Symbol {
            name: name.to_owned(),
            addr,
            kind: SymbolKind::Export,
        })
        .to_vec();
    let mut a = Analysis::compute(&p);
    if let Some(f) = a.functions.iter_mut().find(|f| f.entry == HELPER) {
        f.name = Some("release_ref".to_owned());
        f.name_source = NameSource::Helper;
    }
    let mut o = Overlay {
        enum_source: EnumSource::Binary,
        ..Overlay::default()
    };
    o.names.insert(USER, "load_settings".to_owned());
    (p, a, o)
}

/// Returns the kind of each token of a view linked to `r`, in order, with
/// who it says stated the name.
///
/// # Arguments
///
/// * `v` - The view.
/// * `r` - The referent.
fn said_of(v: &View, r: &Ref) -> Vec<(Kind, Option<Said>)> {
    (0..v.lines())
        .flat_map(|i| {
            v.tokens_said(i)
                .filter_map(|(_, kind, link)| {
                    link.filter(|(x, _)| *x == r).map(|(_, said)| (kind, said))
                })
                .collect::<Vec<_>>()
        })
        .collect()
}

/// Each callee's name says who stated it, as the function table's row of
/// it does.
///
/// A symbol's is the file's, the overlay's the user's, a helper's
/// the engine's finding, and an unnamed one's, the caller's own `sub_`
/// among them, a placeholder; the decompile and the listing agree.
#[test]
fn each_callee_says_who_named_it_as_its_function_row_does() {
    let (p, a, o) = callers();
    let text = decompile_named(&p, &a, &o, CALLER).expect("a text");
    let v = view(&p, &a, &o, CALLER).expect("a view");
    let listing = disasm_view(&p, &a, &o, CALLER, 100, Bytes::Hidden).expect("a listing");
    for (entry, want) in [
        (SYMBOL, Said::Stated),
        (USER, Said::User),
        (HELPER, Said::Inferred),
        (UNNAMED, Said::Placeholder),
        (CALLER, Said::Placeholder),
    ] {
        let f = a.function(entry).expect("a function");
        assert_eq!(
            Said::from(FunctionRow::of(&a, &o, f).src),
            want,
            "{entry:#x}"
        );
        let views = if entry == CALLER {
            vec![("decompile", &*v)]
        } else {
            vec![("decompile", &*v), ("listing", &listing)]
        };
        for (what, shown) in views {
            let said = said_of(shown, &Ref::Function(entry));
            assert!(
                !said.is_empty() && said.iter().all(|&(_, s)| s == Some(want)),
                "{what} {entry:#x}: {said:?}\n{text}"
            );
        }
    }
}

/// Every source of a function's name maps to who stated it: the overlay's
/// to the user, a symbol's to the file, no name to a placeholder, and
/// every finding of the engine's to it.
#[test]
fn every_name_source_says_who_stated_it() {
    assert_eq!(Said::from(RowSource::User), Said::User);
    assert_eq!(
        Said::from(RowSource::Found(NameSource::None)),
        Said::Placeholder
    );
    assert_eq!(
        Said::from(RowSource::Found(NameSource::Symbol)),
        Said::Stated
    );
    for found in [
        NameSource::Helper,
        NameSource::Signature,
        NameSource::Handler,
        NameSource::Slot,
        NameSource::Qt,
        NameSource::Funclet,
        NameSource::Pack,
        NameSource::Library,
        NameSource::ObjC,
        NameSource::Constants,
    ] {
        assert_eq!(
            Said::from(RowSource::Found(found)),
            Said::Inferred,
            "{found:?}"
        );
    }
}

/// Renaming a function the view does not name keeps the view, and naming
/// a callee builds it again with the callee's tokens saying the user named
/// it.
#[test]
fn a_rename_the_view_does_not_name_keeps_it_and_a_callees_says_user() {
    let (p, a, before) = callers();
    let built = |o: &Overlay| {
        let text = decompile_named(&p, &a, o, CALLER).expect("a text");
        let make = || view_of(&p, &a, o, CALLER, &text);
        a.derived
            .get_or_build_item("view_said_test", o.fingerprint(), CALLER, make, |_| 0)
    };
    let was = built(&before);
    let mut far = before.clone();
    far.names.insert(APART, "renamed_apart".to_owned());
    a.derived.moved(&a, &before, &far);
    assert!(Arc::ptr_eq(&was, &built(&far)), "the view was built again");
    let mut near = far.clone();
    near.names.insert(UNNAMED, "named_now".to_owned());
    a.derived.moved(&a, &far, &near);
    let now = built(&near);
    assert!(!Arc::ptr_eq(&was, &now), "the view was kept");
    let v = now.as_ref().as_ref().expect("a view");
    let said = said_of(v, &Ref::Function(UNNAMED));
    assert!(
        !said.is_empty() && said.iter().all(|&(_, s)| s == Some(Said::User)),
        "{said:?}\n{}",
        v.spell()
    );
}

/// An import says who named it.
///
/// The `<dll>_ord<n>` or `(unnamed)` the
/// loader makes up is a placeholder, a table's export name for an ordinal
/// the engine's finding, an import the file names stays the file's, and
/// one listed at two slots whose names came apart, or at a slot two import
/// symbols share, says nothing, in the decompile and the listing alike;
/// a name spelled whole with a made-up module, as both views spell
/// `(unnamed)!Halt`, is a placeholder.
#[test]
fn an_ordinal_import_says_whether_a_table_or_the_loader_named_it() {
    let code: &[u8] = &[
        0x48, 0x83, 0xec, 0x28, // ASM: sub rsp,0x28
        0xff, 0x15, 0xf6, 0x0f, 0, 0, // ASM: call [rip+0xff6]
        0xff, 0x15, 0xf8, 0x0f, 0, 0, // ASM: call [rip+0xff8]
        0xff, 0x15, 0xfa, 0x0f, 0, 0, // ASM: call [rip+0xffa]
        0xff, 0x15, 0xfc, 0x0f, 0, 0, // ASM: call [rip+0xffc]
        0xff, 0x15, 0xfe, 0x0f, 0, 0, // ASM: call [rip+0xffe]
        0xff, 0x15, 0x00, 0x10, 0, 0, // ASM: call [rip+0x1000]
        0xff, 0x15, 0x02, 0x10, 0, 0, // ASM: call [rip+0x1002]
        0x48, 0x83, 0xc4, 0x28, 0xc3, // ASM: add rsp,0x28; ret
    ];
    let slots = [
        0x40_2000, 0x40_2008, 0x40_2010, 0x40_2018, 0x40_2020, 0x40_2028, 0x40_2030,
    ];
    let at = [0, 1, 2, 3, 4, 5, 5, 6].map(|k| slots[k]);
    let mut p = crate::raw::image(Arch::X86_64, code, &[]);
    p.format = BinaryFormat::Pe;
    p.symbols = [
        "certcli.dll!certcli_ord60000",
        "WLDAP32.dll!ldap_initW",
        "KERNEL32.dll!Sleep",
        "KERNEL32.dll!(unnamed)",
        "WLDAP32.dll!ldap_initW",
        "KERNEL32.dll!Beep",
        "KERNEL32.dll!(unnamed)",
        "(unnamed)!Halt",
    ]
    .into_iter()
    .zip(at)
    .map(|(name, addr)| Symbol {
        name: name.to_owned(),
        addr,
        kind: SymbolKind::Import,
    })
    .collect();
    let made = Some(OrdinalName::Made);
    let named = |symbol: usize, ordinal: Option<u16>, origin, module| ImportName {
        slot: at[symbol],
        symbol,
        ordinal,
        origin,
        module,
    };
    p.headers.import_names = ImportOrigins::new(vec![
        named(6, None, made, None),
        named(0, Some(60000), made, None),
        named(3, None, made, None),
        named(4, Some(145), Some(OrdinalName::Listed), None),
        named(7, None, None, made),
    ]);
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let v = view(&p, &a, &o, CALLER).expect("a view");
    let listing = disasm_view(&p, &a, &o, CALLER, 100, Bytes::Hidden).expect("a listing");
    for (slot, want, views) in [
        (slots[0], Some(Said::Placeholder), 2),
        (slots[1], None, 2),
        (slots[2], Some(Said::Stated), 2),
        (slots[3], Some(Said::Placeholder), 1),
        (slots[5], None, 2),
        (slots[6], Some(Said::Placeholder), 2),
    ] {
        for (what, shown) in [("listing", &listing), ("decompile", &*v)]
            .into_iter()
            .take(views)
        {
            let said = said_of(shown, &Ref::Import(slot));
            assert!(
                !said.is_empty() && said.iter().all(|&(_, s)| s == want),
                "{what} {slot:#x}: {said:?}\n{}",
                shown.spell()
            );
        }
    }
}

/// A block start the overlay names is no placeholder, though the listing
/// spells its label from its address; a block start nothing names is one.
#[test]
fn a_named_block_start_is_no_placeholder() {
    let code: &[u8] = &[0x85, 0xc9, 0x74, 0x01, 0x90, 0xc3]; // ASM: test ecx,ecx; je +1; nop; ret
    let p = crate::raw::image(Arch::X86_64, code, &[]);
    let a = Analysis::compute(&p);
    let mut o = Overlay::default();
    o.names.insert(CALLER + 4, "fallen_through".to_owned());
    let listing = disasm_view(&p, &a, &o, CALLER, 100, Bytes::Hidden).expect("a listing");
    let named = said_of(&listing, &Ref::Address(CALLER + 4));
    assert!(
        !named.is_empty() && named.iter().all(|&(_, s)| s != Some(Said::Placeholder)),
        "{named:?}\n{}",
        listing.spell()
    );
    let unnamed = said_of(&listing, &Ref::Address(CALLER + 5));
    assert!(
        unnamed.contains(&(Kind::Label, Some(Said::Placeholder))),
        "{unnamed:?}\n{}",
        listing.spell()
    );
}

/// Returns who each linked token of a view spelling `word` says stated
/// its name, in order.
///
/// # Arguments
///
/// * `v` - The view.
/// * `word` - The spelling.
fn said_spelled(v: &View, word: &str) -> Vec<Option<Said>> {
    (0..v.lines())
        .flat_map(|i| {
            let line = v.line(i).unwrap_or_default();
            v.tokens_said(i)
                .filter_map(|(span, _, link)| {
                    let (_, said) = link?;
                    (line.get(span) == Some(word)).then_some(said)
                })
                .collect::<Vec<_>>()
        })
        .collect()
}

/// Returns the first variable of a view spelled with `prefix`.
///
/// # Arguments
///
/// * `v` - The view.
/// * `prefix` - How its name opens.
fn variable_named(v: &View, prefix: &str) -> Option<String> {
    (0..v.lines()).find_map(|i| {
        let line = v.line(i)?;
        v.tokens(i).find_map(|(span, kind, _)| {
            let word = line.get(span)?;
            (kind == Kind::Variable && word.starts_with(prefix)).then(|| word.to_owned())
        })
    })
}

/// Tells whether every linked token spelling `word` says `want`, and one
/// does.
///
/// # Arguments
///
/// * `v` - The view.
/// * `word` - The spelling.
/// * `want` - Who each should say stated it.
fn all_say(v: &View, word: &str, want: Option<Said>) -> bool {
    let said = said_spelled(v, word);
    !said.is_empty() && said.iter().all(|&s| s == want)
}

/// A variable says who named it as the edit path reads it: an unnamed
/// local or parameter is a placeholder, a local the overlay names the
/// user's, and a parameter a debug record names the file's.
///
/// The image is [`crate::view::filling`]'s.
#[test]
fn a_variable_says_who_named_it() {
    use crate::view::{TEXT, filling};
    let p = filling(false);
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let plain = view(&p, &a, &o, TEXT).expect("a view");
    let local = variable_named(&plain, "local_").expect("a local");
    for word in [local.as_str(), "a1"] {
        assert!(
            all_say(&plain, word, Some(Said::Placeholder)),
            "{word}: {:?}\n{}",
            said_spelled(&plain, word),
            plain.spell()
        );
    }
    let edits = [Edit::Var {
        entry: TEXT,
        var: local,
        field: None,
        name: Some("packet".to_owned()),
        ty: None,
    }];
    let mut named = o.clone();
    let made = plan(&p, &a, &named, &edits, Force::Refuse).expect("planned");
    commit(&p, &a, &mut named, &made).expect("committed");
    let v = view(&p, &a, &named, TEXT).expect("a view");
    assert!(all_say(&v, "packet", Some(Said::User)), "{}", v.spell());
    let mut debugged = filling(false);
    debugged.debug_functions.push(Subprogram {
        low_pc: TEXT,
        name: "filler".to_owned(),
        parameters: vec![Parameter {
            name: "inbound".to_owned(),
            type_name: None,
        }],
        return_type: None,
        locals: BTreeMap::new(),
    });
    let a = Analysis::compute(&debugged);
    let v = view(&debugged, &a, &o, TEXT).expect("a view");
    assert!(all_say(&v, "inbound", Some(Said::Stated)), "{}", v.spell());
}

/// A field or a type says who named it.
///
/// The overlay's struct is the
/// user's, the debug information's the file's, a `field_0x<hex>` at its own
/// offset a placeholder, and a struct only the text defines says nothing.
#[test]
fn a_field_and_a_type_say_who_named_them() {
    let field = |name: &str, ty: TypeExpr| UserField {
        name: name.to_owned(),
        ty,
    };
    let strukt = |off: u64, f: UserField| {
        UserType::Struct(UserStruct {
            size: 0x10,
            fields: BTreeMap::from([(off, f)]),
        })
    };
    let mut p = crate::raw::image(Arch::X86_64, &[0xc3], &[]); // ASM: ret
    p.debug_types.insert(
        "Record".to_owned(),
        strukt(8, field("level", TypeExpr::U64)),
    );
    let a = Analysis::compute(&p);
    let mut o = Overlay::default();
    o.types
        .insert("Player".to_owned(), strukt(4, field("hp", TypeExpr::U32)));
    let text = concat!(
        "// signature: uint64_t sub_401000(struct Player *a1, struct Record *a2, struct Pair *a3)
",
        "struct Record { uint64_t pad; uint64_t level; };
",
        "struct Pair { uint64_t head; uint64_t tail; };
",
        "return a1->hp + a2->level + a3->head + a3->field_0x8;
",
    );
    let v = view_of(&p, &a, &o, CALLER, text).expect("a view");
    for (word, want) in [
        ("hp", Some(Said::User)),
        ("Player", Some(Said::User)),
        ("level", Some(Said::Stated)),
        ("Record", Some(Said::Stated)),
        ("field_0x8", Some(Said::Placeholder)),
        ("head", None),
        ("Pair", None),
    ] {
        assert!(
            all_say(&v, word, want),
            "{word}: {:?}\n{}",
            said_spelled(&v, word),
            v.spell()
        );
    }
}

/// A view of a text that declares its own `Foo` reads no user type of that
/// name, so it says nothing of who named `Foo` and stating a user `Foo`
/// keeps it.
#[test]
fn a_type_the_text_declares_reads_no_user_type() {
    let p = crate::raw::image(Arch::X86_64, &[0xc3], &[]); // ASM: ret
    let a = Analysis::compute(&p);
    let mut before = Overlay::default();
    before
        .comments
        .insert(CALLER + 0x100, "elsewhere".to_owned());
    let text = concat!(
        "// signature: uint64_t sub_401000(struct Foo *a1)\n",
        "struct Foo { uint64_t x; };\n",
        "\n",
        "return 0;\n",
    );
    let built = |o: &Overlay| {
        let make = || view_of(&p, &a, o, CALLER, text);
        a.derived.get_or_build_item(
            "view_declared_type_test",
            o.fingerprint(),
            CALLER,
            make,
            |_| 0,
        )
    };
    let was = built(&before);
    let shown = was.as_ref().as_ref().expect("a view");
    assert!(all_say(shown, "Foo", None), "{}", shown.spell());
    let mut after = before.clone();
    after.types.insert(
        "Foo".to_owned(),
        UserType::Struct(UserStruct {
            size: 8,
            fields: BTreeMap::new(),
        }),
    );
    a.derived.moved(&a, &before, &after);
    assert!(
        Arc::ptr_eq(&was, &built(&after)),
        "the view was built again"
    );
}

/// Returns the kind and the link of each token of a view spelling `word`,
/// in order.
///
/// # Arguments
///
/// * `v` - The view.
/// * `word` - The spelling.
fn kinds_spelled(v: &View, word: &str) -> Vec<(Kind, Option<Ref>)> {
    (0..v.lines())
        .flat_map(|i| {
            let line = v.line(i).unwrap_or_default();
            v.tokens(i)
                .filter(|(span, ..)| line.get(span.clone()) == Some(word))
                .map(|(_, kind, link)| (kind, link.cloned()))
                .collect::<Vec<_>>()
        })
        .collect()
}

/// Returns [`callers`]'s overlay with comments at [`CALLER`]'s instructions.
///
/// They are the first call's, the second's an open question, the third's and fourth's
/// alike, the `add`'s spelled as an answer's trailer, and the `ret`'s an
/// open question behind a blank.
fn commented() -> Overlay {
    let (.., mut o) = callers();
    for (at, c) in [
        (CALLER + 4, "checks the license"),
        (CALLER + 9, "? why twice"),
        (CALLER + 0xe, "same text"),
        (CALLER + 0x13, "same text"),
        (CALLER + 0x18, "next: borer://solve/0x401004"),
        (CALLER + 0x1c, " ? why"),
    ] {
        o.comments.insert(at, c.to_owned());
    }
    o
}

/// An overlay comment at an instruction of the function is a note linked
/// to its address.
///
/// One opening with `?` (blanks before it ignored) a
/// question, a text two instructions hold a note linked to neither, and a
/// header line, an answer's trailer among them, or a comment the overlay
/// does not hold stays a comment; the listing marks its comments alike.
#[test]
fn an_overlay_comment_is_a_note_and_one_opening_with_a_question_mark_a_question() {
    let (p, a, _) = callers();
    let o = commented();
    let note = |at: u64| (Kind::Note, Some(Ref::Comment(at)));
    let question = |at: u64| (Kind::Question, Some(Ref::Comment(at)));
    let answered = view(&p, &a, &o, CALLER).expect("a view");
    assert_eq!(
        kinds_spelled(&answered, "// checks the license"),
        [note(CALLER + 4)],
        "{}",
        answered.spell()
    );
    let text = concat!(
        "// sub_401000 @ 0x401000\n",
        "// checks the license\n",
        "// next: borer://solve/0x401004\n",
        "// signature: uint64_t sub_401000(void)\n",
        "\n",
        "    // checks the license\n",
        "// ? why twice\n",
        "// same text\n",
        "// not held\n",
        "//  ? why\n",
        "return 0;\n",
    );
    let v = view_of(&p, &a, &o, CALLER, text).expect("a view");
    assert_eq!(v.spell(), text);
    assert_eq!(
        kinds_spelled(&v, "// checks the license"),
        [(Kind::Comment, None), note(CALLER + 4)]
    );
    assert_eq!(
        kinds_spelled(&v, "// next: borer://solve/0x401004"),
        [(Kind::Comment, None)]
    );
    assert_eq!(kinds_spelled(&v, "// ? why twice"), [question(CALLER + 9)]);
    assert_eq!(kinds_spelled(&v, "//  ? why"), [question(CALLER + 0x1c)]);
    assert_eq!(kinds_spelled(&v, "// same text"), [(Kind::Note, None)]);
    assert_eq!(kinds_spelled(&v, "// not held"), [(Kind::Comment, None)]);
    let listing = disasm_view(&p, &a, &o, CALLER, 100, Bytes::Hidden).expect("a listing");
    assert_eq!(
        kinds_spelled(&listing, "// ? why twice"),
        [question(CALLER + 9)]
    );
    assert_eq!(
        kinds_spelled(&listing, "//  ? why"),
        [question(CALLER + 0x1c)]
    );
    assert_eq!(
        kinds_spelled(&listing, "// same text"),
        [note(CALLER + 0xe), note(CALLER + 0x13)]
    );
}

/// A comment at another function's instruction keeps a view that shows
/// notes: the view reads the comments of its own instructions alone.
#[test]
fn a_comment_elsewhere_keeps_a_view_with_notes() {
    let (p, a, _) = callers();
    let before = commented();
    let built = |o: &Overlay| {
        let text = decompile_named(&p, &a, o, CALLER).expect("a text");
        let make = || view_of(&p, &a, o, CALLER, &text);
        a.derived
            .get_or_build_item("view_notes_test", o.fingerprint(), CALLER, make, |_| 0)
    };
    let was = built(&before);
    let shown = was.as_ref().as_ref().expect("a view");
    assert_eq!(
        kinds_spelled(shown, "// checks the license"),
        [(Kind::Note, Some(Ref::Comment(CALLER + 4)))],
        "{}",
        shown.spell()
    );
    let mut after = before.clone();
    after.comments.insert(APART, "elsewhere".to_owned());
    a.derived.moved(&a, &before, &after);
    assert!(
        Arc::ptr_eq(&was, &built(&after)),
        "the view was built again"
    );
}

/// A view counts each referent once by who stated its name, however many
/// tokens spell it.
///
/// Naming the unnamed callee moves one from the
/// placeholders to the user's, and a note, which is no name, counts
/// nowhere.
#[test]
fn said_counts_count_each_referent_once() {
    let (p, a, o) = callers();
    let before = view(&p, &a, &o, CALLER).expect("a view").said_counts();
    assert_eq!(
        (before.user, before.stated, before.inferred),
        (1, 1, 1),
        "{before:?}"
    );
    let mut named = o;
    named.names.insert(UNNAMED, "named_now".to_owned());
    named.comments.insert(CALLER + 4, "a note".to_owned());
    let after = view(&p, &a, &named, CALLER).expect("a view").said_counts();
    assert_eq!(
        SaidCounts {
            user: before.user + 1,
            placeholder: before.placeholder - 1,
            ..before
        },
        after
    );
}
