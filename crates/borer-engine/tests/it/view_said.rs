//! Who stated each name a view links: the overlay, the file, the engine's
//! findings, or nothing, read from the fact the name was spelled with.

#![expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]

use std::sync::Arc;

use borer_engine::analysis::decompile::decompile_named;
use borer_engine::analysis::decompile::view::{view, view_of};
use borer_engine::analysis::render::{Bytes, FunctionRow, disasm_view};
use borer_engine::analysis::{Analysis, EnumSource, NameSource, Overlay};
use borer_engine::headers::{ImportName, ImportOrigins, OrdinalName};
use borer_engine::program::{Arch, BinaryFormat, Program, Symbol, SymbolKind};
use borer_engine::view::{Kind, Ref, Said, View};

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
        "{named:?}
{}",
        listing.spell()
    );
    let unnamed = said_of(&listing, &Ref::Address(CALLER + 5));
    assert!(
        unnamed.contains(&(Kind::Label, Some(Said::Placeholder))),
        "{unnamed:?}
{}",
        listing.spell()
    );
}
