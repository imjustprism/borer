//! What a rename carries of the decompile views and texts already built,
//! and what it builds again ([`borer_engine::analysis::Derived::moved`]).

use std::sync::Arc;

use crate::view::{SLOT, TEXT, exported_four, image, symbol, tokens};
use borer_engine::analysis::decompile::view::view;
use borer_engine::analysis::decompile::{Detail, Pass, Passes, answer};
use borer_engine::analysis::{Analysis, EnumSource, Overlay};
use borer_engine::program::SymbolKind;
use borer_engine::view::{Kind, Ref, View};

/// Returns the answered views ([`view`]) of `fa` and `fc` across a rename.
///
/// The image is [`exported_four`]'s, read under the binary's name tables;
/// the memo is carried over the rename
/// ([`borer_engine::analysis::Derived::moved`]).
///
/// # Arguments
///
/// * `at` - The function renamed.
/// * `name` - Its new name.
///
/// # Returns
///
/// The views of `fa` and `fc`, each before the rename, after it, and as a
/// fresh analysis builds it under the new names.
#[expect(clippy::expect_used, reason = "every function of the image decompiles")]
fn renamed_views(at: u64, name: &str) -> [(Arc<View>, Arc<View>, Arc<View>); 2] {
    let p = exported_four();
    let a = Analysis::compute(&p);
    let before = Overlay {
        enum_source: EnumSource::Binary,
        ..Overlay::default()
    };
    let ends = [TEXT, TEXT + 0x80];
    let mut was = ends
        .map(|e| view(&p, &a, &before, e).expect("a view"))
        .into_iter();
    let mut after = before.clone();
    after.names.insert(at, name.to_owned());
    a.derived.moved(&a, &before, &after);
    let fresh = Analysis::compute(&p);
    ends.map(|e| {
        (
            was.next().expect("a view per entry"),
            view(&p, &a, &after, e).expect("a view"),
            view(&p, &fresh, &after, e).expect("a fresh view"),
        )
    })
}

/// A rename keeps the answered view of a function that does not name the
/// renamed one: the same result, not built again.
///
/// The answer's text looks its names up in the program's name index,
/// which reads every function's name; the answer notes only the names it
/// looked up, so renaming `fb`, which `fa` calls, keeps `fc`'s view.
#[test]
fn a_rename_keeps_each_answered_view_that_does_not_name_it() {
    let [_, (apart, kept, fresh)] = renamed_views(TEXT + 0x40, "renamed_b");
    assert!(Arc::ptr_eq(&apart, &kept), "the apart view was built again");
    assert_eq!(tokens(&kept), tokens(&fresh));
}

/// A rename builds the answered view of the renamed function's caller again.
///
/// The new name links to the callee and the view reads as a fresh
/// analysis reads it; so does a rename of another function to the callee's
/// name, which makes that name name two functions.
#[test]
fn a_rename_builds_its_callers_answered_view_again() {
    let b = TEXT + 0x40;
    let [(caller, rebuilt, fresh), _] = renamed_views(b, "renamed_b");
    assert!(
        !Arc::ptr_eq(&caller, &rebuilt),
        "the caller's view was kept"
    );
    assert!(
        tokens(&rebuilt)
            .iter()
            .any(|(_, w, kind, link)| w == "renamed_b"
                && *kind == Kind::Function
                && *link == Some(Ref::Function(b))),
        "{}",
        rebuilt.spell()
    );
    assert_eq!(tokens(&rebuilt), tokens(&fresh));
    let [(_, now, fresh), _] = renamed_views(TEXT + 0x80, "fb");
    assert_eq!(tokens(&now), tokens(&fresh), "{}", now.spell());
}

/// A rename to a name a text calls builds that text again.
///
/// `fa` calls the import `fill_record` through its slot and never reaches
/// `fc`; once `fc` goes by `fill_record` the answer declares it, as a
/// fresh analysis does. The overlay's own tables are in force, which leave
/// the body unnoted, and it names an address the text does not reach, so the
/// memo carries what the rename does not touch.
///
/// `fa` at [`TEXT`]: `sub rsp,0x28; call [SLOT]; add rsp,0x28; ret`; `fc`
/// at `TEXT + 0x40`: `mov eax,3; ret`.
#[test]
fn a_rename_to_a_name_a_text_calls_builds_that_text_again() {
    let c = TEXT + 0x40;
    let code: [(u64, &[u8]); 4] = [
        (TEXT, &[0x48, 0x83, 0xec, 0x28]),              // ASM: sub rsp,0x28
        (TEXT + 0x04, &[0xff, 0x15, 0xf6, 0x0f, 0, 0]), // ASM: call [rip+0xff6]
        (TEXT + 0x0a, &[0x48, 0x83, 0xc4, 0x28, 0xc3]), // ASM: add rsp,0x28; ret
        (c, &[0xb8, 3, 0, 0, 0, 0xc3]),                 // ASM: mov eax,3; ret
    ];
    let symbols = vec![
        symbol("TESTLIB.dll!fill_record", SLOT, SymbolKind::Import),
        symbol("fa", TEXT, SymbolKind::Export),
        symbol("fc", c, SymbolKind::Export),
    ];
    let p = image(&code, symbols);
    let a = Analysis::compute(&p);
    let mut before = Overlay::default();
    before.names.insert(SLOT + 0x800, "unread".to_owned());
    let was = answer(&p, &a, &before, TEXT, Detail::Full).expect("an answer");
    let mut after = before.clone();
    after.names.insert(c, "fill_record".to_owned());
    a.derived.moved(&a, &before, &after);
    let now = answer(&p, &a, &after, TEXT, Detail::Full).expect("an answer");
    let fresh = answer(&p, &Analysis::compute(&p), &after, TEXT, Detail::Full);
    assert_ne!(was, now);
    assert_eq!(Some(now), fresh);
}

/// A rename that makes a callee's name name two functions builds the
/// caller's text again, without the unit's declarations to note it.
///
/// `fa` passes its parameter to `g`, which hands its own to `strlen`, so
/// `fa`'s parameter reads `g`'s `char *`. Once `fh` goes by `g` too, the
/// name no longer says which function `fa` calls, and its parameter stays
/// untyped, as a fresh analysis reads it. The unit closure is left out and
/// the overlay's own tables are in force, so only the callee lookup notes
/// the name.
///
/// `fa` at [`TEXT`]: `sub rsp,0x28; mov rax,rcx; mov rcx,rax; call g; add
/// rsp,0x28; ret`; `g` at `TEXT + 0x40`: `sub rsp,0x28; call [SLOT]; add
/// rsp,0x28; ret`; `fh` at `TEXT + 0x80`: `mov eax,3; ret`.
#[test]
fn a_rename_that_shares_a_callees_name_builds_its_caller_again() {
    let (g, h) = (TEXT + 0x40, TEXT + 0x80);
    let code: [(u64, &[u8]); 9] = [
        (TEXT, &[0x48, 0x83, 0xec, 0x28]),              // ASM: sub rsp,0x28
        (TEXT + 0x04, &[0x48, 0x89, 0xc8]),             // ASM: mov rax,rcx
        (TEXT + 0x07, &[0x48, 0x89, 0xc1]),             // ASM: mov rcx,rax
        (TEXT + 0x0a, &[0xe8, 0x31, 0, 0, 0]),          // ASM: call g
        (TEXT + 0x0f, &[0x48, 0x83, 0xc4, 0x28, 0xc3]), // ASM: add rsp,0x28; ret
        (g, &[0x48, 0x83, 0xec, 0x28]),                 // ASM: sub rsp,0x28
        (g + 0x04, &[0xff, 0x15, 0xb6, 0x0f, 0, 0]),    // ASM: call [rip+0xfb6]
        (g + 0x0a, &[0x48, 0x83, 0xc4, 0x28, 0xc3]),    // ASM: add rsp,0x28; ret
        (h, &[0xb8, 3, 0, 0, 0, 0xc3]),                 // ASM: mov eax,3; ret
    ];
    let symbols = vec![
        symbol("msvcrt.dll!strlen", SLOT, SymbolKind::Import),
        symbol("fa", TEXT, SymbolKind::Export),
        symbol("g", g, SymbolKind::Export),
        symbol("fh", h, SymbolKind::Export),
    ];
    let p = image(&code, symbols);
    let a = Analysis::compute(&p);
    let before = Overlay {
        passes: Passes::NONE.without(Pass::UnitClosure),
        ..Overlay::default()
    };
    let was = answer(&p, &a, &before, TEXT, Detail::Full).expect("an answer");
    assert!(was.contains("char *a1"), "{was}");
    let mut after = before.clone();
    after.names.insert(h, "g".to_owned());
    a.derived.moved(&a, &before, &after);
    let now = answer(&p, &a, &after, TEXT, Detail::Full).expect("an answer");
    let fresh = answer(&p, &Analysis::compute(&p), &after, TEXT, Detail::Full);
    assert!(!now.contains("char *a1"), "{now}");
    assert_eq!(Some(now), fresh);
}
