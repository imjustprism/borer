//! A decompile read as lines of typed tokens: every byte of the answer in
//! a token, and a name linked only to the one thing that spells it, where
//! the code bears the link out.

#![expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]

use std::path::PathBuf;
use std::sync::Arc;

use crate::machogen::{self, CODE, Fix, PIE, R, RW, RX, Sect, Seg, Starts, X86_64};
use borer_engine::analysis::decompile::view::{view, view_of};
use borer_engine::analysis::decompile::{Detail, answer, decompile_named};
use borer_engine::analysis::{Analysis, EnumSource, Overlay};
use borer_engine::program::{Arch, BinaryFormat, Program, Section, Symbol, SymbolKind};
use borer_engine::view::{Kind, Ref, Unlinked, View};

/// Where [`image`] maps its code, entered at its start.
const TEXT: u64 = 0x1_4000_1000;

/// The read-only page of [`image`], where an import's slot sits.
const SLOT: u64 = 0x1_4000_2000;

/// The writable page of [`image`], where a global sits.
const GLOBAL: u64 = 0x1_4000_3000;

/// Builds a PE-shaped x64 image: each piece of code at its address in a
/// page at [`TEXT`], a read-only page at [`SLOT`] and a writable one at
/// [`GLOBAL`].
///
/// # Arguments
///
/// * `code` - The pieces of code, each at its address.
/// * `symbols` - The image's symbols.
#[expect(
    clippy::expect_used,
    reason = "fixture code offsets sit inside the text page"
)]
fn image(code: &[(u64, &[u8])], symbols: Vec<Symbol>) -> Program {
    let mut bytes = vec![0u8; 0x3000];
    bytes[..0x1000].fill(0xcc);
    for &(at, piece) in code {
        let at = usize::try_from(at - TEXT).expect("in the page");
        bytes[at..at + piece.len()].copy_from_slice(piece);
    }
    let pages = [
        (".text", TEXT, false, true),
        (".rdata", SLOT, false, false),
        (".data", GLOBAL, true, false),
    ];
    let sections = pages
        .into_iter()
        .map(|(name, va, writable, executable)| {
            Section::mapped(name, va, va - TEXT, 0x1000, writable, executable)
        })
        .collect();
    let mut p = Program::raw(bytes, Arch::X86_64, 0x1_4000_0000, Some(TEXT), sections);
    p.format = BinaryFormat::Pe;
    p.symbols = symbols;
    p
}

/// Returns a symbol of [`image`].
///
/// # Arguments
///
/// * `name` - Its name.
/// * `addr` - Its address.
/// * `kind` - What it is.
fn symbol(name: &str, addr: u64, kind: SymbolKind) -> Symbol {
    Symbol {
        name: name.to_owned(),
        addr,
        kind,
    }
}

/// Returns every token of a view: its line, its text, its kind and its
/// link.
///
/// # Arguments
///
/// * `v` - The view.
fn tokens(v: &View) -> Vec<(usize, String, Kind, Option<Ref>)> {
    (0..v.lines())
        .flat_map(|i| {
            let line = v.line(i).unwrap_or_default();
            v.tokens(i)
                .map(move |(span, kind, link)| (i, line[span].to_owned(), kind, link.cloned()))
        })
        .collect()
}

/// Returns the kind and the link of each token of a view that spells
/// `word`, in order.
///
/// # Arguments
///
/// * `v` - The view.
/// * `word` - The spelling.
fn spelled(v: &View, word: &str) -> Vec<(Kind, Option<Ref>)> {
    tokens(v)
        .into_iter()
        .filter(|(_, w, ..)| w == word)
        .map(|(.., kind, link)| (kind, link))
        .collect()
}

/// Where [`filling`] puts the stub that jumps through [`SLOT`].
const STUB: u64 = TEXT + 0x60;

/// Builds an image whose `TEXT` stores its parameter in [`GLOBAL`], calls
/// `TESTLIB.dll!fill_record` at [`SLOT`] on a local, and calls `H` with it.
///
/// `TEXT`: `sub rsp,0x38; mov [GLOBAL],rcx; lea rcx,[rsp+0x28]; call
/// [SLOT]; mov rcx,[rsp+0x28]; call H; add rsp,0x38; ret`; `H` at `TEXT +
/// 0x40`: `lea eax,[rcx+1]; ret`.
///
/// # Arguments
///
/// * `stub` - Whether `TEXT` calls the import through a stub at [`STUB`],
///   `jmp [SLOT]` (`call STUB; nop` in place of `call [SLOT]`).
fn filling(stub: bool) -> Program {
    let call: &[u8] = if stub {
        &[0xe8, 0x4b, 0x00, 0x00, 0x00, 0x90] // ASM: call STUB; nop
    } else {
        &[0xff, 0x15, 0xea, 0x0f, 0x00, 0x00] // ASM: call [rip+0xfea]
    };
    let jump: &[u8] = if stub {
        &[0xff, 0x25, 0x9a, 0x0f, 0x00, 0x00] // ASM: jmp [rip+0xf9a]
    } else {
        &[]
    };
    let code: [(u64, &[u8]); 10] = [
        (TEXT, &[0x48, 0x83, 0xec, 0x38]), // ASM: sub rsp,0x38
        (TEXT + 0x04, &[0x48, 0x89, 0x0d, 0xf5, 0x1f, 0x00, 0x00]), // ASM: mov [rip+0x1ff5],rcx
        (TEXT + 0x0b, &[0x48, 0x8d, 0x4c, 0x24, 0x28]), // ASM: lea rcx,[rsp+0x28]
        (TEXT + 0x10, call),
        (TEXT + 0x16, &[0x48, 0x8b, 0x4c, 0x24, 0x28]), // ASM: mov rcx,[rsp+0x28]
        (TEXT + 0x1b, &[0xe8, 0x20, 0x00, 0x00, 0x00]), // ASM: call H
        (TEXT + 0x20, &[0x48, 0x83, 0xc4, 0x38]),       // ASM: add rsp,0x38
        (TEXT + 0x24, &[0xc3]),                         // ASM: ret
        (TEXT + 0x40, &[0x8d, 0x41, 0x01, 0xc3]),       // ASM: lea eax,[rcx+1]; ret
        (STUB, jump),
    ];
    let import = symbol("TESTLIB.dll!fill_record", SLOT, SymbolKind::Import);
    image(&code, vec![import])
}

/// Builds an image whose `A` at [`TEXT`] calls `B`, and whose `B`, `C` and
/// `D` follow it `0x40` apart, each returning a constant; the four are
/// exported as `fa`, `fb`, `fc` and `fd`.
///
/// `A`: `sub rsp,0x28; call B; add rsp,0x28; ret`; `B`, `C`, `D`: `mov
/// eax,k; ret`.
fn exported_four() -> Program {
    let (b, c, d) = (TEXT + 0x40, TEXT + 0x80, TEXT + 0xc0);
    let code: [(u64, &[u8]); 6] = [
        (TEXT, &[0x48, 0x83, 0xec, 0x28]),              // ASM: sub rsp,0x28
        (TEXT + 0x04, &[0xe8, 0x37, 0, 0, 0]),          // ASM: call B
        (TEXT + 0x09, &[0x48, 0x83, 0xc4, 0x28, 0xc3]), // ASM: add rsp,0x28; ret
        (b, &[0xb8, 2, 0, 0, 0, 0xc3]),                 // ASM: mov eax,2; ret
        (c, &[0xb8, 3, 0, 0, 0, 0xc3]),                 // ASM: mov eax,3; ret
        (d, &[0xb8, 4, 0, 0, 0, 0xc3]),                 // ASM: mov eax,4; ret
    ];
    let named = [("fa", TEXT), ("fb", b), ("fc", c), ("fd", d)];
    image(
        &code,
        named
            .map(|(n, at)| symbol(n, at, SymbolKind::Export))
            .to_vec(),
    )
}

/// Every name of a function's answer reads with its kind and its one link.
///
/// Those names are the direct callee, the import called through its slot,
/// the parameter, the local handed to the import and the global; the view
/// spells the answer and marks the signature and local definitions.
///
/// The image is [`filling`]'s, the import called through its slot.
#[test]
fn every_name_of_an_answer_reads_with_its_one_link() {
    let h = TEXT + 0x40;
    let p = filling(false);
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let text = answer(&p, &a, &o, TEXT, Detail::Full).expect("an answer");
    let v = view(&p, &a, &o, TEXT).expect("a view");
    assert_eq!(v.spell(), text);
    let all = tokens(&v);
    let lines: Vec<&str> = text.split('\n').collect();
    let variable = |function, name: &str| Ref::Variable {
        function,
        name: name.into(),
    };
    for (i, word, kind, link) in &all {
        let named = word.starts_with(|c: char| c.is_ascii_alphabetic() || c == '_');
        if !named || *kind == Kind::Comment {
            continue;
        }
        let want = match word.as_str() {
            "sub_140001000" => (Kind::Function, Some(Ref::Function(TEXT))),
            "sub_140001040" => (Kind::Function, Some(Ref::Function(h))),
            "fill_record" => (Kind::Function, Some(Ref::Import(SLOT))),
            "g64_140003000" => (Kind::Global, Some(Ref::Global(GLOBAL))),
            "a1" if lines[*i].starts_with("static inline ") => {
                (Kind::Variable, Some(variable(h, "a1")))
            }
            w if *kind == Kind::Variable => (Kind::Variable, Some(variable(TEXT, w))),
            "return" | "static" | "inline" | "extern" => (Kind::Keyword, None),
            w if w.starts_with("uint") || w.starts_with("int") || w == "void" => (Kind::Type, None),
            w => panic!("{w} on line {i} is no name this text holds:\n{text}"),
        };
        assert_eq!((*kind, link.clone()), want, "{word} on line {i}:\n{text}");
    }
    for spelled in ["sub_140001040", "fill_record", "g64_140003000", "a1"] {
        assert!(
            all.iter()
                .any(|(_, w, _, link)| w == spelled && link.is_some()),
            "{spelled} is never linked:\n{text}"
        );
    }
    let local = all
        .iter()
        .find_map(|(_, w, ..)| w.starts_with("local_").then(|| w.clone()))
        .expect("a local");
    let declared = lines
        .iter()
        .position(|l| !l.starts_with("//") && l.contains(local.as_str()));
    let signature = lines.iter().position(|l| l.starts_with("// signature: "));
    assert_eq!(v.definition(&variable(TEXT, &local)), declared, "{text}");
    assert_eq!(v.definition(&variable(TEXT, "a1")), signature, "{text}");
    assert_eq!(v.definition(&Ref::Function(TEXT)), signature, "{text}");
    assert_eq!(v.unlinked(), Unlinked::default(), "{text}");
}

/// A label reads as one where a label stands, after `goto` and before its
/// colon, links to the block it names, and its colon's line defines it.
///
/// The shared fixture's `LB` (0x5240) keeps the four gotos its flow tests
/// pin.
#[test]
fn a_label_links_to_its_block_and_its_line_defines_it() {
    let p = crate::common::fixture();
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let text = answer(&p, &a, &o, 0x5240, Detail::Full).expect("an answer");
    let v = view(&p, &a, &o, 0x5240).expect("a view");
    assert_eq!(v.spell(), text);
    let lines: Vec<&str> = text.split('\n').collect();
    let labels: Vec<(usize, String, Option<Ref>)> = tokens(&v)
        .into_iter()
        .filter(|(_, _, kind, _)| *kind == Kind::Label)
        .map(|(i, w, _, link)| (i, w, link))
        .collect();
    assert!(
        labels.iter().any(|(i, ..)| lines[*i].contains("goto L_")),
        "{text}"
    );
    for (i, w, link) in &labels {
        let va = u64::from_str_radix(&w[2..], 16).expect("a label's address");
        assert_eq!(
            link.as_ref(),
            Some(&Ref::Address(va)),
            "{w} on line {i}:\n{text}"
        );
        let colon = lines.iter().position(|l| l.trim() == format!("{w}:"));
        assert!(colon.is_some(), "{w} has no line:\n{text}");
        assert_eq!(v.definition(&Ref::Address(va)), colon, "{w}:\n{text}");
    }
}

/// Names no C identifier holds read back byte for byte and link only whole,
/// while two functions named alike link to neither and are counted.
///
/// The names carry quotes, backslashes, non-ASCII letters, comment markers,
/// a 4 KB run, a label's shape, a scope and a newline.
///
/// `TEXT` calls each of ten functions at `TEXT + 0x100` on, 0x10 apart,
/// each `mov eax,k; ret`.
#[test]
fn hostile_names_read_back_and_shared_ones_link_nowhere() {
    let big = "big_".repeat(1024);
    let names = [
        "q\"uote",
        "back\\slash",
        "naïve",
        "a*/b/*c",
        big.as_str(),
        "L_1234",
        "ns::thing",
        "twin",
        "twin",
        "line\nbreak",
    ];
    let at = |k: usize| TEXT + 0x100 + 0x10 * u64::try_from(k).expect("small");
    let mut caller = vec![0x48, 0x83, 0xec, 0x28]; // ASM: sub rsp,0x28
    for k in 0..names.len() {
        let next = TEXT + u64::try_from(caller.len() + 5).expect("small");
        let rel = i32::try_from(at(k) - next).expect("near");
        caller.push(0xe8); // ASM: call the k-th function
        caller.extend(rel.to_le_bytes());
    }
    caller.extend([0x48, 0x83, 0xc4, 0x28, 0xc3]); // ASM: add rsp,0x28; ret
    let bodies: Vec<[u8; 6]> = (0..names.len())
        .map(|k| [0xb8, u8::try_from(k).expect("small"), 0, 0, 0, 0xc3]) // ASM: mov eax,k; ret
        .collect();
    let mut code: Vec<(u64, &[u8])> = vec![(TEXT, caller.as_slice())];
    code.extend(
        bodies
            .iter()
            .enumerate()
            .map(|(k, b)| (at(k), b.as_slice())),
    );
    let symbols = [1, 8, 9]
        .map(|k| symbol(names[k], at(k), SymbolKind::Export))
        .to_vec();
    let p = image(&code, symbols);
    let a = Analysis::compute(&p);
    let mut o = Overlay::default();
    for k in [0, 2, 3, 4, 5, 6, 7] {
        o.names.insert(at(k), names[k].to_owned());
    }
    let text = answer(&p, &a, &o, TEXT, Detail::Full).expect("an answer");
    let v = view(&p, &a, &o, TEXT).expect("a view");
    assert_eq!(v.spell(), text);
    for i in 0..v.lines() {
        let line = v.line(i).expect("a line");
        for (span, ..) in v.tokens(i) {
            assert!(line.is_char_boundary(span.start) && line.is_char_boundary(span.end));
        }
    }
    let all = tokens(&v);
    let linked = |k: usize| {
        all.iter()
            .filter(|(.., link)| *link == Some(Ref::Function(at(k))))
            .map(|(_, w, ..)| w.clone())
            .collect::<Vec<_>>()
    };
    let non_ascii = view_of(&p, &a, &o, TEXT, "naïve();").expect("a view");
    assert_eq!(
        spelled(&non_ascii, "naïve"),
        [(Kind::Function, Some(Ref::Function(at(2))))]
    );
    for k in [4, 5, 6] {
        let words = linked(k);
        assert!(!words.is_empty(), "{} is never linked:\n{text}", names[k]);
        assert!(words.iter().all(|w| w == names[k]), "{words:?}:\n{text}");
    }
    for k in [0, 1, 2, 3, 7, 8, 9] {
        assert!(linked(k).is_empty(), "{} is linked:\n{text}", names[k]);
    }
    let twins: Vec<_> = all.iter().filter(|(_, w, ..)| w == "twin").collect();
    assert!(!twins.is_empty(), "{text}");
    assert!(twins.iter().all(|(.., link)| link.is_none()), "{text}");
    assert!(v.unlinked().ambiguous >= twins.len(), "{:?}", v.unlinked());
}

/// A name the code never reaches gets no link and is counted: a copy run
/// reads as `memcpy`, and the user's name `memcpy` on a function the copy
/// never calls does not make the idiom a call of it.
///
/// `TEXT`: `movups xmm0,[rdx]; movups xmm1,[rdx+0x10]; movups
/// [rcx+0x10],xmm1; movups [rcx],xmm0; ret`, a 32-byte copy; `TEXT +
/// 0x40`: `xor eax,eax; ret`, exported as `unrelated`.
#[test]
fn a_name_the_code_never_reaches_links_nowhere_and_is_counted() {
    let code: [(u64, &[u8]); 6] = [
        (TEXT, &[0x0f, 0x10, 0x02]),              // ASM: movups xmm0,[rdx]
        (TEXT + 0x03, &[0x0f, 0x10, 0x4a, 0x10]), // ASM: movups xmm1,[rdx+0x10]
        (TEXT + 0x07, &[0x0f, 0x11, 0x49, 0x10]), // ASM: movups [rcx+0x10],xmm1
        (TEXT + 0x0b, &[0x0f, 0x11, 0x01]),       // ASM: movups [rcx],xmm0
        (TEXT + 0x0e, &[0xc3]),                   // ASM: ret
        (TEXT + 0x40, &[0x31, 0xc0, 0xc3]),       // ASM: xor eax,eax; ret
    ];
    let p = image(
        &code,
        vec![symbol("unrelated", TEXT + 0x40, SymbolKind::Export)],
    );
    let a = Analysis::compute(&p);
    let copies = |v: &View| {
        tokens(v)
            .into_iter()
            .filter(|(_, w, ..)| w == "memcpy")
            .collect::<Vec<_>>()
    };
    let plain = view(&p, &a, &Overlay::default(), TEXT).expect("a view");
    let calls = copies(&plain);
    assert!(
        !calls.is_empty(),
        "the copy reads as memcpy:\n{}",
        plain.spell()
    );
    assert!(
        calls
            .iter()
            .all(|(_, _, kind, link)| *kind == Kind::Text && link.is_none()),
        "{calls:?}"
    );
    assert_eq!(plain.unlinked(), Unlinked::default());
    let mut o = Overlay::default();
    o.names.insert(TEXT + 0x40, "memcpy".to_owned());
    let renamed = view(&p, &a, &o, TEXT).expect("a view");
    let calls = copies(&renamed);
    assert!(
        !calls.is_empty() && calls.iter().all(|(.., link)| link.is_none()),
        "{calls:?}:\n{}",
        renamed.spell()
    );
    assert!(
        renamed.unlinked().uncorroborated >= calls.len(),
        "{:?}",
        renamed.unlinked()
    );
}

/// A rename lets go of a view only where the old or the new name is in it.
///
/// `A` calls `B`; `C` names neither; `D` is named by no text. Built
/// through a memo of its own, a view reads only what it looked up: renaming
/// `D` carries both views to the new names as they are, and renaming `B`
/// lets go of `A`'s alone, which links `B`'s new name to `B`. Built over the
/// answer ([`view`]), a view reads what the answer read too, so it is
/// carried exactly when the answer is.
///
/// The image is [`exported_four`]'s.
#[test]
fn a_rename_lets_go_of_only_the_views_that_name_it() {
    let (b, c, d) = (TEXT + 0x40, TEXT + 0x80, TEXT + 0xc0);
    let p = exported_four();
    let a = Analysis::compute(&p);
    let reads_of = |o: &Overlay, e: u64| {
        let text = decompile_named(&p, &a, o, e).expect("a text");
        let make = || view_of(&p, &a, o, e, &text);
        a.derived
            .get_or_build_item("view_reads_test", o.fingerprint(), e, make, |_| 0)
    };
    let before = Overlay {
        enum_source: EnumSource::Binary,
        ..Overlay::default()
    };
    let (va, vc) = (reads_of(&before, TEXT), reads_of(&before, c));
    let mut far = before.clone();
    far.names.insert(d, "renamed_d".to_owned());
    a.derived.moved(&a, &before, &far);
    assert!(Arc::ptr_eq(&va, &reads_of(&far, TEXT)));
    assert!(Arc::ptr_eq(&vc, &reads_of(&far, c)));
    let mut near = far.clone();
    near.names.insert(b, "renamed_b".to_owned());
    a.derived.moved(&a, &far, &near);
    let again = reads_of(&near, TEXT);
    assert!(!Arc::ptr_eq(&va, &again));
    let linked = again.as_ref().as_ref().map(tokens).unwrap_or_default();
    assert!(
        linked
            .iter()
            .any(|(_, w, _, link)| w == "renamed_b" && *link == Some(Ref::Function(b))),
        "{linked:?}"
    );
    assert!(Arc::ptr_eq(&vc, &reads_of(&near, c)));
    let a = Analysis::compute(&p);
    let answered: Vec<Arc<View>> = [TEXT, c]
        .map(|e| view(&p, &a, &before, e).expect("a view"))
        .to_vec();
    a.derived.moved(&a, &before, &far);
    for (e, was) in [TEXT, c].into_iter().zip(&answered) {
        let builds = a.derived.builds();
        answer(&p, &a, &far, e, Detail::Full).expect("an answer");
        let carried = a.derived.builds() == builds;
        let now = view(&p, &a, &far, e).expect("a view");
        println!(
            "{e:#x}: answer carried {carried}; {:?}",
            a.derived.read_stats()
        );
        assert_eq!(Arc::ptr_eq(was, &now), carried, "{e:#x}");
    }
}

/// A name reads as what it stands as, and a piece cut from a longer name
/// links nowhere even when a function goes by the piece.
///
/// A struct's member is a field though the function is named alike, and a
/// struct tag is a type though a parameter is named alike.
///
/// The image is [`exported_four`]'s, `A` named `fa`.
#[test]
fn a_name_reads_as_what_it_stands_as_and_a_piece_of_one_links_nowhere() {
    let p = exported_four();
    let a = Analysis::compute(&p);
    let read = |o: &Overlay, text: &str| view_of(&p, &a, o, TEXT, text).expect("a view");
    let plain = Overlay::default();
    let member = read(&plain, "struct s { uint64_t fa; };");
    assert_eq!(spelled(&member, "fa"), [(Kind::Field, None)]);
    let tag = tokens(&read(&plain, "// signature: void fa(struct tm *tm)"));
    let named = tag
        .iter()
        .position(|(_, w, ..)| w == "struct")
        .and_then(|k| tag.get(k + 2))
        .expect("a name after the tag's keyword");
    assert_eq!((named.1.as_str(), named.2), ("tm", Kind::Type), "{tag:?}");
    let mut o = Overlay::default();
    o.names.insert(TEXT, "Foo::bar".to_owned());
    o.names.insert(TEXT + 0x40, "Foo::bar.part.0".to_owned());
    let clone = tokens(&read(&o, "Foo::bar.part.0();"));
    assert!(
        clone
            .iter()
            .all(|(.., link)| *link != Some(Ref::Function(TEXT))),
        "{clone:?}"
    );
}

/// One import listed at many slots is one thing, and looking its name up
/// reads no fact of the overlay per slot.
///
/// The call no fact bears out is counted once, as unborne and not as
/// ambiguous, by a build whose read-set stays small.
///
/// `TEXT`: `ret`; 4,096 import symbols named `free`, one at each slot from
/// [`SLOT`] on.
#[test]
fn an_import_at_many_slots_is_one_thing_and_no_read_per_slot() {
    let slots = (0..4096u64)
        .map(|k| symbol("free", SLOT + 8 * k, SymbolKind::Import))
        .collect();
    let p = image(&[(TEXT, &[0xc3])], slots); // ASM: ret
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let make = || view_of(&p, &a, &o, TEXT, "free();");
    let built = a
        .derived
        .get_or_build_item("view_slots_test", o.fingerprint(), TEXT, make, |_| 0);
    let v = built.as_ref().as_ref().expect("a view");
    assert_eq!(spelled(v, "free"), [(Kind::Function, None)]);
    let counted = Unlinked {
        uncorroborated: 1,
        ambiguous: 0,
    };
    assert_eq!(v.unlinked(), counted);
    let read = a.derived.read_stats();
    assert!(read.keys < 64, "{read:?}");
}

/// A call of an import links to its slot whether it goes through an import
/// stub or straight through a slot the user renamed.
///
/// The images are [`filling`]'s: the import called through the stub, and
/// through its slot, which the user names `my_fill`.
#[test]
fn a_call_of_an_import_links_through_its_stub_and_under_a_slot_name() {
    for stub in [true, false] {
        let p = filling(stub);
        let a = Analysis::compute(&p);
        let mut o = Overlay::default();
        if !stub {
            o.names.insert(SLOT, "my_fill".to_owned());
        }
        let v = view(&p, &a, &o, TEXT).expect("a view");
        let calls = spelled(&v, "fill_record");
        let want = (Kind::Function, Some(Ref::Import(SLOT)));
        assert!(
            !calls.is_empty() && calls.iter().all(|c| *c == want),
            "{calls:?}:\n{}",
            v.spell()
        );
        assert_eq!(v.unlinked().ambiguous, 0, "{}", v.spell());
    }
}

/// A global known only by its name, a data symbol's or one the user gave
/// an address, reads as a global, links nowhere and is counted.
///
/// `TEXT`: `ret`; the data symbol `counter` at `GLOBAL + 8`, and the user's
/// `config` at `GLOBAL + 0x10`.
#[test]
fn a_global_known_only_by_its_name_is_counted() {
    let counter = symbol("counter", GLOBAL + 8, SymbolKind::Data);
    let p = image(&[(TEXT, &[0xc3])], vec![counter]); // ASM: ret
    let a = Analysis::compute(&p);
    let mut o = Overlay::default();
    o.names.insert(GLOBAL + 0x10, "config".to_owned());
    let v = view_of(&p, &a, &o, TEXT, "counter += config;").expect("a view");
    for name in ["counter", "config"] {
        assert_eq!(spelled(&v, name), [(Kind::Global, None)], "{name}");
    }
    let counted = Unlinked {
        uncorroborated: 2,
        ambiguous: 0,
    };
    assert_eq!(v.unlinked(), counted);
}

/// A function-like `#define`'s parameter, an enclosing scope of a lambda or
/// closure, and a destructor named `~fa` never link to the function `fa`,
/// while `~fa`'s own signature keeps `~fa` whole.
///
/// The image is [`exported_four`]'s, `A` exported as `fa` and calling `B`.
#[test]
fn macro_parameters_closures_and_destructors_do_not_link_the_outer_name() {
    let b = TEXT + 0x40;
    let p = exported_four();
    let a = Analysis::compute(&p);
    let plain = Overlay::default();
    let mac = view_of(
        &p,
        &a,
        &plain,
        TEXT,
        "#define m(fa) ((fa) + 1)\nreturn m(1);",
    )
    .expect("a view");
    assert_eq!(
        spelled(&mac, "fa"),
        [(Kind::Variable, None), (Kind::Variable, None)]
    );
    assert_eq!(
        spelled(&mac, "m"),
        [(Kind::Function, None), (Kind::Function, None)]
    );
    let nested = view_of(
        &p,
        &a,
        &plain,
        TEXT,
        "fa()::{lambda}();\nfa::{{closure}}();",
    )
    .expect("a view");
    assert_eq!(
        spelled(&nested, "fa"),
        [(Kind::Text, None), (Kind::Text, None)]
    );
    assert_eq!(spelled(&nested, "lambda"), [(Kind::Text, None)]);
    assert_eq!(spelled(&nested, "closure"), [(Kind::Text, None)]);
    let mut o = Overlay::default();
    o.names.insert(b, "~fa".to_owned());
    let dtor_call = view_of(&p, &a, &o, TEXT, "~fa();").expect("a view");
    assert_eq!(spelled(&dtor_call, "fa"), [(Kind::Text, None)]);
    let caller = view(&p, &a, &o, TEXT).expect("a view");
    for (i, w, _, link) in tokens(&caller) {
        if !caller.line(i).unwrap_or_default().starts_with("//") && w == "fa" {
            assert_eq!(link, None, "line {i}:\n{}", caller.spell());
        }
    }
    let dtor = view(&p, &a, &o, b).expect("a view");
    assert_eq!(
        spelled(&dtor, "~fa"),
        [(Kind::Function, Some(Ref::Function(b)))]
    );
}

/// Bitwise `~` and C array subscripts keep their links, while non-C
/// selectors, colons and `{...}` thunks never link a cut piece.
///
/// The function's own name stays whole on `// signature:`. The image is
/// [`filling`]'s.
#[test]
fn bitwise_not_and_subscripts_link_while_selectors_and_thunks_do_not() {
    let p = filling(false);
    let a = Analysis::compute(&p);
    let plain = Overlay::default();
    let bitnot = view_of(
        &p,
        &a,
        &plain,
        TEXT,
        "return ~g64_140003000 + ~fill_record();",
    )
    .expect("a view");
    assert_eq!(
        spelled(&bitnot, "g64_140003000"),
        [(Kind::Global, Some(Ref::Global(GLOBAL)))]
    );
    assert_eq!(
        spelled(&bitnot, "fill_record"),
        [(Kind::Function, Some(Ref::Import(SLOT)))]
    );
    let indexed = view_of(&p, &a, &plain, TEXT, "return buf[g32_140003000];").expect("a view");
    assert_eq!(
        spelled(&indexed, "g32_140003000"),
        [(Kind::Global, Some(Ref::Global(GLOBAL)))]
    );
    let mut o = Overlay::default();
    o.names.insert(TEXT, "io:fill_record".to_owned());
    let own_sig = view(&p, &a, &o, TEXT).expect("a view");
    let sig = (0..own_sig.lines())
        .find(|&i| {
            own_sig
                .line(i)
                .is_some_and(|l| l.starts_with("// signature: "))
        })
        .expect("a signature line");
    let sig_links: Vec<_> = own_sig
        .tokens(sig)
        .filter_map(|(_, _, link)| link.cloned())
        .collect();
    assert!(sig_links.contains(&Ref::Function(TEXT)), "{sig_links:?}");
    assert!(!sig_links.contains(&Ref::Import(SLOT)), "{sig_links:?}");
    for snippet in [
        "io:fill_record(a1);",
        "// signature: void -[Box fill_record](void *s)\nreturn @selector(fill_record);",
        "{virtual override thunk({offset, -8}, sub_140001040)}(a1);",
    ] {
        let v = view_of(&p, &a, &plain, TEXT, snippet).expect("a view");
        let bad: Vec<_> = tokens(&v)
            .into_iter()
            .filter(|(.., link)| matches!(link, Some(Ref::Import(_) | Ref::Function(_))))
            .collect();
        assert!(bad.is_empty(), "{snippet} linked {bad:?}");
    }
}

/// Two Mach-O libraries exporting `_foo` keep their slots apart as two
/// imports, so `foo();` is ambiguous and unlinked, while two slots bound to
/// the same library's `_foo` stay one import.
#[test]
fn macho_imports_from_distinct_dylibs_stay_distinct() {
    let (base, main, slot) = (0x1_0000_0000u64, 0x1_0000_0400u64, 0x1_0000_1000u64);
    let build = |fixups: &[(usize, Fix)], imports: &[(u8, bool, &str)]| {
        let mut text = vec![0u8; 0x1000];
        text[0x400..0x407].copy_from_slice(&[0xff, 0x15, 0xfa, 0x0b, 0, 0, 0xc3]); // ASM: call [rip+0xbfa]; ret
        let mut data = vec![0u8; 0x1000];
        machogen::chain(&mut data, fixups);
        let starts = [Starts {
            segment: 1,
            format: 6,
            offset: 0x1000,
            page_size: 0x1000,
            pages: vec![0],
        }];
        let payload = machogen::chained(3, &starts, imports);
        let segs = [
            Seg {
                name: "__TEXT",
                vmaddr: base,
                fileoff: 0,
                bytes: text,
                prot: RX,
                sections: vec![Sect {
                    name: "__text",
                    addr: main,
                    size: 7,
                    flags: CODE,
                }],
            },
            Seg {
                name: "__DATA_CONST",
                vmaddr: slot,
                fileoff: 0x1000,
                bytes: data,
                prot: RW,
                sections: vec![Sect {
                    name: "__got",
                    addr: slot,
                    size: 16,
                    flags: 0,
                }],
            },
            Seg {
                name: "__LINKEDIT",
                vmaddr: base + 0x2000,
                fileoff: 0x2000,
                bytes: payload.clone(),
                prot: R,
                sections: Vec::new(),
            },
        ];
        let cmds = vec![
            machogen::main(main - base),
            machogen::dylib("/usr/lib/libA.dylib"),
            machogen::dylib("/usr/lib/libB.dylib"),
            machogen::linkedit(0x8000_0034, 0x2000, payload.len()),
        ];
        let bytes = machogen::build(X86_64, PIE, &segs, &cmds);
        Program::from_bytes(PathBuf::from("two_dylibs.macho"), bytes).expect("loads")
    };
    let two = build(
        &[(0, Fix::Bind(0)), (8, Fix::Bind(1))],
        &[(1, false, "_foo"), (2, false, "_foo")],
    );
    let a = Analysis::compute(&two);
    let v = view_of(&two, &a, &Overlay::default(), main, "foo();").expect("a view");
    assert_eq!(spelled(&v, "foo"), [(Kind::Function, None)]);
    assert_eq!(
        v.unlinked(),
        Unlinked {
            uncorroborated: 0,
            ambiguous: 1,
        }
    );
    let one = build(
        &[(0, Fix::Bind(0)), (8, Fix::Bind(0))],
        &[(1, false, "_foo")],
    );
    let a = Analysis::compute(&one);
    let v = view_of(&one, &a, &Overlay::default(), main, "foo();").expect("a view");
    assert_eq!(
        spelled(&v, "foo"),
        [(Kind::Function, Some(Ref::Import(slot)))]
    );
    assert_eq!(v.unlinked(), Unlinked::default());
}

/// Repeated calls of an import with 4,096 slots in a function referencing
/// 1,024 addresses resolve to the one slot the function calls, reusing the
/// cached lookup across all 2,000 tokens.
#[test]
fn repeated_calls_to_a_many_slot_import_link_its_referenced_slot() {
    let (rdata, data) = (0x1_4000_3000u64, 0x1_4000_b000u64);
    let highest = rdata + 8 * 4095;
    let mut code = Vec::with_capacity(0x1c00);
    for k in 0..1023u64 {
        let next = TEXT + u64::try_from(code.len() + 7).expect("fits");
        let disp = i32::try_from((data + 8 * k) - next).expect("near");
        code.extend_from_slice(&[0x48, 0x8d, 0x05]); // ASM: lea rax,[rip+disp]
        code.extend_from_slice(&disp.to_le_bytes());
    }
    let next = TEXT + u64::try_from(code.len() + 6).expect("fits");
    let disp = i32::try_from(highest - next).expect("near");
    code.extend_from_slice(&[0xff, 0x15]); // ASM: call [rip+disp]
    code.extend_from_slice(&disp.to_le_bytes());
    code.push(0xc3); // ASM: ret
    let mut bytes = vec![0u8; 0xc000];
    bytes[..0x2000].fill(0xcc);
    bytes[..code.len()].copy_from_slice(&code);
    let sections = vec![
        Section::mapped(".text", TEXT, 0, 0x2000, false, true),
        Section::mapped(".rdata", rdata, 0x2000, 0x8000, false, false),
        Section::mapped(".data", data, 0xa000, 0x2000, true, false),
    ];
    let mut p = Program::raw(bytes, Arch::X86_64, 0x1_4000_0000, Some(TEXT), sections);
    p.format = BinaryFormat::Pe;
    p.symbols = (0..4096u64)
        .map(|k| symbol("free", rdata + 8 * k, SymbolKind::Import))
        .collect();
    let a = Analysis::compute(&p);
    assert_eq!(a.refs_from(TEXT).len(), 1024);
    let body = "free();".repeat(2000);
    let v = view_of(&p, &a, &Overlay::default(), TEXT, &body).expect("a view");
    let calls = spelled(&v, "free");
    assert_eq!(calls.len(), 2000);
    assert!(
        calls
            .iter()
            .all(|c| *c == (Kind::Function, Some(Ref::Import(highest))))
    );
    assert_eq!(v.unlinked(), Unlinked::default());
}
