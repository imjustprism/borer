//! What a decompile view answers of its lines.
//!
//! The token under a byte, the uses of a referent, the instructions its
//! checked header line names, and the variable a name is, which the edit
//! path renames it by.

#![expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]

use crate::view::{TEXT, exported_four, filling, tokens};
use borer_engine::analysis::decompile::decompile_named;
use borer_engine::analysis::decompile::replay::{BlockCheck, TextCheck};
use borer_engine::analysis::decompile::view::{view, view_of};
use borer_engine::analysis::edit::{Edit, Force, commit, plan};
use borer_engine::analysis::protos::{Proto, VarKey, slot_words};
use borer_engine::analysis::{Analysis, Overlay};
use borer_engine::dwarf::Subprogram;
use borer_engine::view::{Kind, Ref, USES_MAX};
use std::collections::BTreeMap;

/// Every byte of a decompile view's lines lies in the token `token_at` gives.
///
/// That is the one [`tokens`](borer_engine::view::View::tokens) spans it
/// with; past a line's end there is none, and no line answers an
/// instruction address.
#[test]
fn token_at_finds_the_token_holding_each_byte() {
    let p = filling(false);
    let a = Analysis::compute(&p);
    let v = view(&p, &a, &Overlay::default(), TEXT).expect("a view");
    let mut many = 0;
    for i in 0..v.lines() {
        let len = v.line(i).expect("a line").len();
        let toks: Vec<_> = v.tokens(i).collect();
        many += usize::from(toks.len() > 1);
        for byte in 0..len {
            let want = toks.iter().find(|(span, ..)| span.contains(&byte)).cloned();
            assert_eq!(v.token_at(i, byte), want, "line {i} byte {byte}");
        }
        assert_eq!(v.token_at(i, len), None, "line {i}");
        assert_eq!(v.address(i), None, "line {i}");
    }
    assert!(many > 3, "{}", v.spell());
    assert_eq!(v.token_at(v.lines(), 0), None);
}

/// The uses of a local are each line and range its name is spelled on in
/// code, in order, and no other; a referent no token links to has none.
#[test]
fn uses_of_a_local_are_where_it_is_spelled() {
    let p = filling(false);
    let a = Analysis::compute(&p);
    let v = view(&p, &a, &Overlay::default(), TEXT).expect("a view");
    let text = v.spell();
    let local = tokens(&v)
        .into_iter()
        .find_map(|(_, w, kind, _)| {
            (kind == Kind::Variable && w.starts_with("local_")).then_some(w)
        })
        .expect("a local");
    let local = local.as_str();
    let word = |c: Option<char>| c.is_some_and(|c| c.is_alphanumeric() || c == '_');
    let want: Vec<(usize, std::ops::Range<usize>)> = text
        .split('\n')
        .enumerate()
        .filter(|(_, l)| !l.starts_with("//"))
        .flat_map(|(i, l)| {
            l.match_indices(local)
                .filter(move |&(at, _)| {
                    !word(l[..at].chars().next_back())
                        && !word(l[at + local.len()..].chars().next())
                })
                .map(move |(at, _)| (i, at..at + local.len()))
        })
        .collect();
    assert!(want.len() > 1, "{text}");
    let (stack, _, frame) = slot_words(&p, TEXT);
    let r = Ref::Variable {
        function: TEXT,
        name: local.into(),
        key: VarKey::parse(local, stack, frame).ok(),
    };
    let total = want.len();
    assert_eq!(v.uses(&r), (want, total), "{text}");
    assert_eq!(v.uses(&Ref::Function(TEXT + 1)), (Vec::new(), 0));
}

/// A referent used past the cap shows the first [`USES_MAX`] uses in line
/// order and counts every one.
#[test]
fn uses_past_the_cap_are_counted_in_all() {
    let p = filling(false);
    let a = Analysis::compute(&p);
    let n = USES_MAX + 1;
    let text = format!(
        "// signature: uint64_t sub_140001000(uint64_t a1)\n{{\n{}}}\n",
        "    a1 = a1;\n".repeat(n)
    );
    let v = view_of(&p, &a, &Overlay::default(), TEXT, &text).expect("a view");
    let r = Ref::Variable {
        function: TEXT,
        name: "a1".into(),
        key: Some(VarKey::Param(0)),
    };
    let linked: Vec<(usize, std::ops::Range<usize>)> = (0..v.lines())
        .flat_map(|i| {
            v.tokens(i)
                .filter(|(.., link)| *link == Some(&r))
                .map(move |(span, ..)| (i, span))
                .collect::<Vec<_>>()
        })
        .collect();
    assert!(linked.len() >= 2 * n, "{}", &text[..200]);
    let (shown, total) = v.uses(&r);
    assert_eq!(total, linked.len());
    assert_eq!(shown, linked[..USES_MAX]);
}

/// The checked line of a header links the function's instructions it names.
///
/// Mid-block ones link too; an address inside an instruction or of another
/// function's code stays comment, as does every address of the other
/// header lines, and the view spells its text.
///
/// The image is [`exported_four`]'s: `fa` runs `sub` at `TEXT`, `call` at
/// `+4`, `add` at `+9` and `ret` at `+0xd`; `fb` starts at `+0x40`.
#[test]
fn a_checked_header_links_only_the_functions_own_instructions() {
    let p = exported_four();
    let a = Analysis::compute(&p);
    let text = "// fa @ 0x140001000: 4 instructions\n\
        // checked vs binary: statements as emitted, 1/1 blocks: 0 proved vs lift; disagree at 0x140001004, 0x140001009, 0x140001002, 0x140001040, 0x14000100d (+1 more); unchecked: C spelling\n\
        // next: borer://solve/0x140001004,a1 (compares against 0x140001009: solve tries it as a1)\n\
        uint64_t fa(void)\n\
        {\n    return fb();\n}\n";
    let v = view_of(&p, &a, &Overlay::default(), TEXT, text).expect("a view");
    assert_eq!(v.spell(), text);
    let line = |i: usize| -> Vec<(String, Kind, Option<Ref>)> {
        let l = v.line(i).expect("a line");
        v.tokens(i)
            .map(|(span, kind, link)| (l[span].to_owned(), kind, link.cloned()))
            .collect()
    };
    let linked: Vec<_> = line(1)
        .into_iter()
        .filter(|(_, kind, _)| *kind != Kind::Comment)
        .collect();
    let at = |off: u64| {
        (
            format!("{:#x}", TEXT + off),
            Kind::Address,
            Some(Ref::Address(TEXT + off)),
        )
    };
    assert_eq!(linked, vec![at(4), at(9), at(0xd)], "{text}");
    assert!(
        line(1)
            .iter()
            .all(|(_, kind, link)| *kind == Kind::Address || link.is_none())
    );
    for i in [0, 2] {
        assert_eq!(line(i).len(), 1, "line {i}: {:?}", line(i));
        assert_eq!(line(i)[0].1, Kind::Comment);
    }
    assert_eq!(v.uses(&Ref::Address(TEXT + 9)), (vec![(1, 100..111)], 1));
}

/// A checked line naming one of the function's instructions ten times
/// links only the first eight: the view decodes a block for each number it
/// looks at, so it looks at no more.
#[test]
fn a_checked_header_links_no_more_than_eight_numbers() {
    let p = exported_four();
    let a = Analysis::compute(&p);
    let named = ["0x140001004"; 10].join(", ");
    let text = format!(
        "// checked vs binary: 1/1 blocks: 0 proved vs lift; disagree at {named}; unchecked: C spelling\nuint64_t fa(void)\n{{\n    return 0;\n}}\n"
    );
    let v = view_of(&p, &a, &Overlay::default(), TEXT, &text).expect("a view");
    assert_eq!(v.spell(), text);
    let (shown, total) = v.uses(&Ref::Address(TEXT + 4));
    assert_eq!(total, 8, "{text}");
    assert!(shown.iter().all(|(i, _)| *i == 0));
}

/// The checked line the replay writes, read in a view, links the
/// function's instructions it names and nothing else: the view reads the
/// replay's own wording.
#[test]
fn the_replays_checked_line_links_the_instructions_it_names() {
    let p = exported_four();
    let a = Analysis::compute(&p);
    let check = TextCheck {
        blocks: vec![BlockCheck::default()],
        disagree: vec![TEXT + 2, TEXT + 4, TEXT + 9, TEXT + 0xd, TEXT + 0x40],
    };
    let text = format!(
        "{}\nuint64_t fa(void)\n{{\n    return 0;\n}}\n",
        check.header()
    );
    let v = view_of(&p, &a, &Overlay::default(), TEXT, &text).expect("a view");
    assert_eq!(v.spell(), text);
    let linked: Vec<Option<Ref>> = v
        .tokens(0)
        .filter(|(_, kind, _)| *kind == Kind::Address)
        .map(|(.., link)| link.cloned())
        .collect();
    let want = [4, 9, 0xd].map(|off| Some(Ref::Address(TEXT + off)));
    assert_eq!(linked, want, "{text}");
}

/// Returns [`filling`]'s one stack local: its spelling and its slot's
/// offset from the entry stack pointer.
#[expect(
    clippy::expect_used,
    clippy::panic,
    reason = "the fixture's local is a slot"
)]
fn filling_local() -> (String, i64) {
    let p = filling(false);
    let a = Analysis::compute(&p);
    let v = view(&p, &a, &Overlay::default(), TEXT).expect("a view");
    let local = tokens(&v)
        .into_iter()
        .find_map(|(_, w, kind, _)| {
            (kind == Kind::Variable && w.starts_with("local_")).then_some(w)
        })
        .expect("a local");
    let (stack, _, frame) = slot_words(&p, TEXT);
    match VarKey::parse(&local, stack, frame) {
        Ok(VarKey::Slot(off)) => (local, off),
        other => panic!("{local} is no slot: {other:?}"),
    }
}

/// Returns [`filling`]'s image with a hand-built debug record of its
/// function, and its analysis.
///
/// # Arguments
///
/// * `parameters` - The parameters the record names, in order.
/// * `locals` - The locals it names, by slot offset.
fn debugged(
    parameters: Vec<borer_engine::dwarf::Parameter>,
    locals: BTreeMap<i64, String>,
) -> (borer_engine::program::Program, Analysis) {
    let mut p = filling(false);
    p.debug_functions.push(Subprogram {
        low_pc: TEXT,
        name: "filler".to_owned(),
        parameters,
        return_type: None,
        locals,
    });
    let a = Analysis::compute(&p);
    (p, a)
}

/// Returns the edit that names `var` of [`filling`]'s function `name`.
///
/// # Arguments
///
/// * `var` - The variable as the text spells it.
/// * `field` - The offset it reads as when it spells an unnamed field.
/// * `name` - Its new name.
fn rename(var: &str, field: Option<u64>, name: &str) -> [Edit; 1] {
    [Edit::Var {
        entry: TEXT,
        var: var.to_owned(),
        field,
        name: Some(name.to_owned()),
        ty: None,
    }]
}

/// Plans and commits `edits` over an empty overlay, and returns the name
/// the overlay it leaves gives `key` of [`filling`]'s function, with that
/// overlay.
///
/// # Arguments
///
/// * `(p, a)` - The program and its analysis.
/// * `edits` - The edits.
/// * `key` - The variable read back.
#[expect(clippy::expect_used, reason = "a refused edit fails the test")]
fn committed(
    (p, a): (&borer_engine::program::Program, &Analysis),
    edits: &[Edit],
    key: VarKey,
) -> (Option<String>, Overlay) {
    let mut after = Overlay::default();
    let made = plan(p, a, &after, edits, Force::Refuse).expect("planned");
    commit(p, a, &mut after, &made).expect("committed");
    let named = after.vars.get(&TEXT).and_then(|vs| vs.get(&key));
    (named.map(|v| v.name.clone()), after)
}

/// A local only the debug information names renames through the edit path.
///
/// It links with its slot, and renaming it by that name or by its slot's
/// own spelling states it in the overlay, and the decompile spells the new
/// name.
///
/// The image is [`filling`]'s, its local handed to the import named
/// `packet` by a hand-built debug record.
#[test]
fn a_debug_named_local_renames_through_the_edit_path() {
    let o = Overlay::default();
    let (local, off) = filling_local();
    let key = VarKey::Slot(off);
    let (p, a) = debugged(Vec::new(), BTreeMap::from([(off, "packet".to_owned())]));
    let (stack, shadow, frame) = slot_words(&p, TEXT);
    let text = decompile_named(&p, &a, &o, TEXT).expect("a text");
    assert!(text.contains("packet") && !text.contains(&local), "{text}");
    let v = view(&p, &a, &o, TEXT).expect("a view");
    let linked = tokens(&v)
        .into_iter()
        .find(|(_, w, ..)| w == "packet")
        .map(|(.., kind, link)| (kind, link));
    let want = Ref::Variable {
        function: TEXT,
        name: "packet".into(),
        key: Some(key),
    };
    assert_eq!(linked, Some((Kind::Variable, Some(want))), "{text}");
    for var in ["packet".to_owned(), key.spell(stack, shadow, frame)] {
        let (named, after) = committed((&p, &a), &rename(&var, None, "filled"), key);
        assert_eq!(named.as_deref(), Some("filled"), "{var}");
        let renamed = decompile_named(&p, &a, &after, TEXT).expect("a text");
        assert!(
            renamed.contains("filled") && !renamed.contains("packet"),
            "{var}: {renamed}"
        );
    }
}

/// A debug name that spells another slot's own `local_N` names two
/// variables: the edit path refuses it, naming both, the view keys it to
/// neither, and the debug slot's own spelling still renames it.
#[test]
fn a_debug_name_spelling_another_slot_is_refused() {
    let o = Overlay::default();
    let (local, off) = filling_local();
    let plain = filling(false);
    let (stack, shadow, frame) = slot_words(&plain, TEXT);
    let other = VarKey::Slot(off - 8).spell(stack, shadow, frame);
    let (p, a) = debugged(Vec::new(), BTreeMap::from([(off, other.clone())]));
    let why = plan(&p, &a, &o, &rename(&other, None, "filled"), Force::Refuse)
        .err()
        .map(|e| format!("{e:#}"))
        .expect("refused");
    assert!(why.contains(&other) && why.contains(&local), "{why}");
    let v = view(&p, &a, &o, TEXT).expect("a view");
    let keys: Vec<Option<Ref>> = tokens(&v)
        .into_iter()
        .filter(|(_, w, ..)| *w == other)
        .map(|(.., link)| link)
        .collect();
    let unkeyed = Ref::Variable {
        function: TEXT,
        name: other.as_str().into(),
        key: None,
    };
    assert!(
        !keys.is_empty() && keys.iter().all(|k| *k == Some(unkeyed.clone())),
        "{keys:?}"
    );
    let edits = rename(&local, None, "filled");
    let (named, _) = committed((&p, &a), &edits, VarKey::Slot(off));
    assert_eq!(named.as_deref(), Some("filled"));
}

/// A parameter only the debug information names renames through the edit path.
///
/// It links with its position, and renaming it by that name states it in
/// the overlay; under a stated prototype, whose names the text spells
/// instead, the debug name names nothing.
///
/// The image is [`filling`]'s, its one parameter named `inbound` by a
/// hand-built debug record.
#[test]
fn a_debug_named_parameter_renames_through_the_edit_path() {
    let inbound = borer_engine::dwarf::Parameter {
        name: "inbound".to_owned(),
        type_name: None,
    };
    let (p, a) = debugged(vec![inbound], BTreeMap::new());
    let o = Overlay::default();
    let text = decompile_named(&p, &a, &o, TEXT).expect("a text");
    let v = view(&p, &a, &o, TEXT).expect("a view");
    let want = Ref::Variable {
        function: TEXT,
        name: "inbound".into(),
        key: Some(VarKey::Param(0)),
    };
    let links: Vec<Option<Ref>> = tokens(&v)
        .into_iter()
        .filter(|(_, w, ..)| w == "inbound")
        .map(|(.., link)| link)
        .collect();
    assert!(
        !links.is_empty() && links.iter().all(|l| *l == Some(want.clone())),
        "{text}"
    );
    let edits = rename("inbound", None, "outbound");
    let (named, after) = committed((&p, &a), &edits, VarKey::Param(0));
    assert_eq!(named.as_deref(), Some("outbound"));
    let renamed = decompile_named(&p, &a, &after, TEXT).expect("a text");
    assert!(
        renamed.contains("outbound") && !renamed.contains("inbound"),
        "{renamed}"
    );
    let mut prototyped = o;
    let proto = Proto::parse("uint64_t filler(uint64_t z)").expect("a prototype");
    prototyped.prototypes.insert(TEXT, proto);
    assert!(plan(&p, &a, &prototyped, &edits, Force::Refuse).is_err());
}
