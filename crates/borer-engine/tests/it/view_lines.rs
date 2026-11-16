//! What a decompile view answers of its lines: the token under a byte, the
//! uses of a referent, and the instructions its checked header line names.

#![expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]

use crate::view::{TEXT, exported_four, filling, tokens};
use borer_engine::analysis::decompile::replay::{BlockCheck, TextCheck};
use borer_engine::analysis::decompile::view::{view, view_of};
use borer_engine::analysis::{Analysis, Overlay};
use borer_engine::view::{Kind, Ref, USES_MAX};

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
    let r = Ref::Variable {
        function: TEXT,
        name: local.into(),
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
