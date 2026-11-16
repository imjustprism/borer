//! What a decompile view answers of its lines: the token under a byte and
//! the uses of a referent.

#![expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]

use crate::view::{TEXT, filling, tokens};
use borer_engine::analysis::decompile::view::view;
use borer_engine::analysis::{Analysis, Overlay};
use borer_engine::view::{Kind, Ref};

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
    assert_eq!(v.uses(&r), want, "{text}");
    assert_eq!(v.uses(&Ref::Function(TEXT + 1)), Vec::new());
}
