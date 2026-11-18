//! One answer of a block's grade and evidence for a function's check
//! ([`BlockAnswer`]), and how a recheck's record takes the place of the
//! check's ([`TextCheck::put_recheck`]).

#![expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]

use borer_engine::analysis::decompile::replay::{
    ANSWER_SEED, BlockAnswer, BlockCheck, Claim, Disagreement, Grade, Prior, Rechecked, TextCheck,
    recheck_block, recheck_states,
};
use borer_engine::analysis::decompile::text_check;
use borer_engine::analysis::{Analysis, Overlay};
use borer_engine::program::{Arch, BinaryFormat, Program, Section};

/// Returns a disagreement found at `0x1000` in block `0x1000`.
fn found() -> Disagreement {
    Disagreement {
        function: 0x1000,
        block: 0x1000,
        at: 0x1000,
        claim: Claim::Memory,
        place: "[rdx]".to_owned(),
        text: 0,
        machine: 0x1234,
        bits: 64,
        lane: false,
        expr: "0".to_owned(),
    }
}

/// A check of two blocks: `0x1000` wrong from 3 states, `0x1010` tested.
fn check() -> TextCheck {
    TextCheck {
        blocks: vec![
            BlockCheck::new(0x1000, Ok(Some("differed")), (3, 1), vec![found()]),
            BlockCheck::new(0x1010, Ok(Some("differed")), (3, 1), Vec::new()),
        ],
        disagree: vec![0x1000],
    }
}

/// No check, no record and a record each answer in their own words, and
/// only a record grades the block other than unchecked.
#[test]
fn no_check_and_no_record_are_told_apart() {
    let c = check();
    let none = BlockAnswer::of(None, 0x1000);
    assert_eq!(none.grade(), Grade::Unchecked);
    assert_eq!(
        none.spell(),
        "block 0x1000: unchecked: no check ran: the function does not decompile or the image has no emulator"
    );
    let missing = BlockAnswer::of(Some(&c), 0x1020);
    assert_eq!(missing.grade(), Grade::Unchecked);
    assert_eq!(
        missing.spell(),
        "block 0x1020: unchecked: the check holds no record of it"
    );
    let wrong = BlockAnswer::of(Some(&c), 0x1000);
    assert_eq!(wrong.grade(), Grade::Wrong);
    assert!(
        wrong.spell().starts_with("block 0x1000: wrong:"),
        "{}",
        wrong.spell()
    );
    assert_eq!(BlockAnswer::of(Some(&c), 0x1010).grade(), Grade::Tested);
}

/// A recheck from fewer states never clears a wrong found from more; one
/// from as many replaces it and says what it replaced; one of a block the
/// check holds no record of is added in address order.
#[test]
fn a_recheck_from_fewer_states_keeps_a_wrong() {
    let mut c = check();
    let tested = |states| BlockCheck::new(0x1000, Ok(Some("differed")), (states, 1), Vec::new());
    let was = Prior {
        grade: Grade::Wrong,
        states: 3,
        rechecked: false,
    };
    assert_eq!(c.put_recheck(tested(2)), Rechecked::KeptWrong(was));
    assert_eq!(BlockAnswer::of(Some(&c), 0x1000).grade(), Grade::Wrong);
    assert_eq!(c.put_recheck(tested(3)), Rechecked::Replaced(was));
    assert_eq!(BlockAnswer::of(Some(&c), 0x1000).grade(), Grade::Tested);
    let new = BlockCheck::new(0x1008, Ok(None), (3, 1), Vec::new());
    assert_eq!(c.put_recheck(new), Rechecked::Added);
    let starts: Vec<u64> = c.blocks.iter().map(BlockCheck::start).collect();
    assert_eq!(starts, [0x1000, 0x1008, 0x1010]);
}

/// A recheck never tries fewer states than the check's own three; a second
/// recheck of a block says it replaced the first.
#[test]
fn a_recheck_tries_at_least_the_check_states() {
    assert_eq!(recheck_states(1), 3);
    assert_eq!(recheck_states(64), 64);
    assert_eq!(recheck_states(u32::MAX), 256);
    let mut bytes = vec![0xcc; 0x100];
    bytes[..4].copy_from_slice(&[0x48, 0x89, 0x0a, 0xc3]); // ASM: mov [rdx], rcx ; ret
    let text = Section::mapped(".text", 0x1000, 0, 0x100, false, true);
    let mut p = Program::raw(bytes, Arch::X86_64, 0x1000, Some(0x1000), vec![text]);
    p.format = BinaryFormat::Pe;
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let once = recheck_block(&p, &a, &o, 0x1000, 0x1000, ANSWER_SEED, 1).expect("rechecked");
    assert_eq!(once.states(), 3, "{once:?}");
    let mut c = (*text_check(&p, &a, &o, 0x1000)).clone().expect("a check");
    let first = c.put_recheck(once.clone());
    assert!(
        matches!(
            first,
            Rechecked::Replaced(Prior {
                rechecked: false,
                ..
            })
        ),
        "{first:?}"
    );
    let again = c.put_recheck(once);
    assert!(
        matches!(
            again,
            Rechecked::Replaced(Prior {
                rechecked: true,
                ..
            })
        ),
        "{again:?}"
    );
}
