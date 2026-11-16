//! Each block's check as a record, and the header counted from the
//! records.

use super::super::tests::replayed_with;
use super::super::{OUTSIDE_FLOAT, replay_function, replay_tsv};
use super::{DIFFERED, Grade, claims};
use crate::analysis::decompile::expr::{Expr, Op};
use crate::analysis::decompile::lift::EffectKind;
use crate::analysis::decompile::text_check;
use crate::analysis::{Analysis, Overlay};
use crate::program::Program;

/// Three blocks: `test ecx, ecx; je` to a block with a packed float
/// multiply the replay leaves out, or to a `return 1`.
const FLOAT_BETWEEN: [u8; 16] = [
    0x85, 0xc9, // ASM: test ecx, ecx
    0x74, 0x06, // ASM: je 0x100a
    0x0f, 0x59, 0xc1, // ASM: mulps xmm0, xmm1
    0x31, 0xc0, // ASM: xor eax, eax
    0xc3, // ASM: ret
    0xb8, 0x01, 0x00, 0x00, 0x00, // ASM: mov eax, 1
    0xc3, // ASM: ret
];

/// One block storing `rcx` whole through `rdx`.
const STORE: [u8; 4] = [
    0x48, 0x89, 0x0a, // ASM: mov [rdx], rcx
    0xc3, // ASM: ret
];

/// Each block of an answer's check has a record in address order.
///
/// Each is graded as the replay decided it, with the reason one was not
/// checked, and the header counts the records as it counted the replay
/// before them.
#[test]
fn each_block_has_a_record_the_header_counts() {
    let p = Program::raw_x64(&FLOAT_BETWEEN);
    let a = Analysis::compute(&p);
    let check = text_check(&p, &a, &Overlay::default(), 0x1000);
    let check = check.as_ref().as_ref().expect("checked");
    let grades: Vec<_> = check
        .blocks
        .iter()
        .map(|b| (b.start, b.grade, b.why))
        .collect();
    assert_eq!(
        grades,
        [
            (0x1000, Grade::Proved, None),
            (0x1004, Grade::Unchecked, Some(OUTSIDE_FLOAT)),
            (0x100a, Grade::Proved, None),
        ]
    );
    assert!(
        check
            .blocks
            .iter()
            .all(|b| (b.states > 0) == (b.grade != Grade::Unchecked)),
        "{check:?}"
    );
    assert_eq!(
        check.header(),
        "// checked vs binary: statements as emitted, 2/3 blocks: 2 proved vs lift, 1 unknown; unchecked: 1 float/vector, C spelling, later text passes"
    );
}

/// A sweep's replay keeps one record per block, and the records add up to
/// its counts: blocks, blocks compared and proved, states and claims.
#[test]
fn the_records_add_up_to_the_replay() {
    let p = Program::raw_x64(&FLOAT_BETWEEN);
    let a = Analysis::compute(&p);
    let r = replay_function(&p, &a, 0x1000, 1);
    let count = |g: Grade| r.records.iter().filter(|b| b.grade == g).count();
    let states: u64 = r.records.iter().map(|b| u64::from(b.states)).sum();
    let compared: usize = r.records.iter().map(|b| b.claims).sum();
    assert_eq!(r.records.len(), r.blocks, "{}", replay_tsv(&r));
    assert_eq!(r.blocks - count(Grade::Unchecked), r.checked);
    assert_eq!(count(Grade::Proved), r.proved);
    assert_eq!(compared, claims(&r));
    assert_eq!(Ok(states), u64::try_from(r.trials));
}

/// A text that differs from the machine only above a value's low 32 bits
/// is the lane model's roughness: its block is tested, not wrong, and
/// keeps no disagreement.
#[test]
fn a_lane_only_difference_grades_no_block_wrong() {
    let p = Program::raw_x64(&STORE);
    let r = replayed_with(&p, 0x1000, 1, |e| {
        if let EffectKind::Store(s) = &mut e.kind {
            let low = Expr::Const(0xffff_ffff);
            s.2 = Expr::Bin(Op::And, Box::new(s.2.clone()), Box::new(low));
        }
    });
    assert!(
        !r.disagreements.is_empty() && r.wrong().is_empty(),
        "{}",
        replay_tsv(&r)
    );
    let grades: Vec<_> = r.records.iter().map(|b| (b.grade, b.why)).collect();
    assert_eq!(
        grades,
        [(Grade::Tested, Some(DIFFERED))],
        "{}",
        replay_tsv(&r)
    );
    assert!(r.records.iter().all(|b| b.disagreements.is_empty()));
}

/// A text that misstates a store grades its block wrong, and the record
/// spells where the text and the machine part and what each holds.
#[test]
fn a_misstated_store_is_wrong_and_spells_both_values() {
    let p = Program::raw_x64(&STORE);
    let r = replayed_with(&p, 0x1000, 1, |e| {
        if let EffectKind::Store(s) = &mut e.kind {
            s.2 = Expr::Const(0);
        }
    });
    assert_eq!(r.records.len(), 1, "{}", replay_tsv(&r));
    let block = r.records.first().expect("a record");
    assert_eq!(block.grade, Grade::Wrong, "{}", replay_tsv(&r));
    let d = block.disagreements.first().expect("a disagreement kept");
    let spelled = block.spell();
    for part in [
        "block 0x1000: wrong".to_owned(),
        format!("memory {} at {:#x}", d.place, d.at),
        format!(
            "text {:#x}, machine {:#x}, {} bits",
            d.text, d.machine, d.bits
        ),
        "the text passes after the emission are not checked".to_owned(),
    ] {
        assert!(spelled.contains(&part), "{part}\n{spelled}");
    }
}

/// A block proved, and one not checked, spell what their grade means and,
/// for the one not checked, why.
#[test]
fn a_proved_and_an_unchecked_block_spell_their_grade() {
    let p = Program::raw_x64(&FLOAT_BETWEEN);
    let a = Analysis::compute(&p);
    let check = text_check(&p, &a, &Overlay::default(), 0x1000);
    let check = check.as_ref().as_ref().expect("checked");
    let spelled: Vec<String> = check.blocks.iter().map(super::BlockCheck::spell).collect();
    let first = spelled.first().expect("the first block");
    assert!(
        first.starts_with("block 0x1000: proved vs lift: "),
        "{first}"
    );
    assert!(
        first.contains("\nstates tried: 1, claims compared: "),
        "{first}"
    );
    assert_eq!(
        spelled.get(1).map(String::as_str),
        Some(
            "block 0x1004: unchecked: not compared from any state\nnot checked: an instruction outside the checked subset\nthe text passes after the emission are not checked"
        )
    );
}
