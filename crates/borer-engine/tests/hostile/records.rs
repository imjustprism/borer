//! Export records over functions that share their code stay within a budget.
//!
//! A table of calls into many stubs that each jump into one long shared run
//! makes every stub's function hold the whole run, so their instructions are
//! the stubs times the run. The records list at most the export's budget of
//! starts ([`starts_budget`]): the file's bytes plus one record's worth, so
//! at most 21 bytes of addresses (`"0xffffffffffffffff",`) per file byte,
//! plus one record's worth, plus the lines and variables, which the C text
//! bounds.

use std::collections::BTreeSet;

use borer_engine::analysis::decompile::export::records::{RECORD_STARTS_MAX, starts_budget};
use borer_engine::analysis::decompile::export::{Library, export_recorded};
use borer_engine::analysis::{Analysis, Overlay};
use borer_engine::program::{Arch, Program, Section};

use super::serial;

/// Stubs the call table reaches.
const STUBS: usize = 300;

/// Instructions of the run every stub jumps into.
const RUN: usize = 4000;

/// Functions that share one long run list no more starts in all than the
/// budget allows, and none more than one record's cap.
///
/// # Panics
///
/// When the records list more starts than the budget or a record more
/// than the cap.
#[test]
fn shared_code_lists_starts_within_the_budget() {
    let _held = serial();
    let rel = |from: usize, to: usize| {
        let from = i64::try_from(from).expect("small");
        let to = i64::try_from(to).expect("small");
        i32::try_from(to - from).expect("near").to_le_bytes()
    };
    let table = 0;
    let stubs = table + STUBS * 5 + 1;
    let run = stubs + STUBS * 5;
    let mut code = Vec::new();
    for i in 0..STUBS {
        code.push(0xe8); // ASM: call rel32
        code.extend_from_slice(&rel(table + i * 5 + 5, stubs + i * 5));
    }
    code.push(0xc3); // ASM: ret
    for i in 0..STUBS {
        code.push(0xe9); // ASM: jmp rel32
        code.extend_from_slice(&rel(stubs + i * 5 + 5, run));
    }
    code.extend(std::iter::repeat_n(0x40, RUN)); // ASM: inc eax
    code.push(0xc3); // ASM: ret
    let len = u64::try_from(code.len()).expect("small");
    let text = Section::mapped(".text", 0x1000, 0, len, false, true);
    let p = Program::raw(code, Arch::X86, 0, Some(0x1000), vec![text]);
    let a = Analysis::compute(&p);
    let all: BTreeSet<u64> = a.functions.iter().map(|f| f.entry).collect();
    let (mut starts, mut most, mut records) = (0usize, 0usize, 0usize);
    let mut each = |_, r: borer_engine::analysis::decompile::export::records::Record| {
        let n: usize = r.blocks.values().map(|b| b.starts.len()).sum();
        starts += n;
        most = most.max(n);
        records += 1;
        Ok(())
    };
    let o = Overlay::default();
    export_recorded(
        &p,
        &a,
        &o,
        Library::Include,
        Some(&all),
        &mut |_| Ok(()),
        &mut each,
    )
    .expect("the sinks take everything");
    let budget = p.bytes.len() + RECORD_STARTS_MAX;
    assert_eq!(starts_budget(&p), budget);
    assert!(records > STUBS / 2, "{records} records");
    assert!(most > 0, "the run's lines stand for its block");
    assert!(
        starts <= budget,
        "{starts} starts over a budget of {budget}"
    );
    assert!(most <= RECORD_STARTS_MAX);
}
