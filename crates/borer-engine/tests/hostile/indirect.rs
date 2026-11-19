//! A census of unresolved calls over many functions and classes keeps
//! each site's candidates to its cap and counts the rest.
//!
//! Many sites sharing a function, a slot's stores or a trampoline take
//! bounded time.

use std::sync::Arc;
use std::time::Duration;

use borer_engine::analysis::Analysis;
use borer_engine::analysis::render::{CANDIDATES_MAX, Census, Form, census};
use borer_engine::analysis::vtables::ClassInfo;
use borer_engine::program::{Arch, Program, Section};

use super::{measured, serial};

/// Functions the image's entry calls, each a lone `ret`.
const FUNCTIONS: usize = 100_000;

/// Classes, each holding one of the functions in slot 0.
const CLASSES: usize = 10_000;

/// Most bytes building the census may take beyond the analysis, per byte
/// of the file.
///
/// It holds what each function's branch sites land on, one function
/// at a time (the count of unresolved calls read it so before), and the
/// classes holding one slot, by name. A hundred thousand calls in one
/// function measured 16 bytes per file byte (2026-11-19).
const CENSUS_HEAP_PER_BYTE: usize = 20;

/// Ten thousand classes holding a function in slot 0 give a call through
/// slot 0 ten thousand candidates, of which it keeps [`CANDIDATES_MAX`]
/// and counts the rest, within [`CENSUS_HEAP_PER_BYTE`].
#[test]
fn a_slot_every_class_fills_keeps_its_candidates_to_the_cap() {
    let _held = serial();
    let stubs = 0x1000 + FUNCTIONS * 5 + 0x10;
    let mut code = Vec::with_capacity(stubs - 0x1000 + FUNCTIONS);
    for k in 0..FUNCTIONS {
        let next = 0x1000 + (k + 1) * 5;
        let rel = i32::try_from(stubs + k - next).expect("a near call");
        code.push(0xe8); // ASM: call stub_k
        code.extend(rel.to_le_bytes());
    }
    code.extend([0x48, 0x8b, 0x01]); // ASM: mov rax,[rcx]
    code.extend([0xff, 0x10]); // ASM: call [rax]
    code.push(0xc3); // ASM: ret
    code.resize(stubs - 0x1000, 0xcc);
    code.resize(stubs - 0x1000 + FUNCTIONS, 0xc3);
    let bytes = code.len();
    let len = u64::try_from(bytes).expect("fits");
    let text = Section::mapped(".text", 0x1000, 0, len, false, true);
    let p = Program::raw(code, Arch::X86_64, 0, Some(0x1000), vec![text]);
    let mut a = Analysis::compute(&p);
    let stub = |k: usize| u64::try_from(stubs + k * (FUNCTIONS / CLASSES)).expect("fits");
    for k in 0..CLASSES {
        a.classes.by_name.insert(
            format!("C{k:05}"),
            ClassInfo {
                name: format!("C{k:05}"),
                vtable: None,
                slots: vec![stub(k)],
                parent: None,
                ctors: Vec::new(),
                creators: Vec::new(),
            },
        );
    }
    let (found, heap) = measured(|| census(&p, &a));
    let call = u64::try_from(0x1000 + FUNCTIONS * 5 + 3).expect("fits");
    let site = found
        .sites
        .iter()
        .find(|s| s.at == call)
        .expect("the call is listed");
    assert_eq!(site.form, Form::VtableSlot { slot: 0 });
    assert_eq!(site.candidates_total, CLASSES);
    assert_eq!(site.candidates.len(), CANDIDATES_MAX);
    assert!(
        found
            .sites
            .iter()
            .all(|s| s.candidates.len() <= CANDIDATES_MAX)
    );
    assert!(
        heap <= bytes * CENSUS_HEAP_PER_BYTE,
        "the census took {heap} bytes for {bytes} bytes of file"
    );
}

/// Longest a census of a hostile image may take, in seconds.
const CENSUS_SECS: u64 = 10;

/// Returns a census of an image and how long building it took.
///
/// # Arguments
///
/// * `p` - The image.
/// * `a` - Its analysis.
fn timed(p: &Program, a: &Analysis) -> (Arc<Census>, Duration) {
    #[expect(
        clippy::disallowed_methods,
        reason = "the test bounds the time a hostile image takes"
    )]
    let started = std::time::Instant::now();
    let found = census(p, a);
    (found, started.elapsed())
}

/// Returns an x86-64 image with `code` at 0x1000 and `data` zeroed,
/// writable bytes right after it, page aligned.
///
/// # Arguments
///
/// * `code` - The bytes of `.text`.
/// * `data` - How many bytes of `.data`.
fn image(mut code: Vec<u8>, data: usize) -> Program {
    let text = code.len().next_multiple_of(0x1000);
    code.resize(text + data, 0);
    let len = u64::try_from(text).expect("fits");
    let size = u64::try_from(data).expect("fits");
    let sections = vec![
        Section::mapped(".text", 0x1000, 0, len, false, true),
        Section::mapped(".data", 0x1000 + len, len, size, true, false),
    ];
    Program::raw(code, Arch::X86_64, 0, Some(0x1000), sections)
}

/// Returns the displacement from `next` to `to`, as a near call or a
/// rip-relative operand spells it.
///
/// # Arguments
///
/// * `next` - The address after the instruction.
/// * `to` - The address it names.
fn rel(next: usize, to: usize) -> [u8; 4] {
    let d = i64::try_from(to).expect("fits") - i64::try_from(next).expect("fits");
    i32::try_from(d).expect("a near address").to_le_bytes()
}

/// Calls through slots filled at run time, all in one function, are
/// each a row, read in time.
///
/// Each site's function has as many sites, and each slot's store sits in
/// one long block before them.
#[test]
fn many_calls_through_stored_slots_in_one_function_take_bounded_time() {
    const CALLS: usize = 40_000;
    let _held = serial();
    let data = 0x1000 + (CALLS * 13 + 1).next_multiple_of(0x1000);
    let mut code = Vec::with_capacity(CALLS * 13 + 1);
    for k in 0..CALLS {
        code.extend([0x48, 0x89, 0x05]); // ASM: mov [rip+slot_k],rax
        code.extend(rel(0x1000 + code.len() + 4, data + k * 8));
    }
    for k in 0..CALLS {
        code.extend([0xff, 0x15]); // ASM: call [rip+slot_k]
        code.extend(rel(0x1000 + code.len() + 4, data + k * 8));
    }
    code.push(0xc3); // ASM: ret
    let p = image(code, CALLS * 8);
    let a = Analysis::compute(&p);
    let (found, took) = timed(&p, &a);
    assert_eq!(found.sites.len(), CALLS);
    assert!(
        found
            .sites
            .iter()
            .all(|s| matches!(s.form, Form::Global { .. })),
        "{:?}",
        found.sites.first()
    );
    assert!(
        took < Duration::from_secs(CENSUS_SECS),
        "a census of {CALLS} calls took {took:?}"
    );
}

/// Calls into one long trampoline: every call is a row, read in time,
/// though the trampoline's block is tens of thousands of instructions.
#[test]
fn many_calls_into_one_long_trampoline_take_bounded_time() {
    const CALLS: usize = 20_000;
    const STEPS: usize = 70_000;
    let _held = serial();
    let tramp = (CALLS * 5 + 1).next_multiple_of(0x10);
    let mut code = Vec::with_capacity(tramp + STEPS * 3 + 2);
    for _ in 0..CALLS {
        code.push(0xe8); // ASM: call tramp
        code.extend(rel(0x1000 + code.len() + 4, 0x1000 + tramp));
    }
    code.push(0xc3); // ASM: ret
    code.resize(tramp, 0xcc);
    for _ in 0..STEPS {
        code.extend([0x83, 0xc1, 0x01]); // ASM: add ecx,1
    }
    code.extend([0xff, 0xe0]); // ASM: jmp rax
    let p = image(code, 0x10);
    let a = Analysis::compute(&p);
    let (found, took) = timed(&p, &a);
    assert_eq!(found.sites.len(), CALLS);
    assert!(
        took < Duration::from_secs(CENSUS_SECS),
        "a census of {CALLS} calls into a trampoline of {STEPS} steps took {took:?}"
    );
}

/// A direct call whose reference the per-target cap dropped is no row:
/// it names its target, it is only not listed.
#[test]
fn a_direct_call_past_the_reference_cap_is_no_row() {
    const CALLS: usize = 65_537;
    let _held = serial();
    let callee = (CALLS * 5 + 1).next_multiple_of(0x10);
    let mut code = Vec::with_capacity(callee + 1);
    for _ in 0..CALLS {
        code.push(0xe8); // ASM: call callee
        code.extend(rel(0x1000 + code.len() + 4, 0x1000 + callee));
    }
    code.push(0xc3); // ASM: ret
    code.resize(callee, 0xcc);
    code.push(0xc3); // ASM: ret
    let p = image(code, 0x10);
    let a = Analysis::compute(&p);
    let found = census(&p, &a);
    assert_eq!(found.sites, Vec::new());
}

/// Calls through one vtable slot that eight classes fill share one
/// candidate list.
///
/// Each call ends its own block, and the census stays within
/// [`CENSUS_HEAP_PER_BYTE`] however many sites call through the slot. The
/// bound covers this input's six-byte sites: each site costs the census a
/// fixed row and block entry beside the shared list, so the cost is linear
/// in sites, and two-byte sites (`call rax`) cost about three times as much
/// per file byte (about 44).
#[test]
fn many_calls_through_one_slot_share_its_candidates() {
    const CALLS: usize = 100_000;
    const HOLDERS: usize = 8;
    let _held = serial();
    let stubs = (HOLDERS * 5 + CALLS * 6 + 1).next_multiple_of(0x10);
    let mut code = Vec::with_capacity(stubs + HOLDERS);
    for k in 0..HOLDERS {
        code.push(0xe8); // ASM: call stub_k
        code.extend(rel(0x1000 + code.len() + 4, 0x1000 + stubs + k));
    }
    for _ in 0..CALLS {
        code.extend([0x48, 0x8b, 0x01]); // ASM: mov rax,[rcx]
        code.extend([0xff, 0x50, 0x08]); // ASM: call [rax+8]
    }
    code.push(0xc3); // ASM: ret
    code.resize(stubs, 0xcc);
    code.resize(stubs + HOLDERS, 0xc3);
    let bytes = code.len();
    let p = image(code, 0x10);
    let mut a = Analysis::compute(&p);
    for k in 0..HOLDERS {
        let stub = u64::try_from(0x1000 + stubs + k).expect("fits");
        a.classes.by_name.insert(
            format!("C{k}"),
            ClassInfo {
                name: format!("C{k}"),
                slots: vec![0, stub],
                ..ClassInfo::default()
            },
        );
    }
    let (found, heap) = measured(|| census(&p, &a));
    assert_eq!(found.sites.len(), CALLS);
    assert!(
        found
            .sites
            .iter()
            .all(|s| s.candidates_total == HOLDERS && s.candidates.len() == HOLDERS)
    );
    assert!(
        heap <= bytes * CENSUS_HEAP_PER_BYTE,
        "the census took {heap} bytes for {bytes} bytes of file"
    );
}
