//! Export records of functions that round their stack pointer down.
//!
//! A slot addressed through the stack pointer after the rounding has no
//! stated home, and one addressed through the frame pointer set before it
//! keeps its offset from the canonical frame address.

use borer_engine::analysis::decompile::export::records::{Home, Record};
use borer_engine::analysis::decompile::export::{Library, export, export_recorded};
use borer_engine::analysis::{Analysis, Overlay};
use borer_engine::program::Arch;
use std::collections::BTreeSet;

use crate::{common, raw};

/// Returns the record of the function at 0x401000 of `code`.
///
/// # Arguments
///
/// * `arch` - The instruction set.
/// * `code` - The function's bytes.
#[expect(
    clippy::expect_used,
    reason = "a test that has no record has nothing to check"
)]
fn record(arch: Arch, code: &[u8]) -> Record {
    let p = raw::image(arch, code, &[]);
    let a = Analysis::compute(&p);
    let mut records = Vec::new();
    let mut each = |_, r: Record| {
        records.push(r);
        Ok(())
    };
    let o = Overlay::default();
    export_recorded(
        &p,
        &a,
        &o,
        Library::Include,
        None,
        &mut |_| Ok(()),
        &mut each,
    )
    .expect("the sinks take everything");
    records
        .into_iter()
        .find(|r| r.entry == 0x401000)
        .expect("a record of the function")
}

/// Returns the home of the variable `name` the record declares.
///
/// # Arguments
///
/// * `r` - The record.
/// * `name` - The variable's name.
fn home<'r>(r: &'r Record, name: &str) -> Option<&'r Home> {
    r.variables.iter().find(|v| v.name == name).map(|v| &v.home)
}

/// x86-64: a slot past `and rsp, -32` has no home, one through `rbp` has.
///
/// `[rsp+8]` is no place the lift knows (`local_38` has no home), while
/// `[rbp-8]`, through the frame pointer set before the rounding, is 24
/// bytes below the canonical frame address.
#[test]
fn x64_slots_past_a_realigned_stack_pointer_have_no_home() {
    let code = [
        0x55, // ASM: push rbp
        0x48, 0x89, 0xe5, // ASM: mov rbp, rsp
        0x48, 0x83, 0xe4, 0xe0, // ASM: and rsp, -32
        0x48, 0x83, 0xec, 0x40, // ASM: sub rsp, 0x40
        0x89, 0x44, 0x24, 0x08, // ASM: mov [rsp+8], eax
        0x89, 0x4d, 0xf8, // ASM: mov [rbp-8], ecx
        0x48, 0x8d, 0x4c, 0x24, 0x08, // ASM: lea rcx, [rsp+8]
        0x48, 0x8d, 0x55, 0xf8, // ASM: lea rdx, [rbp-8]
        0xe8, 0x05, 0x00, 0x00, 0x00, // ASM: call 0x401026
        0x48, 0x89, 0xec, // ASM: mov rsp, rbp
        0x5d, // ASM: pop rbp
        0xc3, // ASM: ret
        0x31, 0xc0, // ASM: xor eax, eax
        0xc3, // ASM: ret
    ];
    let r = record(Arch::X86_64, &code);
    assert_eq!(home(&r, "local_38"), Some(&Home::Unknown), "{r:?}");
    assert_eq!(home(&r, "local_8"), Some(&Home::Cfa(-24)), "{r:?}");
}

/// 32-bit x86: a slot past `and esp, -8` has no home, one through `ebp` has.
///
/// `[esp+4]` has no home, while `[ebp-4]`, through the frame pointer set
/// before the rounding, is 12 bytes below the canonical frame address.
#[test]
fn x86_slots_past_a_realigned_stack_pointer_have_no_home() {
    let code = [
        0x55, // ASM: push ebp
        0x89, 0xe5, // ASM: mov ebp, esp
        0x83, 0xe4, 0xf8, // ASM: and esp, -8
        0x83, 0xec, 0x20, // ASM: sub esp, 0x20
        0x89, 0x44, 0x24, 0x04, // ASM: mov [esp+4], eax
        0x89, 0x4d, 0xfc, // ASM: mov [ebp-4], ecx
        0x8d, 0x44, 0x24, 0x04, // ASM: lea eax, [esp+4]
        0x50, // ASM: push eax
        0x8d, 0x45, 0xfc, // ASM: lea eax, [ebp-4]
        0x50, // ASM: push eax
        0xe8, 0x04, 0x00, 0x00, 0x00, // ASM: call 0x401022
        0x89, 0xec, // ASM: mov esp, ebp
        0x5d, // ASM: pop ebp
        0xc3, // ASM: ret
        0x31, 0xc0, // ASM: xor eax, eax
        0xc3, // ASM: ret
    ];
    let r = record(Arch::X86, &code);
    let realigned: Vec<&Home> = r
        .variables
        .iter()
        .filter(|v| v.name != "local_4" && v.name.starts_with("local_"))
        .map(|v| &v.home)
        .collect();
    assert!(
        !realigned.is_empty() && realigned.iter().all(|h| **h == Home::Unknown),
        "{r:?}"
    );
    assert_eq!(home(&r, "local_4"), Some(&Home::Cfa(-12)), "{r:?}");
}

/// x86-64: a slot a `push` writes past `and rsp, -32` has no home.
///
/// `rax` is saved by the push across the call and read back through
/// `[rsp]`'s pop, neither of which addresses the slot through a memory
/// operand, so the push itself must mark it.
#[test]
fn x64_a_slot_pushed_past_a_realigned_stack_pointer_has_no_home() {
    let code = [
        0x55, // ASM: push rbp
        0x48, 0x89, 0xe5, // ASM: mov rbp, rsp
        0x48, 0x83, 0xe4, 0xe0, // ASM: and rsp, -32
        0x50, // ASM: push rax
        0xe8, 0x08, 0x00, 0x00, 0x00, // ASM: call 0x401016
        0x59, // ASM: pop rcx
        0x01, 0xc8, // ASM: add eax, ecx
        0x48, 0x89, 0xec, // ASM: mov rsp, rbp
        0x5d, // ASM: pop rbp
        0xc3, // ASM: ret
        0x31, 0xc0, // ASM: xor eax, eax
        0xc3, // ASM: ret
    ];
    let r = record(Arch::X86_64, &code);
    let locals: Vec<&Home> = r
        .variables
        .iter()
        .filter(|v| v.name.starts_with("local_"))
        .map(|v| &v.home)
        .collect();
    assert!(
        !locals.is_empty() && locals.iter().all(|h| **h == Home::Unknown),
        "{r:?}"
    );
}

/// A recorded export writes the plain export's bytes over the shared
/// fixture.
///
/// The fixture's functions hold loops, jump-table and compare-ladder
/// switches, calls and an assert ([`common::fixture`]), so tracing the text
/// for the records is shown to be an observation only.
#[test]
fn a_recorded_export_writes_the_plain_bytes_over_the_shared_fixture() {
    let p = common::fixture();
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let some: BTreeSet<u64> = a.functions.iter().map(|f| f.entry).collect();
    assert!(some.len() > 30, "{} functions", some.len());
    let (mut plain, mut traced, mut records) = (String::new(), String::new(), 0usize);
    let g = export(&p, &a, &o, Library::Include, Some(&some), &mut |t| {
        plain.push_str(t);
        Ok(())
    })
    .expect("the sink takes everything");
    let h = export_recorded(
        &p,
        &a,
        &o,
        Library::Include,
        Some(&some),
        &mut |t| {
            traced.push_str(t);
            Ok(())
        },
        &mut |_, _| {
            records += 1;
            Ok(())
        },
    )
    .expect("the sinks take everything");
    assert!(
        g.written > 30 && records == h.written,
        "{} {} {records}",
        g.written,
        h.written
    );
    assert_eq!(h.head("t") + traced.as_str(), g.head("t") + plain.as_str());
}
