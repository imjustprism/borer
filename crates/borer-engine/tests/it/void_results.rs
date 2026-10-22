//! Functions that return nothing, told from their callers and from the
//! idioms compilers leave at the end of a `void` function: x64 and T32.

#![expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]

use borer_engine::analysis::decompile::decompile;
use borer_engine::analysis::{Analysis, Overlay};
use borer_engine::isa::a32::{Mode, Modes};
use borer_engine::program::{Arch, Program, Section, Symbol, SymbolKind};

use crate::decompiled::{program64, replays_clean};

/// Where the x64 code starts.
const X64: u64 = 0x1_4000_1000;

/// The return verdict of the function at `entry`.
///
/// # Arguments
///
/// * `a` - The analysis.
/// * `entry` - The function's entry.
fn verdict(a: &Analysis, entry: u64) -> Option<bool> {
    a.function(entry).and_then(|f| f.returns_value)
}

/// A `nop` before the epilogue makes a function nobody calls return
/// nothing.
///
/// The one-byte `nop` between the last write of rax and the unwinding of
/// the frame is the closing brace of a `void` function unoptimized GCC
/// code marks, and the text ends without a `return;`; without the `nop`,
/// the value its own instruction left stays its possible result.
#[test]
fn a_nop_before_the_epilogue_returns_nothing() {
    let body = [
        0x55, // ASM: push rbp
        0x48, 0x89, 0xe5, // ASM: mov rbp,rsp
        0x8b, 0x01, // ASM: mov eax,[rcx]
        0x83, 0xc0, 0x01, // ASM: add eax,1
        0x89, 0x01, // ASM: mov [rcx],eax
        0x90, // ASM: nop
        0x5d, // ASM: pop rbp
        0xc3, // ASM: ret
    ];
    let p = program64(&body);
    let a = Analysis::compute(&p);
    assert_eq!(verdict(&a, X64), Some(false));
    let text = decompile(&p, &a, &Overlay::default(), X64).unwrap_or_default();
    assert!(text.contains("// signature: void "), "{text}");
    assert!(!text.contains("return"), "{text}");
    replays_clean(&p, &a, &[X64]);
    let kept: Vec<u8> = body.iter().copied().filter(|&b| b != 0x90).collect();
    let p = program64(&kept);
    let a = Analysis::compute(&p);
    assert_eq!(verdict(&a, X64), None);
}

/// A stack-cookie check run in rax says rax holds no result there: a
/// compiler checks the cookie in another register when rax holds one.
#[test]
fn a_cookie_check_in_rax_returns_nothing() {
    let code = [
        0x48, 0x83, 0xec, 0x18, // ASM: sub rsp,0x18
        0x64, 0x48, 0x8b, 0x04, 0x25, 0x28, 0x00, 0x00, 0x00, // ASM: mov rax,fs:[0x28]
        0x48, 0x89, 0x44, 0x24, 0x08, // ASM: mov [rsp+8],rax
        0x31, 0xc0, // ASM: xor eax,eax
        0xc7, 0x01, 0x01, 0x00, 0x00, 0x00, // ASM: mov dword [rcx],1
        0x48, 0x8b, 0x44, 0x24, 0x08, // ASM: mov rax,[rsp+8]
        0x64, 0x48, 0x2b, 0x04, 0x25, 0x28, 0x00, 0x00, 0x00, // ASM: sub rax,fs:[0x28]
        0x75, 0x05, // ASM: jne 0x140001033
        0x48, 0x83, 0xc4, 0x18, // ASM: add rsp,0x18
        0xc3, // ASM: ret
        0x0f, 0x0b, // ASM: ud2
    ];
    let p = program64(&code);
    let a = Analysis::compute(&p);
    assert_eq!(verdict(&a, X64), Some(false));
}

/// An epilogue clearing the scratch registers with rax returns nothing.
///
/// `xor eax, eax` within a run that clears two or more registers no ABI
/// returns in is code zeroing the registers it used, which leaves rax
/// alone when it holds the result; zeroing rax and rdx alone is a pair of
/// zeros handed back, and a cleared register the exit then stores is a
/// value, so a zero in rax beside it may be the result too.
#[test]
fn a_register_clearing_epilogue_returns_nothing() {
    let cleared = [
        0x89, 0x11, // ASM: mov [rcx],edx
        0x31, 0xc0, // ASM: xor eax,eax
        0x31, 0xd2, // ASM: xor edx,edx
        0x31, 0xc9, // ASM: xor ecx,ecx
        0x31, 0xf6, // ASM: xor esi,esi
        0xc3, // ASM: ret
    ];
    let p = program64(&cleared);
    let a = Analysis::compute(&p);
    assert_eq!(verdict(&a, X64), Some(false));
    let paired = [
        0x89, 0x11, // ASM: mov [rcx],edx
        0x31, 0xc0, // ASM: xor eax,eax
        0x31, 0xd2, // ASM: xor edx,edx
        0xc3, // ASM: ret
    ];
    let p = program64(&paired);
    let a = Analysis::compute(&p);
    assert_eq!(verdict(&a, X64), None);
    let stored = [
        0x31, 0xc0, // ASM: xor eax,eax
        0x31, 0xc9, // ASM: xor ecx,ecx
        0x31, 0xf6, // ASM: xor esi,esi
        0x89, 0x0a, // ASM: mov [rdx],ecx
        0xc3, // ASM: ret
    ];
    let p = program64(&stored);
    let a = Analysis::compute(&p);
    assert_eq!(verdict(&a, X64), None);
}

/// An own write of rax read back before the `ret` is scratch.
///
/// A function whose callers all discard its result returns nothing when
/// the last value its own code left in rax was read back on the way out,
/// for a store; one that hands its own value back unread keeps it as a
/// possible result.
#[test]
fn an_own_write_read_back_is_scratch_when_callers_discard() {
    let mut code = vec![
        0x48, 0x83, 0xec, 0x28, // ASM: sub rsp,0x28
        0xe8, 0x37, 0x00, 0x00, 0x00, // ASM: call 0x140001040
        0xe8, 0x52, 0x00, 0x00, 0x00, // ASM: call 0x140001060
        0x31, 0xc0, // ASM: xor eax,eax
        0x48, 0x83, 0xc4, 0x28, // ASM: add rsp,0x28
        0xc3, // ASM: ret
    ];
    code.resize(0x40, 0xcc);
    code.extend_from_slice(&[
        0x8b, 0x01, // ASM: mov eax,[rcx]
        0x89, 0x02, // ASM: mov [rdx],eax
        0xc3, // ASM: ret
    ]);
    code.resize(0x60, 0xcc);
    code.extend_from_slice(&[
        0x8b, 0x01, // ASM: mov eax,[rcx]
        0xc3, // ASM: ret
    ]);
    let p = program64(&code);
    let a = Analysis::compute(&p);
    assert_eq!(verdict(&a, X64 + 0x40), Some(false));
    assert_eq!(verdict(&a, X64 + 0x60), None);
    replays_clean(&p, &a, &[X64, X64 + 0x40]);
}

/// Where the T32 code starts.
const T32: u64 = 0x4_0000;

/// T32 routines (`clang --target=thumbv7m-none-eabi`), each named in its
/// first instruction's comment.
const ROUTINES: [u16; 31] = [
    0xb580, // ASM: push {r7, lr} (idle)
    0xaf00, // ASM: add r7, sp, #0x0
    0x6803, // ASM: ldr r3, [r0]
    0x600b, // ASM: str r3, [r1]
    0xbf00, // ASM: nop
    0xbd80, // ASM: pop {r7, pc}
    0xb510, // ASM: push {r4, lr} (caller)
    0xf000, 0xf808, // ASM: bl 0x40022 (wrap)
    0x2000, // ASM: movs r0, #0x0
    0xf000, 0xf80b, // ASM: bl 0x4002e (keep)
    0x2000, // ASM: movs r0, #0x0
    0xf000, 0xf80a, // ASM: bl 0x40032 (used)
    0x3001, // ASM: adds r0, #0x1
    0xbd10, // ASM: pop {r4, pc}
    0xb510, // ASM: push {r4, lr} (wrap)
    0x4604, // ASM: mov r4, r0
    0xf000, 0xf808, // ASM: bl 0x4003a (leaf)
    0x6020, // ASM: str r0, [r4]
    0xbd10, // ASM: pop {r4, pc}
    0x1c40, // ASM: adds r0, r0, #0x1 (keep)
    0x4770, // ASM: bx lr
    0xb510, // ASM: push {r4, lr} (used)
    0xf000, 0xf801, // ASM: bl 0x4003a (leaf)
    0xbd10, // ASM: pop {r4, pc}
    0x6800, // ASM: ldr r0, [r0] (leaf)
    0x4770, // ASM: bx lr
];

/// ARM32 results come from what callers do with `r0` and the closing `nop`.
///
/// A result is used where a caller reads `r0` after the call, and is
/// nothing where its callers write `r0` first and it hands back a callee's
/// leftover, or where the GCC `nop` before its epilogue says so though
/// nothing calls it; a value its own instruction left stays a possible
/// result.
#[test]
fn arm32_results_come_from_callers_and_the_closing_nop() {
    let code: Vec<u8> = ROUTINES.iter().flat_map(|h| h.to_le_bytes()).collect();
    let len = u64::try_from(code.len()).unwrap_or(0);
    let text = Section::mapped(".text", T32, 0, len, false, true);
    let mut p = Program::raw(code, Arch::Arm, 0, Some(T32 + 0xc), vec![text]);
    p.modes = Modes::from_marks(vec![(T32, Mode::Thumb)]);
    p.symbols = [("idle", T32), ("caller", T32 + 0xc)]
        .iter()
        .map(|&(name, addr)| Symbol {
            name: name.to_owned(),
            addr,
            kind: SymbolKind::Local,
        })
        .collect();
    let a = Analysis::compute(&p);
    assert_eq!(verdict(&a, T32), Some(false));
    assert_eq!(verdict(&a, T32 + 0x22), Some(false));
    assert_eq!(verdict(&a, T32 + 0x2e), None);
    assert_eq!(verdict(&a, T32 + 0x32), Some(true));
    assert_eq!(verdict(&a, T32 + 0x3a), Some(true));
    let wrap = decompile(&p, &a, &Overlay::default(), T32 + 0x22).unwrap_or_default();
    assert!(wrap.contains("// signature: void "), "{wrap}");
}
