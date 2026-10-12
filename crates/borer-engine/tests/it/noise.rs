//! Lines the pseudo-C prints that say nothing about the program: phantom
//! second results, float results nobody reads, imports declared as
//! variables, dead stores and the spills of a variadic prologue.

#![expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]

use crate::decompiled::decompiled;
use crate::raw::image;

use borer_engine::analysis::Analysis;
use borer_engine::analysis::decompile::cleanup;
use borer_engine::program::Arch;

/// Pads `code` with `int3` up to `len` bytes, where the next function
/// starts.
///
/// # Arguments
///
/// * `code` - The bytes so far.
/// * `len` - The offset the next function starts at.
fn pad(code: &mut Vec<u8>, len: usize) {
    code.resize(len, 0xcc);
}

/// A call site whose scan runs out before anything reads or writes `rdx`
/// is no evidence of a second result.
///
/// `call PAIR` followed by thirteen `nop`s and `ret`, where `PAIR` is `mov
/// eax,1; mov edx,2; ret`: the twelve-instruction scan after the call
/// loses the site, and a lost site made `PAIR` hand back `rdx`, which put
/// a phantom `rdx = PAIR__rdx()` beside every call to it.
#[test]
fn a_call_site_the_scan_loses_is_no_second_result() {
    let mut code = vec![
        0xe8, 0x1b, 0x00, 0x00, 0x00, // ASM: call 0x401020
    ];
    code.extend_from_slice(&[0x90; 13]); // ASM: nop (thirteen times)
    code.push(0xc3); // ASM: ret
    pad(&mut code, 0x20);
    code.extend_from_slice(&[
        0xb8, 0x01, 0x00, 0x00, 0x00, // ASM: mov eax, 1
        0xba, 0x02, 0x00, 0x00, 0x00, // ASM: mov edx, 2
        0xc3, // ASM: ret
    ]);
    let p = image(Arch::X86_64, &code, &[]);
    let a = Analysis::compute(&p);
    let pair = a.function(0x401020).expect("the callee");
    assert!(!pair.hands_back_rdx, "a lost site made a second result");
}

/// A caller that reads only `rax` after a call shows no second result,
/// though another caller of the same function reads `rdx`.
///
/// `PAIR` is `lea rax,[rcx+1]; mov edx,7; ret`; the first caller ends
/// `call PAIR; mov rax,rdx; ret`, the second `call PAIR; add rax,1; ret`,
/// whose `ret` hands back `rax` alone: the text wrote `rdx =
/// PAIR__rdx();` there too.
#[test]
fn a_caller_reading_only_rax_shows_no_second_result() {
    let mut code = vec![
        0xe8, 0x1b, 0x00, 0x00, 0x00, // ASM: call 0x401020
        0x48, 0x89, 0xd0, // ASM: mov rax, rdx
        0xc3, // ASM: ret
    ];
    pad(&mut code, 0x20);
    code.extend_from_slice(&[
        0x48, 0x8d, 0x41, 0x01, // ASM: lea rax, [rcx+1]
        0xba, 0x07, 0x00, 0x00, 0x00, // ASM: mov edx, 7
        0xc3, // ASM: ret
    ]);
    pad(&mut code, 0x40);
    code.extend_from_slice(&[
        0xe8, 0xdb, 0xff, 0xff, 0xff, // ASM: call 0x401020
        0x48, 0x83, 0xc0, 0x01, // ASM: add rax, 1
        0xc3, // ASM: ret
    ]);
    let p = image(Arch::X86_64, &code, &[]);
    let reader = decompiled(&p, 0x401000);
    assert!(reader.contains("sub_401020__rdx("), "{reader}");
    let other = decompiled(&p, 0x401040);
    assert!(!other.contains("__rdx"), "{other}");
}

/// A second result nothing reads goes like any other dead assignment: it
/// only names what the call on the line before left in `rdx`.
#[test]
fn a_dead_second_result_is_dropped() {
    let body = "f(rsi, a1);\nrdx = f__rdx(rsi, rdx);\nreturn rax;\n";
    let text = cleanup(body);
    assert!(!text.contains("__rdx"), "{text}");
    assert!(text.contains("f(rsi, a1);"), "{text}");
}
