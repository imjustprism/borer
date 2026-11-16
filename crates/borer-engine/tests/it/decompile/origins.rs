//! Which block each line of an answer stands for: the one block whose
//! lifted code spells it, carried through the text passes.

use super::*;
use borer_engine::analysis::decompile::{Detail, answer, answer_with_origins};

/// The answer of one function of `code` at 0x140001000 and the block each
/// of its lines stands for, checked to be the plain answer, one origin per
/// line.
///
/// # Arguments
///
/// * `code` - The function's bytes.
#[expect(
    clippy::expect_used,
    reason = "a function that does not decompile has nothing to check"
)]
fn traced(code: &[u8]) -> (String, Vec<Option<u64>>) {
    let p = program64(code);
    let a = Analysis::compute(&p);
    let o = Overlay::default();
    let entry = 0x1_4000_1000;
    let (text, lines) = answer_with_origins(&p, &a, &o, entry).expect("decompiles");
    assert_eq!(
        Some(&text),
        answer(&p, &a, &o, entry, Detail::Full).as_ref()
    );
    assert_eq!(lines.len(), text.lines().count(), "{text}");
    let each = (0..lines.len()).map(|i| lines.line(i)).collect();
    (text, each)
}

/// Each store of a two-block function stands for the block that writes
/// it, and a header line for none.
///
/// `cmp edx,5; jne L; mov dword [rcx],1; ret; L: mov dword [rcx+4],2;
/// ret` keeps both stores through the passes.
#[test]
fn each_store_stands_for_the_block_that_writes_it() {
    let (text, lines) = traced(&[
        0x83, 0xfa, 0x05, // ASM: cmp edx,5
        0x75, 0x07, // ASM: jne 0x14000100c
        0xc7, 0x01, 0x01, 0x00, 0x00, 0x00, // ASM: mov dword [rcx],1
        0xc3, // ASM: ret
        0xc7, 0x41, 0x04, 0x02, 0x00, 0x00, 0x00, // ASM: mov dword [rcx+4],2
        0xc3, // ASM: ret
    ]);
    let at = |end: &str| text.lines().position(|l| l.trim().ends_with(end));
    assert_eq!(
        at("= 1;").map(|i| lines[i]),
        Some(Some(0x1_4000_1005)),
        "{text}"
    );
    assert_eq!(
        at("= 2;").map(|i| lines[i]),
        Some(Some(0x1_4000_100c)),
        "{text}"
    );
    assert_eq!(lines[1], None, "a header line: {text}");
}

/// A return tail the emitter copies under another block's label stands for
/// the tail's block or for none, never for the block it was copied into.
///
/// `mov eax,2; test ecx,ecx; jz R; mov eax,1; jmp R; R: ret`: R has two
/// ways in.
#[test]
fn a_copied_return_stands_for_its_own_block() {
    let (text, lines) = traced(&[
        0xb8, 0x02, 0x00, 0x00, 0x00, // ASM: mov eax,2
        0x85, 0xc9, // ASM: test ecx,ecx
        0x74, 0x07, // ASM: jz 0x140001010
        0xb8, 0x01, 0x00, 0x00, 0x00, // ASM: mov eax,1
        0xeb, 0x00, // ASM: jmp 0x140001010
        0xc3, // ASM: ret
    ]);
    for (line, origin) in text.lines().zip(&lines) {
        if line.trim().starts_with("return") {
            assert!(
                origin.is_none_or(|b| b == 0x1_4000_1010),
                "{line} stands for {origin:x?}:\n{text}"
            );
        }
    }
}

/// A loop header's load the emitter writes again after the body stands
/// for the header or for none, never for the body's last block.
///
/// `xor eax,eax; L: mov edx,[rcx+rax*4]; test edx,edx; je D; inc eax; jmp
/// L; D: ret`.
#[test]
fn a_header_written_after_the_body_stands_for_the_header() {
    let (text, lines) = traced(&[
        0x31, 0xc0, // ASM: xor eax,eax
        0x8b, 0x14, 0x81, // ASM: mov edx,[rcx+rax*4]
        0x85, 0xd2, // ASM: test edx,edx
        0x74, 0x04, // ASM: je 0x14000100d
        0xff, 0xc0, // ASM: inc eax
        0xeb, 0xf5, // ASM: jmp 0x140001002
        0xc3, // ASM: ret
    ]);
    for (line, origin) in text.lines().zip(&lines) {
        if line.contains("a1 +") && !line.contains("+= 1") {
            assert!(
                origin.is_none_or(|b| b == 0x1_4000_1002),
                "{line} stands for {origin:x?}:\n{text}"
            );
        }
    }
}
