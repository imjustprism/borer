//! Code that moves the stack pointer to the far end of the 64-bit range
//! and then works on the stack there: each case decompiles.

use borer_engine::analysis::decompile::decompile;
use borer_engine::analysis::{Analysis, Overlay};
use borer_engine::program::{Arch, Program, Section, Symbol, SymbolKind};

/// A push, a pop, a `leave`, stores, loads and calls at a stack offset the
/// code moved to the end of the 64-bit range decompile, where a sum over
/// the offset overflowed.
///
/// `add rsp, rax` moves the stack pointer by whatever `rax` holds, so the
/// offset folded to `i64::MIN` or within a word of `i64::MAX`, and a
/// subtraction of the size `rax` held before a call moved it as far. The next push,
/// pop or `leave` moved it by a word; a second store to the slot there
/// added the first one's width; a call added its home space; a load
/// through `rsp` plus a register spanned the slot past it; a load at the
/// offset was named by its distance from the first stack argument: each a
/// panic in a build that traps overflow. The lifter now folds and probes
/// an offset only within a reach of the entry's, which a push or a pop
/// passes only by a word.
#[test]
fn a_stack_move_past_the_offset_range_decompiles() {
    let after = |imm: u64, rest: &[u8]| {
        let mut code = vec![0x48, 0xb8]; // ASM: mov rax, imm
        code.extend(imm.to_le_bytes());
        code.extend(rest);
        code
    };
    let top = i64::MAX.cast_unsigned();
    let cases = [
        after(
            1 << 63,
            &[
                0x48, 0x01, 0xc4, // ASM: add rsp, rax
                0x50, // ASM: push rax
                0xc3, // ASM: ret
            ],
        ),
        after(
            top - 7,
            &[
                0x48, 0x01, 0xc4, // ASM: add rsp, rax
                0x59, // ASM: pop rcx
                0xc3, // ASM: ret
            ],
        ),
        after(
            top - 7,
            &[
                0x48, 0x01, 0xe0, // ASM: add rax, rsp
                0x48, 0x89, 0xc5, // ASM: mov rbp, rax
                0xc9, // ASM: leave
                0xc3, // ASM: ret
            ],
        ),
        after(
            top - 3,
            &[
                0x48, 0x01, 0xc4, // ASM: add rsp, rax
                0x48, 0x89, 0x0c, 0x24, // ASM: mov [rsp], rcx
                0x66, 0x89, 0x14, 0x24, // ASM: mov [rsp], dx
                0xc3, // ASM: ret
            ],
        ),
        after(
            top - 7,
            &[
                0x48, 0x01, 0xc4, // ASM: add rsp, rax
                0xff, 0xd1, // ASM: call rcx
                0xc3, // ASM: ret
            ],
        ),
        after(
            top - 3,
            &[
                0x48, 0x01, 0xc4, // ASM: add rsp, rax
                0x48, 0x89, 0x0c, 0x24, // ASM: mov [rsp], rcx
                0x8b, 0x04, 0x14, // ASM: mov eax, [rsp+rdx]
                0xc3, // ASM: ret
            ],
        ),
        after(
            1 << 63,
            &[
                0x48, 0x01, 0xc4, // ASM: add rsp, rax
                0x48, 0x8b, 0x04, 0x24, // ASM: mov rax, [rsp]
                0xc3, // ASM: ret
            ],
        ),
        after(
            1 << 63,
            &[
                0xff, 0xd1, // ASM: call rcx
                0x48, 0x29, 0xc4, // ASM: sub rsp, rax
                0x48, 0x8b, 0x04, 0x24, // ASM: mov rax, [rsp]
                0xc3, // ASM: ret
            ],
        ),
    ];
    for code in cases {
        let text = Section::mapped(".text", 0x1000, 0, 0x100, false, true);
        let mut bytes = vec![0xcc; 0x100];
        bytes[..code.len()].copy_from_slice(&code);
        bytes[0x80] = 0xc3; // ASM: ret
        let mut p = Program::raw(bytes, Arch::X86_64, 0, Some(0x1000), vec![text]);
        p.symbols = vec![Symbol {
            name: "__chkstk".to_owned(),
            addr: 0x1080,
            kind: SymbolKind::Local,
        }];
        let a = Analysis::compute(&p);
        let out = decompile(&p, &a, &Overlay::default(), 0x1000);
        assert!(out.is_some(), "{code:x?} does not decompile");
    }
}
