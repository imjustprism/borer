//! Code whose offsets reach the far end of the 64-bit range: a stack
//! pointer moved there, a thread-local slot stated there. Each case
//! decompiles.

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
        assert!(decompiles(&code, "__chkstk", 0x1080), "{code:x?}");
    }
}

/// A thread-local slot a constructor's code states past the top of the
/// address space decompiles, where naming the slot's global added its
/// offset to the TLS base unchecked.
///
/// `Foo::Foo` stores through its TLS block at `-8`: the class scan ignores
/// offsets above `u32::MAX`, and even when a caller inserts that slot
/// directly, naming its global keeps the address as it is rather than
/// overflowing the TLS base.
#[test]
fn a_thread_local_slot_past_the_top_decompiles() {
    let code = [
        0x65, 0x48, 0x8b, 0x04, 0x25, 0x58, 0x00, 0x00, 0x00, // ASM: mov rax, gs:[0x58]
        0x48, 0x8b, 0x04, 0xd0, // ASM: mov rax, [rax+rdx*8]
        0x48, 0x89, 0x48, 0xf8, // ASM: mov [rax-8], rcx
        0xc3, // ASM: ret
    ];
    let text = Section::mapped(".text", 0x1000, 0, 0x100, false, true);
    let mut bytes = vec![0xcc; 0x100];
    bytes[..code.len()].copy_from_slice(&code);
    let mut p = Program::raw(bytes, Arch::X86_64, 0, Some(0x1000), vec![text]);
    p.symbols = vec![Symbol {
        name: "Foo::Foo".to_owned(),
        addr: 0x1000,
        kind: SymbolKind::Local,
    }];
    let mut a = Analysis::compute(&p);
    assert!(a.classes.tls_slots.is_empty());
    a.classes.tls_slots.insert(u64::MAX - 7, "Foo".to_owned());
    assert!(decompile(&p, &a, &Overlay::default(), 0x1000).is_some());
}

/// Decompiles 64-bit `code` at 0x1000, a `ret` at 0x1080, with one symbol.
///
/// # Arguments
///
/// * `code` - The function's bytes, at most 0x80 of them.
/// * `name` - The symbol's name.
/// * `addr` - Where it names.
///
/// # Returns
///
/// Whether the function decompiled.
fn decompiles(code: &[u8], name: &str, addr: u64) -> bool {
    let text = Section::mapped(".text", 0x1000, 0, 0x100, false, true);
    let mut bytes = vec![0xcc; 0x100];
    bytes[..code.len()].copy_from_slice(code);
    bytes[0x80] = 0xc3; // ASM: ret
    let mut p = Program::raw(bytes, Arch::X86_64, 0, Some(0x1000), vec![text]);
    p.symbols = vec![Symbol {
        name: name.to_owned(),
        addr,
        kind: SymbolKind::Local,
    }];
    let a = Analysis::compute(&p);
    decompile(&p, &a, &Overlay::default(), 0x1000).is_some()
}
