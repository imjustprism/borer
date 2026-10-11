//! Function discovery from the code alone: what a padding run, a gap and a
//! pointer are believed to say, and what they are not.
//!
//! Every fixture is a hand-assembled raw x64 image with nothing declared -
//! no symbols, no unwind entries - so each test states exactly which bytes
//! make a function and which do not.

#![expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]

use crate::raw;

use borer_engine::analysis::Analysis;
use borer_engine::program::Arch;

/// Where [`raw::image`] maps `.text`; the entry point is its first byte.
const TEXT: u64 = 0x401000;

/// The entries discovered, in address order.
///
/// # Arguments
///
/// * `code` - The bytes of `.text`.
/// * `data` - The bytes of `.rdata`.
fn entries(code: &[u8], data: &[u8]) -> Vec<u64> {
    Analysis::compute(&raw::image(Arch::X86_64, code, data))
        .functions
        .iter()
        .map(|f| f.entry)
        .collect()
}

/// `xor eax, eax; ret`: the entry function, three bytes.
const LEAF: [u8; 3] = [0x31, 0xc0, 0xc3];
/// `push rbx; xor eax, eax; pop rbx; ret`: a function with a frame.
const FRAMED: [u8; 5] = [0x53, 0x31, 0xc0, 0x5b, 0xc3];

/// A function behind a single `int3` is found.
///
/// A function that ends one byte short of its alignment gets exactly one
/// `int3`, and a sixteenth of them do; asking for two missed every one.
#[test]
fn a_function_after_one_int3_is_found() {
    let mut code = LEAF.to_vec();
    code.push(0xcc);
    code.extend_from_slice(&FRAMED);
    assert_eq!(entries(&code, &[]), vec![TEXT, TEXT + 4]);
}

/// A function behind a run of `nop` padding is found.
///
/// A linker aligns with the multi-byte `nop` forms as well as with `int3`,
/// and a syscall stub in `ntdll` is preceded by nothing else.
#[test]
fn a_function_after_nop_padding_is_found() {
    let mut code = LEAF.to_vec();
    code.extend_from_slice(&[0x0f, 0x1f, 0x44, 0x00, 0x00]); // ASM: nop dword [rax+rax]
    code.extend_from_slice(&FRAMED);
    assert_eq!(entries(&code, &[]), vec![TEXT, TEXT + 8]);
}

/// The tail of a function behind padding is not a function.
///
/// An `add rsp, 28h; ret` after an `int3` tears down a frame nothing set
/// up: it is the unreached rest of the function before the padding, and
/// reporting it as a function of its own makes a phantom.
#[test]
fn a_fragment_that_tears_down_a_frame_is_not_a_function() {
    let mut code = LEAF.to_vec();
    code.extend_from_slice(&[0xcc, 0xcc]);
    code.extend_from_slice(&[0x48, 0x83, 0xc4, 0x28, 0xc3]); // ASM: add rsp, 28h; ret
    assert_eq!(entries(&code, &[]), vec![TEXT]);
}

/// Zero bytes behind padding are data, whatever they decode to.
#[test]
fn zero_bytes_after_padding_are_not_a_function() {
    let mut code = LEAF.to_vec();
    code.extend_from_slice(&[0xcc, 0xcc]);
    code.extend_from_slice(&[0x00, 0x00, 0x00, 0x00, 0xc3]); // ASM: add [rax], al; add [rax], al; ret
    assert_eq!(entries(&code, &[]), vec![TEXT]);
}

/// A gap that opens at the alignment a function gets, with a prologue, is a function.
///
/// Nothing pads between the two: the first is exactly sixteen bytes and
/// the second begins flush against it. Its alignment and its `sub rsp` are
/// the only witnesses, and they are enough.
#[test]
fn an_aligned_gap_with_a_prologue_is_a_function() {
    let mut code = vec![
        0x48, 0x83, 0xec, 0x28, // ASM: sub rsp, 28h
        0xb8, 0x01, 0x00, 0x00, 0x00, // ASM: mov eax, 1
        0x31, 0xc9, // ASM: xor ecx, ecx
        0x48, 0x83, 0xc4, 0x28, // ASM: add rsp, 28h
        0xc3, // ASM: ret
    ];
    assert_eq!(code.len(), 16);
    code.extend_from_slice(&[
        0x48, 0x83, 0xec, 0x28, 0x31, 0xc0, 0x48, 0x83, 0xc4, 0x28, 0xc3,
    ]);
    assert_eq!(entries(&code, &[]), vec![TEXT, TEXT + 16]);
}

/// The same code off its alignment is not believed.
///
/// With no padding and no alignment there is nothing to say the bytes
/// after one function are not its unreached tail.
#[test]
fn an_unaligned_gap_is_not_a_function() {
    let mut code = vec![
        0x48, 0x83, 0xec, 0x28, // ASM: sub rsp, 28h
        0xb8, 0x01, 0x00, 0x00, 0x00, // ASM: mov eax, 1
        0x48, 0x83, 0xc4, 0x28, // ASM: add rsp, 28h
        0xc3, // ASM: ret
    ];
    assert_eq!(code.len(), 14);
    code.extend_from_slice(&[
        0x48, 0x83, 0xec, 0x28, 0x31, 0xc0, 0x48, 0x83, 0xc4, 0x28, 0xc3,
    ]);
    assert_eq!(entries(&code, &[]), vec![TEXT]);
}

/// A function a pointer names is kept even when it never returns.
///
/// A service loop is `for (;;)`, and a data pointer is a witness on its
/// own; only decoding data would disqualify it.
#[test]
fn a_pointed_at_endless_loop_is_a_function() {
    let mut code = LEAF.to_vec();
    code.resize(0x20, 0x00);
    code.extend_from_slice(&[0xeb, 0xfe]); // ASM: jmp $
    let data = (TEXT + 0x20).to_le_bytes();
    assert_eq!(entries(&code, &data), vec![TEXT, TEXT + 0x20]);
}

/// A guess rejected once is still a function when a call reaches it later.
///
/// The pointer at `.rdata` names zero bytes and is rightly refused; the
/// function behind the padding calls the same address, and a call is a
/// fact. Marking the rejected guess as walked would have lost it.
#[test]
fn a_rejected_guess_is_walked_again_when_called() {
    let mut code = LEAF.to_vec();
    code.push(0xcc);
    // ASM: push rbx; call 0x401030; pop rbx; ret   (at 0x401004)
    code.extend_from_slice(&[0x53, 0xe8, 0x26, 0x00, 0x00, 0x00, 0x5b, 0xc3]);
    code.resize(0x30, 0xcc);
    // ASM: mov eax, 1; add [rax], al; ret   (at 0x401030): the zero bytes
    // reject the pointer's guess, and the call outweighs them.
    code.extend_from_slice(&[0xb8, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0xc3]);
    let data = (TEXT + 0x30).to_le_bytes();
    let found = entries(&code, &data);
    assert!(found.contains(&(TEXT + 4)), "{found:x?}");
    assert!(
        found.contains(&(TEXT + 0x30)),
        "the called address is a function: {found:x?}"
    );
}

/// A call into bytes that are not code names no function: the entry's own
/// bytes outweigh any witness, a call included.
#[test]
fn a_call_into_bytes_that_are_not_code_is_not_a_function() {
    let mut code = LEAF.to_vec();
    code.push(0xcc);
    // ASM: push rbx; call 0x401030; pop rbx; ret   (at 0x401004)
    code.extend_from_slice(&[0x53, 0xe8, 0x26, 0x00, 0x00, 0x00, 0x5b, 0xc3]);
    code.resize(0x30, 0xcc);
    code.extend_from_slice(&[0x00, 0x00, 0xc3]); // ASM: add [rax], al; ret   (at 0x401030)
    let found = entries(&code, &[]);
    assert!(found.contains(&(TEXT + 4)), "{found:x?}");
    assert!(
        !found.contains(&(TEXT + 0x30)),
        "zero bytes are no function: {found:x?}"
    );
}

/// A switch whose bound check sits in the block before its dispatch resolves.
///
/// `cmp ecx, 3; jbe dispatch` guards the table, but the block after the
/// jump is the default case, eight instructions ending in `ret`, so the
/// dispatch is entered only by the jump. A backward chain that only steps
/// back in memory reaches the default case and never the bound; following
/// the jump into the dispatch finds it, and the four cases become blocks
/// of the function instead of code nothing reaches.
#[test]
fn a_bound_check_in_the_block_before_the_dispatch_is_found() {
    let mut code = vec![
        0x83, 0xf9, 0x03, // ASM: cmp ecx, 3            (0x401000)
        0x76, 0x09, // ASM: jbe short 0x40100e         (0x401003)
        0x31, 0xc0, // ASM: xor eax, eax               (0x401005)
        0x90, 0x90, 0x90, 0x90, 0x90, 0x90, // ASM: nop x6
        0xc3, // ASM: ret                              (0x40100d)
        0x48, 0x8d, 0x15, 0xeb, 0xff, 0xff,
        0xff, // ASM: lea rdx, [rip - 0x15] = 0x401000  (0x40100e)
        0x8b, 0x84, 0x8a, 0x00, 0x10, 0x00,
        0x00, // ASM: mov eax, [rdx + rcx*4 + 0x1000]   (0x401015)
        0x48, 0x03, 0xc2, // ASM: add rax, rdx        (0x40101c)
        0xff, 0xe0, // ASM: jmp rax                   (0x40101f)
    ];
    assert_eq!(code.len(), 0x21);
    for (k, at) in [0x30usize, 0x40, 0x50, 0x60].into_iter().enumerate() {
        code.resize(at, 0xcc);
        let mark = u8::try_from(k + 1).expect("fits");
        code.extend_from_slice(&[0xb8, mark, 0, 0, 0, 0xc3]); // ASM: mov eax, k+1; ret
    }
    // the table: each case as an offset from 0x401000
    let mut data = Vec::new();
    for at in [0x30u32, 0x40, 0x50, 0x60] {
        data.extend_from_slice(&at.to_le_bytes());
    }
    let a = Analysis::compute(&raw::image(Arch::X86_64, &code, &data));
    let targets = a
        .jump_tables
        .get(&(TEXT + 0x1f))
        .cloned()
        .unwrap_or_default();
    assert_eq!(
        targets,
        vec![TEXT + 0x30, TEXT + 0x40, TEXT + 0x50, TEXT + 0x60],
        "the table was not resolved: {:x?}",
        a.jump_tables
    );
    let f = a.function(TEXT).expect("the switch function");
    assert!(
        f.blocks.iter().any(|b| b.start == TEXT + 0x50),
        "a case is not a block of the function"
    );
}
