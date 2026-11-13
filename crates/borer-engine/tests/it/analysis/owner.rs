//! Basic-block address ownership (`Analysis::function_at` and `Analysis::block_at`).

use super::*;
use borer_engine::analysis::render::{instruction_at_or_before, listing_caveat};

/// Assembles a raw x86-64 program whose `.text` starts at `0x1000`.
///
/// # Arguments
///
/// * `size` - Byte length of `.text`, pre-filled with `0xcc`.
/// * `entry` - Entry virtual address.
/// * `pieces` - `(va, bytes)` fragments copied into `.text`.
/// * `locals` - `(name, addr)` local function symbols.
///
/// # Returns
///
/// The assembled [`Program`].
fn raw_code(size: usize, entry: u64, pieces: &[(u64, &[u8])], locals: &[(&str, u64)]) -> Program {
    let mut bytes = vec![0xccu8; size];
    for &(va, piece) in pieces {
        let at = borer_engine::num::saturating_usize(va - 0x1000);
        bytes[at..at + piece.len()].copy_from_slice(piece);
    }
    let mut p = Program::raw(
        bytes,
        Arch::X86_64,
        0,
        Some(entry),
        vec![Section::mapped(
            ".text",
            0x1000,
            0,
            from_usize(size),
            false,
            true,
        )],
    );
    p.symbols = locals
        .iter()
        .map(|&(name, addr)| Symbol {
            name: name.to_owned(),
            addr,
            kind: SymbolKind::Local,
        })
        .collect();
    p
}

/// Keeps a tail block past a nested function with the outer function.
///
/// Function `0x1000` calls `0x1100` and jumps over it to `0x1150`; `0x1100`
/// owns its own `ret`, `0x1000` owns `0x1150..0x1156` and the pre-`0x1100`
/// span, and the `0xcc` gap between `0x1101` and `0x1150` stays `None`.
#[test]
fn nested_function_keeps_outer_block_past_inner_entry() {
    let p = raw_code(
        0x1000,
        0x1000,
        &[
            (
                0x1000,
                &[
                    0xe8, 0xfb, 0x00, 0x00, 0x00, // ASM: call 0x1100
                    0xe9, 0x46, 0x01, 0x00, 0x00, // ASM: jmp 0x1150
                ],
            ),
            (
                0x1100,
                &[
                    0xc3, // ASM: ret
                ],
            ),
            (
                0x1150,
                &[
                    0xb8, 0x01, 0x00, 0x00, 0x00, // ASM: mov eax, 1
                    0xc3, // ASM: ret
                ],
            ),
        ],
        &[],
    );
    let a = Analysis::compute(&p);
    let outer = a.function(0x1000).expect("outer function");
    assert!(
        outer
            .blocks
            .iter()
            .any(|b| (b.start, b.end) == (0x1150, 0x1156))
    );
    assert_eq!(a.function_at(0x1150).map(|f| f.entry), Some(0x1000));
    assert_eq!(a.function_at(0x1155).map(|f| f.entry), Some(0x1000));
    assert_eq!(a.function_at(0x1100).map(|f| f.entry), Some(0x1100));
    assert_eq!(
        a.block_at(0x1152).map(|(f, b)| (f.entry, b.start)),
        Some((0x1000, 0x1150))
    );
    assert_eq!(a.function_at(0x1050).map(|f| f.entry), Some(0x1000));
    assert!(a.function_at(0x1120).is_none());
}

/// Attributes a cold block below its entry to its function and clears the listing caveat.
///
/// Function `0x2000` branches backward to `0x1800`, above function `0x1700`;
/// `0x1802` resolves to `0x2000`, snaps to instruction boundary `0x1800`, and
/// carries no `outside every discovered function` caveat, while the `0xcc`
/// gaps on either side stay `None`.
#[test]
fn cold_block_below_entry_resolves_to_owner_without_caveat() {
    let p = raw_code(
        0x2000,
        0x2000,
        &[
            (
                0x1700,
                &[
                    0x31, 0xc0, // ASM: xor eax, eax
                    0xc3, // ASM: ret
                ],
            ),
            (
                0x1800,
                &[
                    0xb8, 0xff, 0xff, 0xff, 0xff, // ASM: mov eax, -1
                    0xc3, // ASM: ret
                ],
            ),
            (
                0x2000,
                &[
                    0x85, 0xff, // ASM: test edi, edi
                    0x0f, 0x84, 0xf8, 0xf7, 0xff, 0xff, // ASM: je 0x1800
                    0xb8, 0x01, 0x00, 0x00, 0x00, // ASM: mov eax, 1
                    0xc3, // ASM: ret
                ],
            ),
        ],
        &[("d", 0x1700)],
    );
    let a = Analysis::compute(&p);
    let c = a.function(0x2000).expect("function with cold block");
    assert!(
        c.blocks
            .iter()
            .any(|b| (b.start, b.end) == (0x1800, 0x1806))
    );
    assert_eq!(a.function_at(0x1700).map(|f| f.entry), Some(0x1700));
    assert_eq!(a.function_at(0x1802).map(|f| f.entry), Some(0x2000));
    assert_eq!(instruction_at_or_before(&p, &a, 0x1802), Some(0x1800));
    assert_eq!(listing_caveat(&p, &a, 0x1802), "");
    assert!(a.function_at(0x1750).is_none());
    assert!(a.function_at(0x1900).is_none());
    assert!(listing_caveat(&p, &a, 0x1900).contains("outside every discovered function"));
}

/// Breaks shared and nested block ties by highest `entry <= va`, else lowest `entry`.
///
/// Functions `0x1200`, `0x1400` and `0x1800` all branch to `0x1100` (above all
/// of them, so `0x1200` wins), while `0x1200` and `0x1800` share `0x1500..0x1506`
/// and `0x1400` jumps into the inner `ret` at `0x1504..0x1505` (`0x1400` wins at
/// `0x1504`, and `0x1200` owns both `0x1500` before it and `0x1505` past it).
#[test]
fn shared_blocks_pick_highest_entry_at_or_below_else_lowest_entry() {
    let p = raw_code(
        0x1000,
        0x1200,
        &[
            (
                0x1100,
                &[
                    0xb8, 0xff, 0xff, 0xff, 0xff, // ASM: mov eax, -1
                    0xc3, // ASM: ret
                ],
            ),
            (
                0x1200,
                &[
                    0x85, 0xff, // ASM: test edi, edi
                    0x0f, 0x84, 0xf8, 0xfe, 0xff, 0xff, // ASM: je 0x1100
                    0xe9, 0xf3, 0x02, 0x00, 0x00, // ASM: jmp 0x1500
                ],
            ),
            (
                0x1400,
                &[
                    0x85, 0xf6, // ASM: test esi, esi
                    0x0f, 0x84, 0xf8, 0xfc, 0xff, 0xff, // ASM: je 0x1100
                    0xe9, 0xf7, 0x00, 0x00, 0x00, // ASM: jmp 0x1504
                ],
            ),
            (
                0x1500,
                &[
                    0xb8, 0x01, 0x00, 0x00, 0xc3, // ASM: mov eax, 0xc3000001 (0x1504 is ret)
                    0xc3, // ASM: ret
                ],
            ),
            (
                0x1800,
                &[
                    0x85, 0xd2, // ASM: test edx, edx
                    0x0f, 0x84, 0xf8, 0xf8, 0xff, 0xff, // ASM: je 0x1100
                    0xe9, 0xf3, 0xfc, 0xff, 0xff, // ASM: jmp 0x1500
                ],
            ),
        ],
        &[("mid", 0x1400), ("high", 0x1800)],
    );
    let a = Analysis::compute(&p);
    assert_eq!(a.function_at(0x1102).map(|f| f.entry), Some(0x1200));
    assert_eq!(a.function_at(0x1500).map(|f| f.entry), Some(0x1200));
    assert_eq!(
        a.block_at(0x1504).map(|(f, b)| (f.entry, b.start, b.end)),
        Some((0x1400, 0x1504, 0x1505))
    );
    assert_eq!(a.function_at(0x1504).map(|f| f.entry), Some(0x1400));
    assert_eq!(
        a.block_at(0x1505).map(|(f, b)| (f.entry, b.start, b.end)),
        Some((0x1200, 0x1500, 0x1506))
    );
    assert_eq!(a.function_at(0x1505).map(|f| f.entry), Some(0x1200));
}

/// Keeps an ARM32 backward-jumped body recoverable at its block start through `entry_or_gap`.
///
/// Thunk `0x100c` jumps backward into `0x1000..0x1008`; `function_at` owns the
/// whole block under `0x100c`, an interior address `0x1004` stays with `0x100c`,
/// and asking `entry_or_gap` at `0x1000` still recovers `0x1000` as its own function.
#[test]
fn arm32_backward_jumped_body_stays_recoverable_at_its_start() {
    let words: [u32; 5] = [
        0xe280_0001, // ASM: add r0, r0, #1
        0xe12f_ff1e, // ASM: bx lr
        0xe1a0_0000, // ASM: mov r0, r0
        0xe3a0_1007, // ASM: mov r1, #7
        0xeaff_fffa, // ASM: b 0x1000
    ];
    let bytes: Vec<u8> = words.iter().flat_map(|w| w.to_le_bytes()).collect();
    let p = Program::raw(
        bytes,
        Arch::Arm,
        0,
        Some(0x100c),
        vec![Section::mapped(
            ".text",
            0x1000,
            0,
            from_usize(words.len() * 4),
            false,
            true,
        )],
    );
    let mut a = Analysis::compute(&p);
    assert_eq!(a.function_at(0x1000).map(|f| f.entry), Some(0x100c));
    assert_eq!(
        borer_engine::analysis::entry_or_gap(&p, &mut a, 0x1004),
        Ok(0x100c)
    );
    assert!(a.function(0x1000).is_none());
    assert_eq!(
        borer_engine::analysis::entry_or_gap(&p, &mut a, 0x1000),
        Ok(0x1000)
    );
    assert_eq!(a.function_at(0x1000).map(|f| f.entry), Some(0x1000));
}
