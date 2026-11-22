//! ARM32 code shaped to make function discovery do more than linear work.

use std::path::PathBuf;

use borer_engine::analysis::Analysis;
use borer_engine::program::Program;

use super::heap::serial;

/// Where `.text` is mapped.
const TEXT_VA: u64 = 0x8000;
/// The file offset of `.text`: past the file header and one program
/// header.
const TEXT_AT: usize = 0x60;

/// Returns a stripped 32-bit little-endian `EM_ARM` executable holding
/// `code` as `.text`, entered in Thumb at its first byte.
///
/// # Arguments
///
/// * `code` - The bytes of `.text`.
fn thumb_image(code: &[u8]) -> Vec<u8> {
    let names = b"\0.text\0.shstrtab\0";
    let names_at = TEXT_AT + code.len();
    let headers_at = (names_at + names.len()).next_multiple_of(4);
    let mut b = vec![0u8; headers_at + 3 * 40];
    let mut le = |at: usize, v: u64, n: usize| b[at..at + n].copy_from_slice(&v.to_le_bytes()[..n]);
    let wide = |v: usize| u64::try_from(v).expect("fits");
    for (at, v, n) in [
        (0, 0x0001_0101_464c_457f, 8),
        (16, 2, 2),
        (18, 40, 2),
        (20, 1, 4),
        (24, TEXT_VA | 1, 4),
        (28, 52, 4),
        (32, wide(headers_at), 4),
        (36, 0x0500_0400, 4),
        (40, 52, 2),
        (42, 32, 2),
        (44, 1, 2),
        (46, 40, 2),
        (48, 3, 2),
        (50, 2, 2),
        (52, 1, 4),
        (56, wide(TEXT_AT), 4),
        (60, TEXT_VA, 4),
        (64, TEXT_VA, 4),
        (68, wide(code.len()), 4),
        (72, wide(code.len()), 4),
        (76, 5, 4),
        (80, 4, 4),
    ] {
        le(at, v, n);
    }
    let text = [
        1,
        1,
        6,
        TEXT_VA,
        wide(TEXT_AT),
        wide(code.len()),
        0,
        0,
        2,
        0,
    ];
    let shstr = [7, 3, 0, 0, wide(names_at), wide(names.len()), 0, 0, 1, 0];
    for (k, row) in [text, shstr].iter().enumerate() {
        for (j, v) in row.iter().enumerate() {
            le(headers_at + 40 * (k + 1) + 4 * j, *v, 4);
        }
    }
    b[TEXT_AT..names_at].copy_from_slice(code);
    b[names_at..names_at + names.len()].copy_from_slice(names);
    b
}

/// A chain of a hundred thousand jumps, each to the next instruction, past
/// a called function, does not make tail-call promotion quadratic.
///
/// Every jump of the chain targets code that follows the end of other code
/// and lies past another start, so each is a candidate tail call. Weighing
/// one rebuilt the walk's predecessors and followed everything the target
/// reaches; over every target of the chain that was some ten billion steps
/// and the load hung. The candidates per round are capped and their work
/// is charged to the discovery's fuel, so the analysis returns, finding no
/// more functions than the rounds can promote.
#[test]
fn a_chain_of_jumps_past_a_start_stays_bounded() {
    let _serial = serial();
    /// Jumps in the chain.
    const JUMPS: usize = 1 << 17;
    let mut halves: Vec<u16> = vec![
        0xf000, 0xf801, // ASM: bl 0x6
        0xe000, // ASM: b 0x8
        0x4770, // ASM: bx lr
    ];
    halves.extend(std::iter::repeat_n(0xe7ff, JUMPS));
    halves.push(0x4770);
    let code: Vec<u8> = halves.iter().flat_map(|h| h.to_le_bytes()).collect();
    let p = Program::from_bytes(PathBuf::from("chain.elf"), thumb_image(&code)).expect("parses");
    let a = Analysis::compute(&p);
    assert!(a.function(TEXT_VA).is_some(), "the entry is a function");
    assert!(
        a.functions.len() <= 2 + 4 * 1024,
        "{} functions",
        a.functions.len()
    );
}
