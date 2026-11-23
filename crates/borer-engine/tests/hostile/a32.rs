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

/// Seconds an analysis here may take before the test fails; a fixed one
/// takes a few, the quadratic ones it stands for took hours.
const BOUND_SECS: u64 = 120;

/// Returns a stripped 32-bit little-endian `EM_ARM` executable holding
/// `code` as `.text`, entered in Thumb at byte `entry` of it.
///
/// # Arguments
///
/// * `code` - The bytes of `.text`.
/// * `entry` - The entry's offset into `code`.
fn thumb_image(code: &[u8], entry: usize) -> Vec<u8> {
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
        (24, (TEXT_VA + wide(entry)) | 1, 4),
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
    let (entry, count) = analyze_bounded("chain.elf", &halves, 0);
    assert!(entry, "the entry is a function");
    assert!(count <= 2 + 4 * 1024, "{count} functions");
}

/// Analyzes a Thumb image on a thread of its own and waits at most
/// [`BOUND_SECS`] for it, so that a quadratic discovery fails the test
/// instead of hanging it.
///
/// # Arguments
///
/// * `name` - The file name.
/// * `halves` - The halfwords of `.text`.
/// * `entry` - The entry's offset into `.text`, in bytes.
///
/// # Returns
///
/// Whether the entry is a function, and how many functions were found.
///
/// # Panics
///
/// When the analysis takes longer than [`BOUND_SECS`].
fn analyze_bounded(name: &str, halves: &[u16], entry: usize) -> (bool, usize) {
    let code: Vec<u8> = halves.iter().flat_map(|h| h.to_le_bytes()).collect();
    let p = Program::from_bytes(PathBuf::from(name), thumb_image(&code, entry)).expect("parses");
    let at = TEXT_VA + u64::try_from(entry).expect("fits");
    let (send, done) = std::sync::mpsc::channel();
    std::thread::spawn(move || {
        let a = Analysis::compute(&p);
        send.send((a.function(at).is_some(), a.functions.len()))
            .expect("the test waits");
    });
    done.recv_timeout(std::time::Duration::from_secs(BOUND_SECS))
        .expect("the analysis ends within the bound")
}

/// Returns the two halfwords of a Thumb `b.w` (`link` false) or `bl`
/// (`link` true) at `from` to `to`, both offsets into `.text`.
///
/// # Arguments
///
/// * `from` - The instruction's offset.
/// * `to` - The target's offset.
/// * `link` - Whether it is a `bl`.
fn branch(from: usize, to: usize, link: bool) -> [u16; 2] {
    let wide = |v: usize| i64::try_from(v).expect("fits");
    let off = wide(to) - wide(from) - 4;
    let bit = |n: u32| u16::try_from((off >> n) & 1).expect("one bit");
    let s = bit(24);
    let j1 = (bit(23) ^ s) ^ 1;
    let j2 = (bit(22) ^ s) ^ 1;
    let imm10 = u16::try_from((off >> 12) & 0x3ff).expect("ten bits");
    let imm11 = u16::try_from((off >> 1) & 0x7ff).expect("eleven bits");
    let base = if link { 0xd000 } else { 0x9000 };
    [
        0xf000 | (s << 10) | imm10,
        base | (j1 << 13) | (j2 << 11) | imm11,
    ]
}

/// A walk dense in jump tables does not look each table up by scanning
/// them all.
///
/// Eighty-seven thousand bounded `tbb` dispatches fill one walk to its cap
/// behind a jump that a `pop` gives back the frame for; reading the
/// walk's stack depth and edges scanned every table at every instruction,
/// some twenty billion steps.
#[test]
fn a_walk_dense_in_jump_tables_stays_bounded() {
    let _serial = serial();
    /// Dispatch blocks behind the jump.
    const BLOCKS: usize = 87_000;
    let mut halves: Vec<u16> = vec![0x4770]; // ASM: bx lr
    for _ in 0..BLOCKS {
        halves.extend([
            0x2801, // ASM: cmp r0, #1
            0xd802, // ASM: bhi.n (the next block)
            0xe8df, 0xf000, // ASM: tbb [pc, r0]
            0x0101, // ASM: .byte 1, 1
        ]);
    }
    halves.push(0x4770);
    let entry = 2 * halves.len();
    halves.extend([
        0xb410, // ASM: push {r4}
        0xbc10, // ASM: pop {r4}
    ]);
    halves.extend(branch(entry + 4, 2, false));
    let (found, _) = analyze_bounded("tables.elf", &halves, entry);
    assert!(found, "the entry is a function");
}
