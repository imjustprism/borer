//! Tests of discovery's instruction budget across walker lanes: what is
//! found when the budget runs out inside a wave may not depend on how
//! many lanes walk it.

use super::discover;
use crate::program::{Arch, Program, Section};

/// Builds an entry that calls `leaves` leaves, each one `jmp` into a
/// shared run of `nops` `nop`s ending in a `ret`, so every leaf's walk
/// decodes the run again and costs `nops + 2` instructions.
///
/// The entry sits at `0x1000`, the leaves right after its `ret`, five
/// bytes each, and the run after the last leaf.
///
/// # Arguments
///
/// * `leaves` - How many leaves the entry calls.
/// * `nops` - How long the shared run is.
///
/// # Panics
///
/// When the image is too large to map.
fn sled(leaves: u32, nops: usize) -> Program {
    let (first, run) = (0x1000 + 5 * leaves + 1, 0x1000 + 10 * leaves + 1);
    let to = |opcode: u8, at: u32, target: u32| {
        let rel = target.wrapping_sub(at + 5).to_le_bytes();
        [opcode, rel[0], rel[1], rel[2], rel[3]]
    };
    let calls = (0..leaves).flat_map(|i| to(0xe8, 0x1000 + 5 * i, first + 5 * i)); // ASM: call leaf
    let jumps = (0..leaves).flat_map(|i| to(0xe9, first + 5 * i, run)); // ASM: jmp run
    let mut bytes = vec![0u8; 0x1000];
    bytes.extend(calls.chain([0xc3]).chain(jumps)); // ASM: ret after the calls
    bytes.resize(bytes.len() + nops, 0x90); // ASM: nop
    bytes.push(0xc3); // ASM: ret
    let size = u64::try_from(bytes.len() - 0x1000).expect("a small image");
    let text = Section::mapped(".text", 0x1000, 0x1000, size, false, true);
    Program::raw(bytes, Arch::X86_64, 0, Some(0x1000), vec![text])
}

/// Discovery finds the same functions, cut at the same instruction, on one
/// lane and on many, when the budget runs out inside a wave.
///
/// The budget is two million instructions. With 128 leaves of 40,002 it
/// runs out in the wave's first batch; with 300 of 30,002 in its second,
/// which the lanes walk while the first is committed. One walker takes the
/// leaves in order from the one budget, so the last leaf it reaches is cut
/// short and the leaves after it are never walked. Every lane once walked
/// its share of a batch from the whole budget left, so eight lanes found
/// eight leaves cut short and more whole ones than one walker did.
///
/// # Panics
///
/// When the budget does not run out, or a lane count finds other
/// functions than one walker.
#[test]
fn spent_fuel_cuts_the_same_walks_at_any_lane_count() {
    for (leaves, nops) in [(128, 40_000), (300, 30_000)] {
        let p = sled(leaves, nops);
        let found = |lanes: usize| {
            let a = discover(&p, 64, lanes);
            let sizes: Vec<(u64, usize)> = a
                .functions
                .iter()
                .map(|f| (f.entry, f.instr_count))
                .collect();
            let all = format!("{:?}", (&a.functions, &a.xrefs));
            (a.incomplete, sizes, all)
        };
        let one = found(1);
        assert!(one.0, "{leaves} leaves fit the budget");
        for lanes in [2, 8, 64] {
            let many = found(lanes);
            assert_eq!((many.0, &many.1), (one.0, &one.1), "{lanes} lanes");
            assert!(many.2 == one.2, "{leaves} leaves on {lanes} lanes");
        }
    }
}
