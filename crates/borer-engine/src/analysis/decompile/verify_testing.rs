//! What the unit tests of the lift check's drivers share: a raw image of a
//! routine, and one block checked from several seeds, as lifted and with a
//! lift the test gets wrong on purpose.

use super::verify::{Bench, Ran, Verified};
use crate::emulate::Stop;
use crate::program::{Arch, Program, Section};

/// Where a test's routine is placed and entered.
pub(super) const AT: u64 = 0x1000;

/// Builds a raw image whose only section, at [`AT`], holds `words`.
///
/// # Arguments
///
/// * `arch` - The instruction set.
/// * `words` - The code, in order.
#[expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]
pub(super) fn image(arch: Arch, words: &[u32]) -> Program {
    let code: Vec<u8> = words.iter().flat_map(|w| w.to_le_bytes()).collect();
    let len = u64::try_from(code.len()).expect("a small image");
    let text = Section::mapped(".text", AT, 0, len, false, true);
    Program::raw(code, arch, 0, Some(AT), vec![text])
}

/// Checks one block from seeds 1 to 8, as lifted, which must agree, and
/// with the lift `spoil` gets wrong.
///
/// # Arguments
///
/// * `run` - Runs the block both ways from a seed.
/// * `compare` - Compares every fact of a run.
/// * `spoil` - Makes the lift wrong.
///
/// # Returns
///
/// How many seeds the machine took the block's branch from, when it ends in
/// one, and how many the wrong lift disagreed from.
#[expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]
pub(super) fn tried<'p, M: Bench + 'p, R>(
    mut run: impl FnMut(u64, &mut Verified) -> Ran<'p, M, R>,
    compare: impl Fn(Ran<'p, M, R>, &mut Verified),
    spoil: impl Fn(&mut Ran<'p, M, R>),
) -> (usize, usize) {
    let (mut taken, mut caught) = (0, 0);
    for seed in 1..=8 {
        let mut out = Verified::default();
        let ran = run(seed, &mut out);
        if let Some((jcc, _)) = &ran.branch {
            let mut emu = ran.emu.clone();
            emu.set_budget(1);
            emu.stop_at(Some(jcc.target));
            taken += usize::from(emu.run(jcc.ip).stop == Stop::Stopped(jcc.target));
        }
        compare(ran, &mut out);
        assert!(
            out.mismatches.is_empty(),
            "seed {seed}: {:?}",
            out.mismatches
        );
        let mut wrong = Verified::default();
        let mut ran = run(seed, &mut wrong);
        spoil(&mut ran);
        compare(ran, &mut wrong);
        caught += usize::from(!wrong.mismatches.is_empty());
    }
    (taken, caught)
}
