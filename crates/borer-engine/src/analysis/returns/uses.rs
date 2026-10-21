//! What the code after a call does with the float a callee may leave in
//! xmm0.

use super::*;

/// What the code after a call does with xmm0.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum FloatUse {
    /// Read before anything writes it: the caller takes a float result,
    /// at the precision the reading instruction names, when it names one
    /// ([`xmm0_read_bits`]).
    Read(Option<u8>),
    /// Handed on by the caller's `ret`, untouched: taken exactly when the
    /// caller's own float result is (the caller's entry).
    Tail(u64),
    /// Written, clobbered by a call, or lost where the scan stops.
    Dropped,
}

/// The precision a scalar float instruction reads xmm0 at, in bits.
///
/// A conversion names its source after `cvt` or `cvtt` (`cvtss2sd` reads a
/// single); any other scalar instruction names it as its suffix (`movss`,
/// `addsd`). A packed or bit instruction names none.
///
/// # Arguments
///
/// * `i` - The instruction that reads xmm0.
fn xmm0_read_bits(i: &Instruction) -> Option<u8> {
    let name = format!("{:?}", i.mnemonic()).to_ascii_lowercase();
    let name = name
        .strip_prefix('v')
        .filter(|n| n.starts_with("cvt"))
        .unwrap_or(&name);
    let lane = match name
        .strip_prefix("cvtt")
        .or_else(|| name.strip_prefix("cvt"))
    {
        Some(rest) => rest.get(..2)?,
        None => name.get(name.len().checked_sub(2)?..)?,
    };
    match lane {
        "ss" => Some(32),
        "sd" => Some(64),
        _ => None,
    }
}

/// Classifies what the code after the call at `call_va` does with xmm0.
///
/// The scan follows the return address, jumps within the caller, both
/// ways of a conditional branch, and calls to functions that hand xmm0
/// back untouched ([`preserves`]), [`SCAN_MAX`] instructions down each
/// path. A read of xmm0 on any path takes the result: xmm0 is volatile
/// across a call, so code reads it after one only for the result
/// (`test ebx, ebx; je; xorps xmm0, xmm5` negates it on one path). With no
/// read, a `ret` on some path hands it on; a write, another call or the
/// end of the scan drops it.
///
/// # Arguments
///
/// * `program` - The image.
/// * `analysis` - For the caller's blocks.
/// * `factory` - Reused instruction-info factory.
/// * `bitness` - Decoder bitness.
/// * `call_va` - Address of the call instruction.
/// * `preserving` - Per function, in order, whether it hands xmm0 back
///   untouched.
pub(super) fn float_use(
    program: &Program,
    analysis: &Analysis,
    factory: &mut InstructionInfoFactory,
    bitness: u32,
    call_va: u64,
    preserving: &[bool],
) -> FloatUse {
    let Some(caller) = analysis.function_at(call_va) else {
        return FloatUse::Dropped;
    };
    let Some(call) = decode_at(program, bitness, call_va) else {
        return FloatUse::Dropped;
    };
    let within = |va: u64| caller.blocks.iter().any(|b| b.start <= va && va < b.end);
    let preserves = |target: u64| {
        analysis
            .entry_index
            .get(&target)
            .is_some_and(|&i| preserving.get(i).copied().unwrap_or(false))
    };
    let (mut read, mut tail) = (None, false);
    let mut seen = BTreeSet::new();
    let mut paths = vec![(call.next_ip(), 0)];
    while let Some((mut va, mut walked)) = paths.pop() {
        while walked < SCAN_MAX && within(va) && seen.insert(va) {
            walked += 1;
            let Some(instr) = decode_at(program, bitness, va) else {
                break;
            };
            if reads_vector(factory, &instr, Register::ZMM0) {
                let bits = xmm0_read_bits(&instr);
                if bits.is_some() {
                    return FloatUse::Read(bits);
                }
                read = Some(bits);
                break;
            }
            if writes_xmm0(factory, &instr) {
                break;
            }
            let target = instr.near_branch_target();
            va = match instr.flow_control() {
                FlowControl::Next => instr.next_ip(),
                FlowControl::UnconditionalBranch if within(target) => target,
                FlowControl::ConditionalBranch => {
                    paths.push((target, walked));
                    instr.next_ip()
                }
                FlowControl::Call if preserves(target) => instr.next_ip(),
                FlowControl::Return => {
                    tail = true;
                    break;
                }
                FlowControl::UnconditionalBranch
                | FlowControl::IndirectBranch
                | FlowControl::Call
                | FlowControl::IndirectCall
                | FlowControl::Interrupt
                | FlowControl::Exception
                | FlowControl::XbeginXabortXend => break,
            };
        }
    }
    match (read, tail) {
        (Some(bits), _) => FloatUse::Read(bits),
        (None, true) => FloatUse::Tail(caller.entry),
        (None, false) => FloatUse::Dropped,
    }
}
