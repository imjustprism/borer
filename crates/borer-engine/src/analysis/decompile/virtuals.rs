//! The virtual calls a decompilation resolved, read from its memo.

use crate::analysis::{Analysis, Overlay, decompiled_cached};
use crate::program::Program;

/// One virtual call the lifter resolved through the receiver's vtable.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct VirtualCall {
    /// The slot function's entry.
    pub entry: u64,
    /// The address of the call instruction.
    pub site: u64,
    /// The slot's index in the vtable.
    pub slot: usize,
}

/// Returns the virtual calls a function makes that resolve to a slot
/// function.
///
/// A call through the vtable of `this`, of a class-typed parameter or of a
/// typed call result resolves to a slot function (the lifter's
/// virtual-target rule); these are the calls the cross-reference index
/// cannot see. Finding them decompiles the function, once: the
/// decompilation is memoized.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Discovery results the function comes from.
/// * `overlay` - User names and comments.
/// * `entry` - The function's entry address.
///
/// # Returns
///
/// The calls by slot function, then site, then slot; empty when the
/// function does not decompile or makes no resolvable virtual call.
pub fn virtual_calls(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    entry: u64,
) -> Vec<VirtualCall> {
    decompiled_cached(program, analysis, overlay, overlay.fingerprint(), entry)
        .as_ref()
        .as_ref()
        .map_or_else(Vec::new, |d| d.virtual_calls.clone())
}

/// Returns the entries a function's virtual calls resolve to
/// ([`virtual_calls`]).
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Discovery results the function comes from.
/// * `overlay` - User names and comments.
/// * `entry` - The function's entry address.
///
/// # Returns
///
/// The resolved entries, sorted and deduplicated; empty when the function
/// does not decompile or makes no resolvable virtual call.
pub fn virtual_callees(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    entry: u64,
) -> Vec<u64> {
    entries(&virtual_calls(program, analysis, overlay, entry))
}

/// Returns the slot functions some virtual calls reach, sorted and
/// deduplicated.
///
/// # Arguments
///
/// * `calls` - The calls, in any order.
fn entries(calls: &[VirtualCall]) -> Vec<u64> {
    let mut out: Vec<u64> = calls.iter().map(|c| c.entry).collect();
    out.sort_unstable();
    out.dedup();
    out
}

#[cfg(test)]
mod tests {
    use super::{VirtualCall, entries};

    /// Two calls of one slot function are one callee, whatever order the
    /// calls come in.
    ///
    /// # Panics
    ///
    /// When a slot function is listed twice or out of order.
    #[test]
    fn two_calls_of_one_slot_function_are_one_callee() {
        let call = |entry, site| VirtualCall {
            entry,
            site,
            slot: 1,
        };
        let calls = [call(0x20, 0x10), call(0x10, 0x18), call(0x20, 0x30)];
        assert_eq!(entries(&calls), [0x10, 0x20]);
    }
}
