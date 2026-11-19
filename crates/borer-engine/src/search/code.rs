//! The instruction tier of a value search: the constants the operands of
//! the discovered functions' instructions state ([`crate::isa::Constant`]).
//!
//! The constants are decoded once per analysis, every distinct block of
//! the discovered functions in address order, and kept in the derived
//! store ([`crate::analysis::Derived`]); a value clause then reads them in
//! groups of [`CONSTANTS_PER_CHUNK`] that count as chunks of the search,
//! each constant tried against every value clause inside the scope the
//! clause keeps to.

use std::sync::Arc;

use super::form::{Found, Held, Matched, Ranges, Run, Sink, number, over};
use super::spec::{Disp, Find, Value};
use crate::analysis::Analysis;
use crate::isa::{Constant, Part};
use crate::num::saturating_usize;
use crate::program::Program;

/// Constants one chunk of the instruction tier tries.
const CONSTANTS_PER_CHUNK: usize = 1 << 16;

/// The constants a spec's value clauses read: every constant of the
/// discovered functions, at its instruction's address, in address order.
#[derive(Debug, Default)]
pub(super) struct Code {
    /// The constants, shared with the derived store; empty when no clause
    /// seeks a value.
    constants: Arc<Vec<(u64, Constant)>>,
}

impl Code {
    /// Returns the chunks reading the constants takes.
    pub(super) fn chunks(&self) -> usize {
        self.constants.len().div_ceil(CONSTANTS_PER_CHUNK)
    }
}

/// Returns the constants a spec's value clauses read: none when no clause
/// seeks a value, else every constant of the discovered functions.
///
/// # Arguments
///
/// * `p` - The program.
/// * `a` - The analysis.
/// * `finds` - The spec's finds.
pub(super) fn plan(p: &Program, a: &Analysis, finds: &[(&Find, Option<&Ranges>)]) -> Code {
    if !finds.iter().any(|(f, _)| matches!(f, Find::Value(_))) {
        return Code::default();
    }
    Code {
        constants: constants(p, a),
    }
}

/// Returns every constant the instructions of the discovered functions
/// state, each instruction address decoded once, in address order.
///
/// Built once per analysis and memoized ([`crate::analysis::Derived`]); a
/// build the request's cancel flag cuts short stops between blocks and is
/// not kept. It holds 24 bytes per constant (an immediate or a
/// displacement; most instructions state at most one), kept for the
/// analysis's life.
///
/// # Arguments
///
/// * `p` - The program.
/// * `a` - The analysis.
fn constants(p: &Program, a: &Analysis) -> Arc<Vec<(u64, Constant)>> {
    a.derived.get_or_build("code_constants", (), || {
        let mut blocks: Vec<(u64, u64)> = a
            .functions
            .iter()
            .flat_map(|f| f.blocks.iter().map(|b| (b.start, b.end)))
            .collect();
        blocks.sort_unstable();
        blocks.dedup();
        let mut out = Vec::new();
        let Some(isa) = p.arch.isa() else {
            return out;
        };
        let live = blocks
            .iter()
            .take_while(|_| !crate::cancel::Cancel::raised());
        let mut next = std::collections::BTreeMap::new();
        for &(start, end) in live {
            next = next.split_off(&start);
            let mut from = start;
            while from < end {
                if let Some(&after) = next.get(&from) {
                    from = after;
                    continue;
                }
                let stop = next
                    .range(from.saturating_add(1)..end)
                    .next()
                    .map_or(end, |(&at, _)| at);
                let len = saturating_usize(end.saturating_sub(from));
                let Some(bytes) = p.read_va_upto(from, len) else {
                    break;
                };
                let mut reached = from;
                crate::disasm::walk(p, bytes, from, isa, (stop, len), |at, n, d| {
                    reached = at.saturating_add(crate::num::from_usize(n).max(1));
                    next.insert(at, reached);
                    d.constants(|c| out.push((at, c)));
                });
                if reached <= from {
                    break;
                }
                from = reached;
            }
        }
        out.sort_unstable_by_key(|&(at, c)| (at, c));
        out
    })
}

/// Tries each constant against every value clause inside its scope.
///
/// # Arguments
///
/// * `p` - The program, for each hit's file offset.
/// * `code` - The constants ([`plan`]).
/// * `finds` - The spec's finds, each with the scope it keeps to.
/// * `run` - The search running.
///
/// # Returns
///
/// One set of hits per value clause, in the order of the finds.
///
/// # Errors
///
/// When the search stops, or a clause holds more than the hits a search
/// holds.
pub(super) fn walk(
    p: &Program,
    code: &Code,
    finds: &[(&Find, Option<&Ranges>)],
    run: &mut Run<'_>,
) -> Result<Vec<Held>, String> {
    let values: Vec<(&Value, Option<&Ranges>)> = finds
        .iter()
        .filter_map(|&(f, clip)| match f {
            Find::Value(v) => Some((v, clip)),
            Find::Bytes(_) | Find::Text(_) => None,
        })
        .collect();
    let mut held: Vec<Held> = values.iter().map(|_| Held::default()).collect();
    for group in code.constants.chunks(CONSTANTS_PER_CHUNK) {
        run.chunk(|| {
            for &(at, c) in group {
                for ((v, clip), sink) in values.iter().zip(held.iter_mut()) {
                    let operand = c.operand;
                    let matched = match c.part {
                        Part::Immediate => Matched::Immediate { operand },
                        Part::Shifted => Matched::Shifted { operand },
                        Part::Displacement if v.disp == Disp::Searched => {
                            Matched::Displacement { operand }
                        }
                        Part::Address if v.disp == Disp::Searched => Matched::Address { operand },
                        Part::Displacement | Part::Address => continue,
                    };
                    let n = number(c.value, u32::from(c.bits), v.sign);
                    if (v.lo..=v.hi).contains(&n) && clip.is_none_or(|r| r.holds(at)) {
                        sink.push(Found {
                            va: Some(at),
                            off: p.va_to_offset(at),
                            matched,
                        });
                    }
                }
            }
        })?;
        if held.iter().any(Sink::full) {
            return Err(over());
        }
    }
    Ok(held)
}
