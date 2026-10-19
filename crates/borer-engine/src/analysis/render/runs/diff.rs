//! Runs of one function in two builds side by side, and where their
//! traces first part.

use super::spec::parse_run;
use super::{Arg, Shared, buffer_base, buffer_writes, lay_out, run_machine, shared_for};
use crate::analysis::decompile::signature::Signature;
use crate::analysis::render::*;
use crate::text::one_line;

/// One input's traced run, what a diff reports from.
pub(super) struct DiffRun {
    /// How it ended, in words.
    pub(super) stop: String,
    /// Steps taken.
    pub(super) steps: usize,
    /// What it returned, `None` when it did not.
    pub(super) value: Option<u64>,
    /// The traced instructions, in the order they ran.
    pub(super) trace: Vec<String>,
    /// Each serviced call as `api(args) -> ret`, in order.
    pub(super) call_lines: Vec<String>,
    /// What each changed buffer argument holds after, as
    /// [`buffer_writes`] leaves it.
    pub(super) writes: Vec<(usize, Vec<u8>, usize)>,
}

/// Runs one input for [`diff_tsv`], its whole path traced.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `shared` - The text and convention [`shared_for`] built.
/// * `entry` - The function.
/// * `input` - The arguments.
/// * `budget` - Steps, never past what one trace holds.
///
/// # Returns
///
/// The traced run, or `None` when the architecture is not emulated.
fn diff_one(
    p: &Program,
    shared: &Shared<'_>,
    entry: u64,
    input: &[Arg],
    budget: usize,
) -> Option<DiffRun> {
    let buffers = input.iter().filter(|a| a.is_buffer()).count();
    let layout = lay_out(buffer_base(p, buffers.max(input.len())), input);
    let ret = shared.sig.as_ref().ok().and_then(Signature::return_kind);
    let m = run_machine(
        p,
        entry,
        shared.pass.as_ref(),
        ret.map(|(_, bits)| bits),
        input,
        &layout,
        budget,
        true,
    )?;
    let writes = buffer_writes(input, &m.buffers);
    Some(DiffRun {
        stop: m.stop.to_string(),
        steps: m.steps,
        value: m.value,
        writes,
        call_lines: m.call_lines,
        trace: m.trace,
    })
}

/// The address a trace line ran at, when the line carries one.
///
/// # Arguments
///
/// * `line` - One line of [`crate::emulate::Emulator::trace`], which
///   begins with where the instruction was.
fn trace_at(line: &str) -> Option<u64> {
    let head = line.split_whitespace().next()?;
    code_addr(head)
}

/// Reads one instruction operand as the address it names, in either
/// decoder's spelling: `0x1014` or `1014h`.
///
/// # Arguments
///
/// * `word` - The operand as the trace printed it.
fn code_addr(word: &str) -> Option<u64> {
    word.strip_prefix("0x")
        .or_else(|| word.strip_suffix('h'))
        .and_then(|h| u64::from_str_radix(h, 16).ok())
}

/// The functions a trace called, from step `from` on, named once each, in
/// order: the transforms a run made of its input.
///
/// # Arguments
///
/// * `a` - The analysis, for the function each call lands in.
/// * `o` - User names.
/// * `lines` - The traced instructions.
/// * `from` - The first step to read.
///
/// # Returns
///
/// At most 12 callee names; an indirect call whose trace shows no target
/// is skipped.
fn trace_calls(a: &Analysis, o: &Overlay, lines: &[String], from: usize) -> Vec<String> {
    /// Most callees a diff names per side.
    const CALLS_MAX: usize = 12;
    let mut out: Vec<String> = Vec::new();
    for line in lines.iter().skip(from) {
        let mut parts = line.split_whitespace();
        let (Some(_), Some(mn), target) = (parts.next(), parts.next(), parts.next()) else {
            continue;
        };
        if !matches!(mn, "call" | "bl") {
            continue;
        }
        let Some(at) = target.and_then(code_addr) else {
            continue;
        };
        let Some(f) = a.function_at(at) else { continue };
        let name = short_name(a, o, f.entry);
        if !out.contains(&name) {
            out.push(name);
            if out.len() >= CALLS_MAX {
                break;
            }
        }
    }
    out
}

/// Bytes as two hex digits each, capped with an ellipsis.
///
/// # Arguments
///
/// * `bytes` - What a run left in a buffer.
fn short_hex(bytes: &[u8]) -> String {
    /// Most bytes one line shows.
    const SHOWN: usize = 32;
    let mut out: String = bytes
        .iter()
        .take(SHOWN)
        .map(|b| format!("{b:02x}"))
        .collect();
    if bytes.len() > SHOWN {
        out.push_str("...");
    }
    out
}

/// Answers where two runs of one function part ways.
///
/// The first step whose instructions differ names the comparison that
/// split them; the calls each side then makes, every write and serviced
/// call that differs follow. The spec is [`run_tsv`]'s with exactly two
/// inputs. Both paths are
/// traced whole, so the budget is held to what one trace holds
/// ([`crate::emulate::TRACE_MAX`]); where the traces agree to the end the
/// report says so, and the writes and calls still tell the two apart.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `a` - The analysis.
/// * `o` - User names.
/// * `spec` - `<function>[,steps=N]/<input>;<input>`.
///
/// # Errors
///
/// When the spec is refused or does not name exactly two inputs.
pub fn run_diff_tsv(p: &Program, a: &Analysis, o: &Overlay, spec: &str) -> Result<String, String> {
    let req = parse_run(a, o, spec)?;
    if req.inputs.len() != 2 {
        return Err("diff takes two inputs: <function>[,steps=N]/<input>;<input>".to_owned());
    }
    let budget = req.budget.min(crate::emulate::TRACE_MAX);
    let (_, shared) = shared_for(p, a, o, req.entry);
    let runs: Vec<DiffRun> = req
        .inputs
        .iter()
        .map(|input| diff_one(p, &shared, req.entry, input, budget))
        .collect::<Option<Vec<_>>>()
        .ok_or("this architecture is not emulated")?;
    let [one, two] = &runs[..] else {
        return Ok(String::new());
    };
    let title = shared
        .sig
        .as_ref()
        .map_or_else(|_| short_name(a, o, req.entry), |s| s.text.clone());
    let mut out = format!(
        "# diff {title}: input 1 vs input 2, at most {budget} steps each
"
    );
    for (n, r) in runs.iter().enumerate() {
        let value = r
            .value
            .map_or_else(|| "-".to_owned(), |v| format!("{v:#x}"));
        let _ = writeln!(
            out,
            "# input {}: {}, returned {}, {} steps",
            n + 1,
            one_line(&r.stop),
            value,
            r.steps
        );
    }
    let common = one
        .trace
        .iter()
        .zip(&two.trace)
        .take_while(|(l, r)| l == r)
        .count();
    if common == one.trace.len() && common == two.trace.len() {
        out.push_str(
            "# the runs agree on every traced step
",
        );
    } else {
        let side = |line: Option<&String>| line.and_then(|l| trace_at(l));
        let (at_one, at_two) = (side(one.trace.get(common)), side(two.trace.get(common)));
        let in_one = at_one
            .and_then(|at| a.function_at(at))
            .map_or_else(|| "no function".to_owned(), |f| short_name(a, o, f.entry));
        let in_two = at_two
            .and_then(|at| a.function_at(at))
            .map_or_else(|| "no function".to_owned(), |f| short_name(a, o, f.entry));
        match (at_one, at_two) {
            (Some(l), Some(r)) => {
                let _ = writeln!(
                    out,
                    "# first divergence: step {} at {l:#x} in {in_one} vs {r:#x} in {in_two}",
                    common + 1
                );
            }
            _ => {
                let _ = writeln!(
                    out,
                    "# first divergence: step {}, one run ended first ({}, {})",
                    common + 1,
                    one_line(&one.stop),
                    one_line(&two.stop)
                );
            }
        }
    }
    for (n, r) in runs.iter().enumerate() {
        let calls = trace_calls(a, o, &r.trace, common);
        if !calls.is_empty() {
            let _ = writeln!(out, "# input {} then called: {}", n + 1, calls.join(", "));
        }
    }
    let split = one
        .call_lines
        .iter()
        .zip(&two.call_lines)
        .position(|(l, r)| l != r);
    match split {
        Some(at) => {
            let _ = writeln!(out, "# serviced call {} differs", at + 1);
            let _ = writeln!(out, "#   1 {}", one.call_lines[at]);
            let _ = writeln!(out, "#   2 {}", two.call_lines[at]);
        }
        None => {
            let (longer, n) = if one.call_lines.len() > two.call_lines.len() {
                (&one.call_lines, 1)
            } else {
                (&two.call_lines, 2)
            };
            for line in longer
                .iter()
                .skip(two.call_lines.len().min(one.call_lines.len()))
            {
                let _ = writeln!(out, "# only input {n} serviced: {line}");
            }
        }
    }
    let mut buffers: Vec<usize> = one
        .writes
        .iter()
        .chain(&two.writes)
        .map(|(k, _, _)| *k)
        .collect();
    buffers.sort_unstable();
    buffers.dedup();
    for k in buffers {
        let hex = |r: &DiffRun| {
            r.writes
                .iter()
                .find(|(n, _, _)| *n == k)
                .map_or_else(|| "(as given)".to_owned(), |(_, b, _)| short_hex(b))
        };
        let _ = writeln!(out, "# a{} after: {} vs {}", k + 1, hex(one), hex(two));
    }
    Ok(out)
}
