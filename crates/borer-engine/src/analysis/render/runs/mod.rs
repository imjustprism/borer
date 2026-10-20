//! Typed runs: a function called on the inputs a reader names, in the
//! emulator, and its answer checked against the function's printed text.

use super::*;
use crate::analysis::decompile::interp::{End, Script, TextRun};
use crate::analysis::decompile::signature::{Kind, Passing, Signature, passing, printed};
use crate::analysis::decompile::{decompile_named, traces, verify};
use crate::emulate::a64::Machine as A64Machine;
use crate::emulate::calls::ApiCall;
use crate::isa::Isa;

mod diff;
mod spec;
mod vectors;

pub use diff::run_diff_tsv;
use spec::{RunSpec, parse_run};
use vectors::VERIFY_SEED;
pub use vectors::{
    Bisected, Counterexample, bisect_iso, check_generated, check_generated_iso, vectors_tsv,
};

/// Most input sets one request runs.
const INPUTS_MAX: usize = 64;

/// Most arguments one input passes.
const ARGS_MAX: usize = 16;

/// Largest buffer one argument sets up, in bytes.
const BUFFER_MAX: usize = 0x8000;

/// Steps each run is given unless the spec says otherwise.
const BUDGET: usize = 1_000_000;

/// Most steps a spec may ask for, of `run` and of `emulate`.
pub(super) const BUDGET_MAX: usize = 20_000_000;

/// Most steps one request's runs take together: the inputs times the steps
/// each is given, so a request's cost is bounded by a count, not by how
/// long the caller waits.
const STEPS_TOTAL_MAX: usize = 100_000_000;

/// Refuses runs that together would take more than [`STEPS_TOTAL_MAX`]
/// steps.
///
/// # Arguments
///
/// * `inputs` - How many inputs the request runs.
/// * `budget` - The steps each run is given.
///
/// # Errors
///
/// When the product is past the cap, saying what to lower.
pub(super) fn within_total(inputs: usize, budget: usize) -> Result<(), String> {
    let total = inputs.saturating_mul(budget);
    if total > STEPS_TOTAL_MAX {
        return Err(format!(
            "{inputs} inputs of {budget} steps is {total} steps, past the {STEPS_TOTAL_MAX} one request runs; lower steps= or pass fewer inputs"
        ));
    }
    Ok(())
}

/// Bytes of a buffer a report spells before the rest are counted.
const SHOWN_MAX: usize = 48;

/// Nonzero runs past [`SHOWN_MAX`] a report names before the rest are a
/// count. A VM context keeps its status past the spelled prefix; the runs
/// say where, without spelling every byte.
const SPAN_MAX: usize = 6;

/// Distance between two buffers' addresses: room for the largest buffer
/// and the guard after it.
const BUFFER_STRIDE: u64 = 0x1_0000;

/// Bytes above the stack pointer at entry a returned stack address may lie:
/// the return address and the stack arguments.
const STACK_ABOVE: u64 = 0x1000;

/// Bytes below the stack pointer at entry a returned stack address may lie:
/// the frames of the function and its callees.
const STACK_BELOW: u64 = 0x100_0000;

/// Zero bytes past each buffer, so a routine that reads a word past a
/// string's end reads zeros, as it would in a real allocation, and a write
/// there shows as one past the end.
const GUARD: usize = 16;

/// One argument of a run, as the reader writes it.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum Arg {
    /// An integer: its bits, two's complement for a negative one.
    Int(u64),
    /// A buffer holding these bytes, whose address is passed: `"text"`
    /// (its terminating zero included) or `hex:<bytes>`.
    Bytes(Vec<u8>),
    /// A zeroed buffer of this many bytes the function writes into:
    /// `out:<size>`.
    Out(usize),
}

impl Arg {
    /// Tells whether the argument passes a buffer's address.
    fn is_buffer(&self) -> bool {
        matches!(self, Self::Bytes(_) | Self::Out(_))
    }

    /// The buffer's bytes as the run starts.
    fn initial(&self) -> Vec<u8> {
        match self {
            Self::Int(_) => Vec::new(),
            Self::Bytes(b) => b.clone(),
            Self::Out(n) => vec![0; *n],
        }
    }

    /// The argument as a report's row spells it.
    fn shown(&self) -> String {
        match self {
            Self::Int(v) => small_hex(*v),
            Self::Bytes(b) => bytes_shown(b),
            Self::Out(n) => format!("out:{n}"),
        }
    }
}

/// A value spelled decimal under ten, hex otherwise, a negative one with
/// its sign.
///
/// # Arguments
///
/// * `v` - The value.
fn small_hex(v: u64) -> String {
    let s = v.cast_signed();
    if (-9..=9).contains(&s) {
        s.to_string()
    } else if s < 0 && s > -0x1_0000 {
        format!("-{:#x}", s.unsigned_abs())
    } else {
        format!("{v:#x}")
    }
}

/// Bytes as a report spells them: a quoted string when they are text up
/// to their terminator, else hex, cut at [`SHOWN_MAX`].
///
/// # Arguments
///
/// * `b` - The bytes.
fn bytes_shown(b: &[u8]) -> String {
    if b == [0] {
        return "\"\"".to_owned();
    }
    let end = b.iter().position(|c| *c == 0).unwrap_or(b.len());
    let (text, rest) = b.split_at(end);
    let tail_zero = rest.iter().all(|c| *c == 0);
    if !text.is_empty() && tail_zero && text.iter().all(|c| (0x20..0x7f).contains(c)) {
        let shown: String = text
            .iter()
            .take(SHOWN_MAX)
            .map(|c| char::from(*c))
            .collect();
        let more = if text.len() > SHOWN_MAX {
            format!("...+{}", text.len() - SHOWN_MAX)
        } else {
            String::new()
        };
        return format!("{shown:?}{more}");
    }
    let hex: Vec<String> = b
        .iter()
        .take(SHOWN_MAX)
        .map(|c| format!("{c:02x}"))
        .collect();
    let more = if b.len() > SHOWN_MAX {
        format!("...+{}", b.len() - SHOWN_MAX)
    } else {
        String::new()
    };
    format!("hex:{}{more}", hex.join(""))
}

/// Nonzero runs in `b` past [`SHOWN_MAX`], at most [`SPAN_MAX`].
///
/// Empty when the spelled prefix already holds every nonzero byte. A
/// further run past the cap is a trailing `,+`.
///
/// # Arguments
///
/// * `b` - The bytes.
fn later_nonzero(b: &[u8]) -> String {
    let mut spans = Vec::new();
    let mut i = SHOWN_MAX;
    let mut more = false;
    while i < b.len() {
        if b[i] == 0 {
            i += 1;
            continue;
        }
        let start = i;
        while i < b.len() && b[i] != 0 {
            i += 1;
        }
        if spans.len() == SPAN_MAX {
            more = true;
            break;
        }
        spans.push(format!("+{start:#x}:{}", i - start));
    }
    if spans.is_empty() {
        return String::new();
    }
    format!(" nz:{}{}", spans.join(","), if more { ",+" } else { "" })
}

/// Bytes a run left in a buffer: [`bytes_shown`], and where nonzero bytes
/// sit past the cut.
///
/// # Arguments
///
/// * `b` - The bytes.
fn bytes_written(b: &[u8]) -> String {
    let shown = bytes_shown(b);
    if shown.starts_with("hex:") {
        format!("{shown}{}", later_nonzero(b))
    } else {
        shown
    }
}

/// Where the buffers of a run go: a region no section of the image takes,
/// one [`BUFFER_STRIDE`] apart.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `count` - How many buffers.
fn buffer_base(p: &Program, count: usize) -> u64 {
    let (mut base, step): (u64, u64) = if p.is_64 {
        (0x0000_5000_0000_0000, 0x0000_0100_0000_0000)
    } else {
        (0x5000_0000, 0x0100_0000)
    };
    let span = from_usize(count.max(1)).saturating_mul(BUFFER_STRIDE);
    for _ in 0..8 {
        let clash = p.sections.iter().any(|s| {
            let end = s.va.0.saturating_add(s.vsize.max(s.file_size));
            s.va.0 < base.saturating_add(span) && base < end
        });
        if !clash {
            break;
        }
        base = base.saturating_add(step);
    }
    base
}

/// What one input sets up: the argument values and the memory behind the
/// buffers.
#[derive(Debug, Clone, PartialEq, Eq)]
struct Layout {
    /// The argument values, in order.
    values: Vec<u64>,
    /// Each argument's buffer address, `None` for an integer.
    at: Vec<Option<u64>>,
    /// The bytes to write first, each buffer with its guard.
    pokes: Vec<(u64, Vec<u8>)>,
}

/// The argument values and the memory one input sets up.
///
/// # Arguments
///
/// * `base` - Where the first buffer goes.
/// * `input` - The arguments.
fn lay_out(base: u64, input: &[Arg]) -> Layout {
    let mut values = Vec::with_capacity(input.len());
    let mut at = Vec::with_capacity(input.len());
    let mut pokes = Vec::new();
    for (k, arg) in input.iter().enumerate() {
        match arg {
            Arg::Int(v) => {
                values.push(*v);
                at.push(None);
            }
            Arg::Bytes(_) | Arg::Out(_) => {
                let addr = base.wrapping_add(from_usize(k).wrapping_mul(BUFFER_STRIDE));
                let mut bytes = arg.initial();
                bytes.resize(bytes.len() + GUARD, 0);
                values.push(addr);
                at.push(Some(addr));
                pokes.push((addr, bytes));
            }
        }
    }
    Layout { values, at, pokes }
}

/// What a run of the binary did.
#[derive(Debug, Clone, PartialEq, Eq)]
struct Machine {
    /// How it ended.
    stop: Stop,
    /// Steps taken.
    steps: usize,
    /// What it returned at the declared width, or `rax` with no
    /// declaration; `None` when it did not return.
    value: Option<u64>,
    /// Each buffer argument's bytes after the run, guard included.
    buffers: Vec<Option<Vec<u8>>>,
    /// The names of the imports it called, in order.
    calls: Vec<String>,
    /// Each serviced call rendered as `api(args) -> ret`, in order: the
    /// behavior trace the arguments decode to.
    call_lines: Vec<String>,
    /// The traced instructions, empty when the run was not traced.
    trace: Vec<String>,
}

/// The register value a return of `bits` hands back: `rax`'s low bits,
/// or `edx:eax` for a 64-bit value on a 32-bit target.
///
/// # Arguments
///
/// * `emu` - The machine after the run.
/// * `bits` - The declared width.
/// * `word` - The machine word in bits.
fn returned_value(emu: &Emulator<'_>, bits: u8, word: u32) -> u64 {
    let rax = emu.register("rax").unwrap_or(0);
    if word == 32 && bits > 32 {
        let rdx = emu.register("rdx").unwrap_or(0);
        return (rdx << 32) | (rax & 0xffff_ffff);
    }
    if bits >= 64 {
        rax
    } else {
        rax & ((1u64 << bits) - 1)
    }
}

/// Reads a buffer back, `0xff` for a byte nothing backs.
///
/// # Arguments
///
/// * `byte_at` - Reads a byte as the machine's loads do, `None` where one
///   faults.
/// * `at` - The buffer's address.
/// * `len` - Its length.
fn read_back(byte_at: impl Fn(u64) -> Option<u8>, at: u64, len: usize) -> Vec<u8> {
    (0..from_usize(len))
        .map(|k| byte_at(at.wrapping_add(k)).unwrap_or(0xff))
        .collect()
}

/// Runs the binary's function on one input.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `entry` - The function.
/// * `pass` - How it takes its arguments on x86; `None` on arm64, whose
///   machine places them by the procedure call standard ([`run_a64`]).
/// * `ret_bits` - The declared return width, `None` to report `rax`.
/// * `input` - The arguments.
/// * `layout` - The values, buffer addresses and setup of the input.
/// * `budget` - Steps.
#[expect(
    clippy::too_many_arguments,
    reason = "a run takes the whole setup of one input"
)]
fn run_machine(
    p: &Program,
    entry: u64,
    pass: Option<&Passing>,
    ret_bits: Option<u8>,
    input: &[Arg],
    layout: &Layout,
    budget: usize,
    traced: bool,
) -> Option<Machine> {
    let Some(pass) = pass else {
        return run_a64(p, entry, ret_bits, input, layout, budget, traced);
    };
    let Layout { values, at, pokes } = layout;
    let mut emu = Emulator::new(p, budget)?;
    emu.back_arguments();
    if traced {
        emu.set_trace(budget);
    }
    emu.install_imports();
    for (addr, bytes) in pokes {
        poke_all(&mut emu, *addr, bytes);
    }
    let sp = emu.register("rsp")?;
    pass.place(&mut emu, sp, values);
    let run = emu.run(entry);
    let word = p.arch.bitness().unwrap_or(64);
    let value = matches!(run.stop, Stop::Returned)
        .then(|| returned_value(&emu, ret_bits.unwrap_or(64), word));
    let buffers = input
        .iter()
        .zip(at)
        .map(|(arg, addr)| {
            addr.map(|a| read_back(|b| emu.byte_at(b), a, arg.initial().len() + GUARD))
        })
        .collect();
    Some(Machine {
        stop: run.stop,
        steps: run.steps,
        value,
        buffers,
        calls: emu.api_names().iter().map(|s| (*s).to_owned()).collect(),
        call_lines: emu.api_calls().iter().map(ApiCall::call_text).collect(),
        trace: emu.trace(),
    })
}

/// Runs an arm64 function on one input, its arguments in `x0`..`x7` and
/// then on the stack, and its value read from `x0`.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `entry` - The function.
/// * `ret_bits` - The declared return width, `None` for all of `x0`.
/// * `input` - The arguments.
/// * `layout` - The values, buffer addresses and setup of the input.
/// * `budget` - Steps.
///
/// # Returns
///
/// The run, which calls no imports; `None` when the image is not arm64.
fn run_a64(
    p: &Program,
    entry: u64,
    ret_bits: Option<u8>,
    input: &[Arg],
    layout: &Layout,
    budget: usize,
    traced: bool,
) -> Option<Machine> {
    let Layout { values, at, pokes } = layout;
    let mut emu = A64Machine::new(p, budget)?;
    for (addr, bytes) in pokes {
        for (k, b) in (0u64..).zip(bytes) {
            emu.poke(addr.wrapping_add(k), *b);
        }
    }
    for (k, v) in values.iter().enumerate() {
        emu.set_arg(k, *v);
    }
    let run = emu.run(entry);
    let value = matches!(run.stop, Stop::Returned).then(|| {
        let x0 = emu.register("x0").unwrap_or(0);
        match ret_bits {
            Some(bits) if bits < 64 => x0 & ((1u64 << bits) - 1),
            Some(_) | None => x0,
        }
    });
    let buffers = input
        .iter()
        .zip(at)
        .map(|(arg, addr)| {
            addr.map(|a| read_back(|b| emu.byte_at(b), a, arg.initial().len() + GUARD))
        })
        .collect();
    if traced {
        emu.set_trace(budget);
    }
    Some(Machine {
        stop: run.stop,
        steps: run.steps,
        value,
        buffers,
        calls: Vec::new(),
        call_lines: emu.api_calls().iter().map(ApiCall::call_text).collect(),
        trace: emu.trace(),
    })
}

/// What the printed text said against the binary on one input.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Verdict {
    /// Both returned the same value and left the same bytes in every
    /// buffer, calling the same imports in the same order; or both stopped
    /// alike.
    Agrees,
    /// They differ: the text's line and what differs there.
    Differs(usize, String),
    /// Nothing is claimed: the line the text stopped at, if any, and why.
    Unchecked(Option<usize>, String),
}

/// One input's answer: the binary's run and the text's verdict.
#[derive(Debug, Clone, PartialEq, Eq)]
struct Outcome {
    /// How the binary's run ended, in words.
    stop: String,
    /// Steps the binary took.
    steps: usize,
    /// What it returned, `None` when it did not.
    value: Option<u64>,
    /// Each buffer argument the run changed, by position from zero, with
    /// its bytes after, and how many bytes it wrote past the end.
    writes: Vec<(usize, Vec<u8>, usize)>,
    /// The text against the binary.
    verdict: Verdict,
    /// Statements the text ran, its callees' steps included.
    text_steps: usize,
    /// The imports and syscalls the binary's run serviced, each rendered
    /// `api(args) -> ret`, in order.
    call_lines: Vec<String>,
}

impl Outcome {
    /// Bytes the outcome holds, for the memo's budget.
    fn bytes(&self) -> usize {
        self.stop.capacity()
            + self
                .writes
                .iter()
                .map(|(_, b, _)| b.capacity() + size_of::<(usize, Vec<u8>, usize)>())
                .sum::<usize>()
            + self
                .call_lines
                .iter()
                .map(|l| l.capacity() + size_of::<String>())
                .sum::<usize>()
            + match &self.verdict {
                Verdict::Agrees => 0,
                Verdict::Differs(_, s) | Verdict::Unchecked(_, s) => s.capacity(),
            }
    }
}

/// Compares the text's run with the binary's on one input.
///
/// # Arguments
///
/// * `m` - The binary's run.
/// * `t` - The text's run.
/// * `at` - Each buffer argument's address.
/// * `ret` - The declared return kind and width, `None` for `void`.
fn judge(m: &Machine, t: &TextRun<'_>, at: &[Option<u64>], ret: Option<(Kind, u8)>) -> Verdict {
    let line = t.line;
    if m.value.is_none() {
        return match (&t.end, &m.stop) {
            (End::Fault(x), Stop::Fault(y)) if x == y => Verdict::Agrees,
            (End::Budget, Stop::Budget) => Verdict::Agrees,
            _ => Verdict::Unchecked(None, format!("the binary did not return: {}", m.stop)),
        };
    }
    let returned = match &t.end {
        End::Returned(v) => *v,
        End::Unchecked(why) => return Verdict::Unchecked(Some(line), why.clone()),
        End::Refused(why) => {
            return Verdict::Differs(line, format!("as ISO C, {why}; the binary returned"));
        }
        End::Trap => {
            return Verdict::Differs(line, "the text stops here; the binary returned".to_owned());
        }
        End::Fault(x) => {
            return Verdict::Differs(
                line,
                format!(
                    "the text reads or writes {}, which nothing set; the binary returned",
                    whose(*x, at, &m.buffers, t.entry_sp)
                ),
            );
        }
        End::Budget => {
            return Verdict::Differs(
                line,
                format!(
                    "the text is still running after {} steps; the binary returned after {}",
                    t.steps, m.steps
                ),
            );
        }
        End::Callee(name, stop) => {
            let stop = match stop {
                Stop::Fault(x) => format!(
                    "it reads or writes {}, which nothing set",
                    whose(*x, at, &m.buffers, t.entry_sp)
                ),
                other => other.to_string(),
            };
            return Verdict::Differs(
                line,
                format!("the call to {name} does not return: {stop}; in the binary it does"),
            );
        }
    };
    let stack = |v: u64| {
        v <= t.entry_sp.wrapping_add(STACK_ABOVE) && t.entry_sp - v.min(t.entry_sp) <= STACK_BELOW
    };
    if let (Some((Kind::Int(..) | Kind::Pointer, bits)), Some(text), Some(machine)) =
        (ret, returned, m.value)
        && text != machine
    {
        if t.literals.contains(&text) {
            return Verdict::Unchecked(
                Some(line),
                "the text returns a string literal, and which copy of its bytes it means the text does not say".to_owned(),
            );
        }
        if stack(text) && stack(machine) {
            return Verdict::Unchecked(
                Some(line),
                "both return an address on the stack, which differs with the depth a call is made from".to_owned(),
            );
        }
        if let Some(lane) = t.ret_lane.filter(|&b| {
            u64::from(b) < u64::from(bits) && text == machine & (1u64 << b).wrapping_sub(1)
        }) {
            return Verdict::Unchecked(
                Some(line),
                format!(
                    "the text states only the low {lane} bits of the result; the bits above are the machine's own"
                ),
            );
        }
        if t.emu.api_calls().iter().any(|c| {
            let reads = match c.api.as_str() {
                "memcpy" | "memmove" => c.args.get(1),
                "strlen" | "wcslen" => c.args.first(),
                _ => None,
            };
            reads.is_some_and(|a| {
                let shown = a.shown();
                shown.starts_with("ptr ") && m.call_lines.iter().any(|l| l.contains(&shown))
            })
        }) {
            return Verdict::Unchecked(
                Some(line),
                "the run reads an address nothing maps through an import, on both sides".to_owned(),
            );
        }
        let low = if bits > 32 && machine >> 32 == 0 && text & 0xffff_ffff == machine {
            " (the low 32 bits agree)"
        } else {
            ""
        };
        let sources: Vec<String> = t
            .sources
            .iter()
            .map(|(n, l)| {
                if *l == 0 {
                    format!("{n} never set before it")
                } else {
                    format!("{n} set at line {l}")
                }
            })
            .collect();
        let from = if sources.is_empty() {
            String::new()
        } else {
            format!("; {}", sources.join(", "))
        };
        return Verdict::Differs(
            line,
            format!("the text returns {text:#x}, the binary {machine:#x}{low}{from}"),
        );
    }
    for (k, addr) in at.iter().enumerate() {
        let (Some(addr), Some(Some(after))) = (addr, m.buffers.get(k)) else {
            continue;
        };
        let text = read_back(|b| t.emu.byte_at(b), *addr, after.len());
        let own = after.len().saturating_sub(GUARD);
        let word = |buf: &[u8], s: usize| {
            buf.get(s..s + 8).map(|b| {
                b.iter()
                    .enumerate()
                    .fold(0u64, |w, (n, x)| w | (u64::from(*x) << (8 * n)))
            })
        };
        let mut diff: Option<(usize, u8, u8)> = None;
        for (i, (x, y)) in text.iter().zip(after.iter()).enumerate() {
            if x == y {
                continue;
            }
            if i >= own && (*x != 0) == (*y != 0) {
                continue;
            }
            diff = Some((i, *x, *y));
            break;
        }
        let Some((i, x, y)) = diff else {
            continue;
        };
        for s in i.saturating_sub(7)..=i {
            if let (Some(tw), Some(mw)) = (word(&text, s), word(after, s)) {
                if t.literals.contains(&tw) {
                    return Verdict::Unchecked(
                        Some(line),
                        "the text writes a string literal's address, and which copy of its bytes it means the text does not say".to_owned(),
                    );
                }
                if stack(tw) && stack(mw) {
                    return Verdict::Unchecked(
                        Some(line),
                        "both write an address on the stack, which differs with the depth a call is made from".to_owned(),
                    );
                }
            }
        }
        let place = from_usize(i);
        let writer = t.writers.get(&addr.wrapping_add(place)).copied();
        let what = format!(
            "a{}[{i}] is {:#04x} after the text, {:#04x} after the binary{}",
            k + 1,
            x,
            y,
            if writer.is_some() {
                ""
            } else {
                "; no line of the text writes it"
            }
        );
        return Verdict::Differs(writer.unwrap_or(line), what);
    }
    let (machine_calls, text_calls) = (&m.calls, t.emu.api_names());
    if let Some(i) = (0..machine_calls.len().max(text_calls.len()))
        .find(|&i| machine_calls.get(i).map(String::as_str) != text_calls.get(i).copied())
    {
        let say = |c: Option<&str>| c.map_or_else(|| "nothing".to_owned(), ToOwned::to_owned);
        return Verdict::Differs(
            line,
            format!(
                "call {} of an import is {} in the text, {} in the binary",
                i + 1,
                say(text_calls.get(i).copied()),
                say(machine_calls.get(i).map(String::as_str))
            ),
        );
    }
    match ret {
        Some((Kind::Float | Kind::Other, _)) => Verdict::Unchecked(
            Some(line),
            "the result is not an integer, so only memory and calls were compared".to_owned(),
        ),
        _ => Verdict::Agrees,
    }
}

/// Says where an address the text faulted on is: in or past a buffer
/// argument, in the stack frame (as an offset from the stack pointer at
/// entry), or just the address.
///
/// # Arguments
///
/// * `x` - The address.
/// * `at` - Each buffer argument's address.
/// * `buffers` - Each buffer argument's bytes, guard included.
/// * `entry_sp` - The stack pointer at entry.
fn whose(x: u64, at: &[Option<u64>], buffers: &[Option<Vec<u8>>], entry_sp: u64) -> String {
    /// Bytes below the stack pointer at entry read as the frame.
    const FRAME: u64 = 0x1_0000;
    for (k, (addr, bytes)) in at.iter().zip(buffers).enumerate() {
        let (Some(addr), Some(bytes)) = (addr, bytes) else {
            continue;
        };
        if let Some(off) = x.checked_sub(*addr).filter(|o| *o < BUFFER_STRIDE) {
            let past = if off >= from_usize(bytes.len().saturating_sub(GUARD)) {
                ", past its end"
            } else {
                ""
            };
            return format!("a{}+{off:#x}{past}", k + 1);
        }
    }
    if x < entry_sp && entry_sp - x <= FRAME {
        return format!("the frame at entry-{:#x}", entry_sp - x);
    }
    if x >= entry_sp && x - entry_sp <= FRAME {
        return format!("the frame at entry+{:#x}", x - entry_sp);
    }
    format!("{x:#x}")
}

/// The parts of one request every input shares: the signature and the
/// text read once, and how the function takes its arguments.
struct Shared<'p> {
    /// The signature the text prints, or why there is none.
    sig: Result<Signature, String>,
    /// The function's text, read, or why it could not be.
    script: Result<Script<'p>, String>,
    /// How the function takes its arguments on x86; `None` on arm64,
    /// whose machine places them itself.
    pass: Option<Passing>,
}

/// Runs one input: the binary, then the text, and the verdict.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `shared` - The text and the convention.
/// * `entry` - The function.
/// * `input` - The arguments.
/// * `budget` - Steps.
fn run_one(p: &Program, shared: &Shared<'_>, entry: u64, input: &[Arg], budget: usize) -> Outcome {
    let buffers = input.iter().filter(|a| a.is_buffer()).count();
    let layout = lay_out(buffer_base(p, buffers.max(input.len())), input);
    let ret = shared.sig.as_ref().ok().and_then(Signature::return_kind);
    let Some(m) = run_machine(
        p,
        entry,
        shared.pass.as_ref(),
        ret.map(|(_, bits)| bits),
        input,
        &layout,
        budget,
        false,
    ) else {
        return Outcome {
            stop: "this architecture is not emulated".to_owned(),
            steps: 0,
            value: None,
            writes: Vec::new(),
            verdict: Verdict::Unchecked(None, "nothing ran".to_owned()),
            text_steps: 0,
            call_lines: Vec::new(),
        };
    };
    let writes = buffer_writes(input, &m.buffers);
    let (verdict, text_steps) = match &shared.script {
        Err(why) => (Verdict::Unchecked(None, why.clone()), 0),
        Ok(script) => match script.run(&layout.values, &layout.pokes, budget) {
            None => (Verdict::Unchecked(None, "nothing ran".to_owned()), 0),
            Some(t) => (judge(&m, &t, &layout.at, ret), t.steps),
        },
    };
    Outcome {
        stop: m.stop.to_string(),
        steps: m.steps,
        value: m.value,
        writes,
        verdict,
        text_steps,
        call_lines: m.call_lines,
    }
}

/// Runs a function on each input, in the emulator and through its printed
/// text, and tabulates both.
///
/// Each input is typed by the decompiler's recovered signature: an integer
/// for an integer parameter, a buffer (`"text"`, `hex:<bytes>`) or an
/// `out:<size>` buffer for a pointer, whose address is passed. An input
/// giving fewer arguments than the signature lists, or a floating one, is
/// refused; a buffer for an integer parameter, or more arguments than the
/// signature lists, is passed and said so. Every run starts from the same
/// state, the registers zero but for the arguments, memory the image's
/// and the buffers', with the step budget and no permissive mode, so the
/// same request answers the same, byte for byte.
///
/// The binary's row says what it returned (at the declared width, or
/// `void` when the signature returns nothing, so a leftover `rax` is not
/// the answer), how it stopped, the steps, and what it left in each buffer
/// it changed. A buffer longer than the spelled prefix also names the
/// nonzero runs past that prefix. The
/// text column says whether the decompiled text, run as C on the same
/// inputs ([`Script`]), returned the same, left the same bytes and called
/// the same imports: `agrees`, `differs@L<n>` with the line, or
/// `unchecked` with why. Each input's result is memoized through
/// [`Analysis::derived`] under the names in force.
///
/// An arm64 function runs in its own machine ([`A64Machine`]), its
/// arguments in `x0`..`x7` and then on the stack; its text is not run as C
/// here (the decompile answer checks it block by block instead), so every
/// row is `unchecked` and no signature types the inputs.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `a` - The analysis.
/// * `o` - User names.
/// * `spec` - `<function>[,steps=N]/<input>[;<input>...]` ([`parse_run`]).
///
/// # Returns
///
/// The table, a line per input that differs or could not be checked, when
/// one differs what the structure check and the lifter's check say of the
/// function, and the imported APIs and syscalls the runs serviced, each
/// `api(args) -> ret` with its arguments decoded by the type library.
///
/// # Errors
///
/// When the spec does not read, or an input does not fit the signature.
pub fn run_tsv(p: &Program, a: &Analysis, o: &Overlay, spec: &str) -> Result<String, String> {
    let req = parse_run(a, o, spec)?;
    let entry = req.entry;
    let (text, shared) = shared_for(p, a, o, entry);
    let mut notes: Vec<String> = Vec::new();
    if let Ok(sig) = &shared.sig {
        let kinds = sig.parameter_kinds();
        for (n, input) in req.inputs.iter().enumerate() {
            if input.len() < kinds.len() {
                return Err(format!(
                    "input {} gives {} argument{}; the signature {} takes {}",
                    n + 1,
                    input.len(),
                    plural(input.len()),
                    sig.text,
                    kinds.len()
                ));
            }
            for (k, (arg, kind)) in input.iter().zip(&kinds).enumerate() {
                match (arg, kind) {
                    (_, Kind::Float) => {
                        return Err(format!(
                            "a{} is a floating parameter; a run passes integers and buffers",
                            k + 1
                        ));
                    }
                    (Arg::Bytes(_) | Arg::Out(_), Kind::Int(..)) => {
                        let note = format!("a{} is an integer, given a buffer: its address", k + 1);
                        if !notes.contains(&note) {
                            notes.push(note);
                        }
                    }
                    _ => {}
                }
            }
            if input.len() > kinds.len() {
                let note = format!(
                    "the signature lists {}; the rest pass where the convention puts them",
                    kinds.len()
                );
                if !notes.contains(&note) {
                    notes.push(note);
                }
            }
        }
    }
    let names = o.fingerprint();
    let outcomes: Vec<Arc<Outcome>> = req
        .inputs
        .iter()
        .map(|input| {
            a.derived.get_or_build_item(
                "fn_run",
                names,
                (entry, req.budget, input.clone()),
                || run_one(p, &shared, entry, input, req.budget),
                Outcome::bytes,
            )
        })
        .collect();
    Ok(render_runs(
        p,
        a,
        o,
        &req,
        &shared,
        text.as_deref(),
        &outcomes,
        &notes,
    ))
}

/// What each buffer argument holds after a run, only the ones the run
/// changed: its index, its bytes, and how far past the input it wrote.
///
/// # Arguments
///
/// * `input` - The arguments, their initial bytes read back against.
/// * `buffers` - Where each buffer argument landed, as the machine left it.
fn buffer_writes(input: &[Arg], buffers: &[Option<Vec<u8>>]) -> Vec<(usize, Vec<u8>, usize)> {
    input
        .iter()
        .zip(buffers)
        .enumerate()
        .filter_map(|(k, (arg, after))| {
            let after = after.as_ref()?;
            let initial = arg.initial();
            let (body, guard) = after.split_at(initial.len().min(after.len()));
            let past = guard.iter().rposition(|b| *b != 0).map_or(0, |i| i + 1);
            (body != initial.as_slice() || past > 0).then(|| (k, body.to_vec(), past))
        })
        .collect()
}

/// The text and convention a run of `entry` needs, with the text itself.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `a` - The analysis.
/// * `o` - User names.
/// * `entry` - The function to run.
///
/// # Returns
///
/// The decompiled text, `None` where the architecture reads none, and the
/// signature, script and calling convention shared by every run of it.
fn shared_for<'s>(
    p: &'s Program,
    a: &'s Analysis,
    o: &'s Overlay,
    entry: u64,
) -> (Option<String>, Shared<'s>) {
    let a64 = matches!(p.arch.isa(), Some(Isa::A64));
    let (text, why) = if a64 {
        (
            None,
            "a run's text is checked for x86 code only; an arm64 text is checked block by block against the arm64 machine (decompile's checked line)",
        )
    } else {
        (
            decompile_named(p, a, o, entry),
            "the function does not decompile",
        )
    };
    let word = u8::try_from(p.arch.bitness().unwrap_or(64)).unwrap_or(64);
    let shared = Shared {
        sig: text
            .as_deref()
            .ok_or_else(|| why.to_owned())
            .and_then(|t| printed(t, word)),
        script: text
            .as_deref()
            .ok_or_else(|| why.to_owned())
            .and_then(|t| Script::read(p, a, o, entry, t)),
        pass: (!a64).then(|| passing(p, a, o, entry)),
    };
    (text, shared)
}

/// Writes the report of a run request.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `a` - The analysis.
/// * `o` - User names.
/// * `req` - The request.
/// * `shared` - Its text and convention.
/// * `text` - The decompiled text, for the lines a verdict names.
/// * `outcomes` - Each input's outcome.
/// * `notes` - What the typing said of the inputs.
#[expect(
    clippy::too_many_arguments,
    reason = "the report reads every part of the request it answers"
)]
fn render_runs(
    p: &Program,
    a: &Analysis,
    o: &Overlay,
    req: &RunSpec,
    shared: &Shared<'_>,
    text: Option<&str>,
    outcomes: &[Arc<Outcome>],
    notes: &[String],
) -> String {
    let lines: Vec<&str> = text.map_or_else(Vec::new, |t| t.lines().collect());
    let signature = shared.sig.as_ref().map_or_else(
        |_| match p.arch.isa() {
            Some(Isa::A64) => format!(
                "{} (no signature: an arm64 run passes its inputs untyped)",
                short_name(a, o, req.entry)
            ),
            Some(Isa::X86 { .. } | Isa::A32) | None => format!(
                "{} (no signature: it does not decompile)",
                short_name(a, o, req.entry)
            ),
        },
        |s| s.text.clone(),
    );
    let count = |f: fn(&Verdict) -> bool| outcomes.iter().filter(|x| f(&x.verdict)).count();
    let agree = count(|v| matches!(v, Verdict::Agrees));
    let differ = count(|v| matches!(v, Verdict::Differs(..)));
    let unchecked = outcomes.len() - agree - differ;
    let void = matches!(&shared.sig, Ok(s) if s.return_kind().is_none());
    let mut out = format!(
        "# run {signature}: {} input{}, at most {} steps each; the text agrees on {agree}, differs on {differ}, unchecked on {unchecked}\n",
        outcomes.len(),
        plural(outcomes.len()),
        req.budget
    );
    for n in notes {
        let _ = writeln!(out, "# {n}");
    }
    out.push_str("# args\treturns\tstop\tsteps\twrites\ttext\n");
    for (input, x) in req.inputs.iter().zip(outcomes) {
        let args = args_shown(input);
        let returns = match (void, x.value) {
            (true, Some(_)) => "void".to_owned(),
            (_, Some(v)) => small_hex(v),
            (_, None) => "-".to_owned(),
        };
        let writes = writes_shown(x);
        let verdict = match &x.verdict {
            Verdict::Agrees => "agrees".to_owned(),
            Verdict::Differs(l, _) => format!("differs@L{l}"),
            Verdict::Unchecked(..) => "unchecked".to_owned(),
        };
        let _ = writeln!(
            out,
            "{args}\t{returns}\t{}\t{}\t{writes}\t{verdict}",
            x.stop, x.steps
        );
    }
    let line_text = |l: usize| {
        lines.get(l.wrapping_sub(1)).map_or_else(String::new, |t| {
            let t = t.trim();
            let cut: String = t.chars().take(80).collect();
            format!(" `{cut}`")
        })
    };
    for (n, x) in outcomes.iter().enumerate() {
        match &x.verdict {
            Verdict::Agrees => {}
            Verdict::Differs(l, what) => {
                let _ = writeln!(
                    out,
                    "# input {} differs at line {l}{}: {what}",
                    n + 1,
                    line_text(*l)
                );
            }
            Verdict::Unchecked(Some(l), why) => {
                let _ = writeln!(
                    out,
                    "# input {} unchecked at line {l}{}: {why}",
                    n + 1,
                    line_text(*l)
                );
            }
            Verdict::Unchecked(None, why) => {
                let _ = writeln!(out, "# input {} unchecked: {why}", n + 1);
            }
        }
    }
    if differ > 0 {
        let structure = match text {
            Some(t) => match traces::check_structure(p, a, o, req.entry, t) {
                traces::Structure::Agrees => "agrees".to_owned(),
                traces::Structure::Disagrees(d) => format!(
                    "the {} has a path the other lacks at {} ({})",
                    match d.side {
                        traces::Side::Text => "text",
                        traces::Side::Binary => "binary",
                    },
                    d.at,
                    d.step
                ),
                traces::Structure::Unchecked(why) => format!("unchecked: {why}"),
            },
            None => "unchecked: no text".to_owned(),
        };
        let _ = writeln!(out, "# structure check: {structure}");
        let v = verify::verify(p, a, &[req.entry], VERIFY_SEED);
        let lifter = match v.mismatches.first() {
            None => format!(
                "agrees on {} of {} blocks ({} facts)",
                v.checked, v.blocks, v.compared
            ),
            Some(m) => format!(
                "{} mismatch{}, first in block {:#x}: {} {} is {:#x} lifted, {:#x} emulated",
                v.mismatches.len(),
                if v.mismatches.len() == 1 { "" } else { "es" },
                m.block,
                m.fact,
                m.place,
                m.lifted,
                m.emulated
            ),
        };
        let _ = writeln!(out, "# lifter check: {lifter}");
    }
    api_calls_section(&mut out, req, outcomes);
    out
}

/// An input's arguments as a row spells them, `-` for none.
///
/// # Arguments
///
/// * `input` - The arguments.
fn args_shown(input: &[Arg]) -> String {
    if input.is_empty() {
        return "-".to_owned();
    }
    input.iter().map(Arg::shown).collect::<Vec<_>>().join(" ")
}

/// What a run left in the buffers it changed, as a row spells it: `aN=`
/// and the bytes, with what it wrote past the end and, for a cut hex
/// buffer, the nonzero runs past the prefix; `-` for nothing.
///
/// # Arguments
///
/// * `x` - The run's outcome.
fn writes_shown(x: &Outcome) -> String {
    if x.writes.is_empty() {
        return "-".to_owned();
    }
    x.writes
        .iter()
        .map(|(k, b, past)| {
            let tail = if *past > 0 {
                format!(" +{past} past the end")
            } else {
                String::new()
            };
            format!("a{}={}{tail}", k + 1, bytes_written(b))
        })
        .collect::<Vec<_>>()
        .join(" ")
}

/// Call rows one run request lists before the rest are counted.
const RUN_CALLS_SHOWN: usize = 48;

/// Writes the imports and syscalls the runs serviced, grouped by input,
/// each call `api(args) -> ret` with its arguments decoded by the type
/// library ([`crate::emulate::calls`]).
///
/// A pure function calls nothing, so the section is written only when a run
/// serviced a call; it is capped at [`RUN_CALLS_SHOWN`] lines with a
/// `# showing N of M` count, since a long run can service many.
///
/// # Arguments
///
/// * `out` - The report so far.
/// * `req` - The request, for the inputs the rows belong to.
/// * `outcomes` - Each input's outcome, holding its serviced calls.
fn api_calls_section(out: &mut String, req: &RunSpec, outcomes: &[Arc<Outcome>]) {
    let total: usize = outcomes.iter().map(|o| o.call_lines.len()).sum();
    if total == 0 {
        return;
    }
    let _ = writeln!(
        out,
        "# api calls: {}, api(args) -> ret, by input",
        showing(total.min(RUN_CALLS_SHOWN), total)
    );
    let mut shown = 0usize;
    for (input, outcome) in req.inputs.iter().zip(outcomes) {
        for line in &outcome.call_lines {
            if shown >= RUN_CALLS_SHOWN {
                return;
            }
            let args: Vec<String> = input.iter().map(Arg::shown).collect();
            let args = if args.is_empty() {
                "-".to_owned()
            } else {
                args.join(" ")
            };
            let _ = writeln!(out, "{args}\t{line}");
            shown += 1;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::vectors::{generated, vector_inputs, vectors_tsv};
    use super::{
        Arg, Kind, SHOWN_MAX, args_shown, bytes_written, later_nonzero, parse_run, run_tsv,
        small_hex,
    };
    use crate::analysis::decompile::decompile_named;
    use crate::analysis::decompile::signature::printed;
    use crate::analysis::{Analysis, Overlay};
    use crate::program::{Arch, Program, Section};

    /// A buffer checksum: `acc = acc * 33 + byte` from 0x1505 over the
    /// first `len` bytes of `buf`, `len` cut at 64 by the compare `solve`
    /// finds.
    const SUM33: [u8; 37] = [
        0xb8, 0x05, 0x15, 0x00, 0x00, // ASM: mov eax, 0x1505
        0x83, 0xfa, 0x40, // ASM: cmp edx, 0x40
        0x76, 0x05, // ASM: jbe +5
        0xba, 0x40, 0x00, 0x00, 0x00, // ASM: mov edx, 0x40
        0x85, 0xd2, // ASM: test edx, edx
        0x74, 0x11, // ASM: je +0x11
        0x6b, 0xc0, 0x21, // ASM: imul eax, eax, 33
        0x44, 0x0f, 0xb6, 0x01, // ASM: movzx r8d, byte [rcx]
        0x44, 0x01, 0xc0, // ASM: add eax, r8d
        0x48, 0xff, 0xc1, // ASM: inc rcx
        0xff, 0xca, // ASM: dec edx
        0x75, 0xef, // ASM: jne -0x11
        0xc3, // ASM: ret
    ];

    /// What [`SUM33`] returns, computed apart from the binary.
    ///
    /// # Arguments
    ///
    /// * `buf` - The buffer.
    /// * `len` - The length argument, as passed.
    fn sum33(buf: &[u8], len: u64) -> u64 {
        let n = usize::try_from(crate::num::lo32(len).min(64)).unwrap_or(64);
        u64::from(buf.iter().take(n).fold(0x1505u32, |acc, &b| {
            acc.wrapping_mul(33).wrapping_add(u32::from(b))
        }))
    }

    /// Vectors none of which returned write no harness: it asserted nothing
    /// and cost some 900 bytes of C in every such answer.
    ///
    /// # Panics
    ///
    /// When the harness is written anyway.
    #[test]
    fn vectors_that_never_return_write_no_harness() {
        let p = Program::raw_x64(&[0xeb, 0xfe]);
        let a = Analysis::compute(&p);
        let out = vectors_tsv(&p, &a, &Overlay::default(), "0x1000,steps=50").unwrap();
        assert!(out.contains("; 0 returned\n"), "{out}");
        assert!(
            out.ends_with("# harness: none, since no vector returned\n"),
            "{out}"
        );
        assert!(!out.contains("#include"), "{out}");
    }

    /// Vectors for a buffer checksum: a row per input with the checksum a
    /// model computes apart, the harness asserting each of them, the same
    /// request answering the same, and the counts capped.
    ///
    /// # Panics
    ///
    /// When a row or an assertion is missing, a repeat differs, or a cap
    /// does not hold.
    #[test]
    fn vectors_record_a_checksum_and_its_harness() {
        let p = Program::raw_x64(&SUM33);
        let a = Analysis::compute(&p);
        let o = Overlay::default();
        let out = vectors_tsv(&p, &a, &o, "0x1000").unwrap();
        let text = decompile_named(&p, &a, &o, 0x1000).unwrap();
        let sig = printed(&text, 64).unwrap();
        let kinds = sig.parameter_kinds();
        assert!(
            matches!(kinds.as_slice(), [Kind::Pointer, Kind::Int(..)]),
            "{sig:?}"
        );
        assert!(out.contains("(1 from the constants it compares"), "{out}");
        let inputs = vector_inputs(&kinds, &[0x40], 16, 0x1000).unwrap();
        assert_eq!(inputs.len(), 16);
        for input in &inputs {
            let [buf, Arg::Int(len)] = input.as_slice() else {
                panic!("{input:?}")
            };
            let want = sum33(&buf.initial(), *len);
            let row = format!(
                "\n{}\t{}\treturned\t-\n",
                args_shown(input),
                small_hex(want)
            );
            assert!(out.contains(&row), "{row:?} in\n{out}");
            assert!(
                out.contains(&format!("if (got != {want:#x}) differs(")),
                "{want:#x} in\n{out}"
            );
        }
        assert!(
            out.contains("\nuint32_t sub_1000(uint8_t *a1, uint64_t a2);\n"),
            "{out}"
        );
        assert!(
            out.contains("/* 16 of the 16 vectors that returned"),
            "{out}"
        );
        assert_eq!(out, vectors_tsv(&p, &a, &o, "0x1000").unwrap());
        let many = vectors_tsv(&p, &a, &o, "0x1000,count=64").unwrap();
        let rows = many
            .lines()
            .skip(2)
            .take_while(|l| !l.starts_with("# harness"))
            .count();
        assert_eq!(rows, 64, "{many}");
        assert!(
            many.contains("/* 16 of the 64 vectors that returned"),
            "{many}"
        );
        for (bad, says) in [
            ("0x1000,count=65", "count is 1 to 64"),
            ("0x1000,count=0", "count is 1 to 64"),
            ("0x1000,lang=c", "vectors takes"),
            ("nowhere", "cannot resolve nowhere"),
        ] {
            let err = vectors_tsv(&p, &a, &o, bad).unwrap_err();
            assert!(err.contains(says), "{bad}: {err}");
        }
    }

    /// A request whose inputs times their steps pass the per-request total
    /// is refused before anything runs, for `run` and for `vectors`.
    ///
    /// # Panics
    ///
    /// When the request is taken, or one within the total refused.
    #[test]
    fn a_request_past_the_total_steps_is_refused() {
        let p = Program::raw_x64(&[0xc3]);
        let a = Analysis::compute(&p);
        let o = Overlay::default();
        let six = "0x1000,steps=20000000/1;2;3;4;5;6";
        let err = parse_run(&a, &o, six).map(|s| s.budget).unwrap_err();
        assert!(err.contains("past the 100000000"), "{err}");
        assert!(parse_run(&a, &o, "0x1000,steps=20000000/1;2;3;4;5").is_ok());
        let err = vectors_tsv(&p, &a, &o, "0x1000,count=64,steps=2000000").unwrap_err();
        assert!(err.contains("past the 100000000"), "{err}");
    }

    /// The forms of an argument read, and a malformed one is refused naming
    /// it.
    ///
    /// # Panics
    ///
    /// When an argument reads otherwise or a malformed one is taken.
    #[test]
    fn arguments_read_in_every_form() {
        let p = Program::raw_x64(&[0xc3]);
        let a = Analysis::compute(&p);
        let o = Overlay::default();
        let spec = parse_run(&a, &o, "0x1000,steps=500/1,-1,\"a,b\\n\",hex:0102,out:4;").unwrap();
        assert_eq!(spec.budget, 500);
        assert_eq!(
            spec.inputs[0],
            vec![
                Arg::Int(1),
                Arg::Int(u64::MAX),
                Arg::Bytes(b"a,b\n\0".to_vec()),
                Arg::Bytes(vec![1, 2]),
                Arg::Out(4),
            ]
        );
        assert_eq!(spec.inputs[1], Vec::new());
        for (bad, says) in [
            ("0x1000/zz", "cannot read the argument zz"),
            ("0x1000/hex:1", "hex: takes pairs"),
            ("0x1000,foo/1", "cannot read foo"),
            ("nowhere/1", "cannot resolve nowhere"),
            ("0x1000", "run takes"),
        ] {
            let err = parse_run(&a, &o, bad).unwrap_err();
            assert!(err.contains(says), "{bad}: {err}");
        }
    }

    /// A cut buffer still names nonzero bytes past the spelled prefix.
    ///
    /// # Panics
    ///
    /// When the suffix does not name that run, or a short buffer grows one.
    #[test]
    fn a_cut_buffer_names_nonzero_bytes_past_the_prefix() {
        let mut bytes = vec![0u8; SHOWN_MAX + 8];
        bytes[SHOWN_MAX + 2] = 0x41;
        bytes[SHOWN_MAX + 3] = 0x42;
        let shown = bytes_written(&bytes);
        assert!(shown.contains("...+8"), "{shown}");
        assert!(
            shown.contains(&format!("nz:+{:#x}:2", SHOWN_MAX + 2)),
            "{shown}"
        );
        assert!(later_nonzero(&[1, 2, 3]).is_empty());
    }

    /// A function the signature types as `void` does not report the `rax`
    /// it left behind. The value lives in the buffer it wrote.
    ///
    /// # Panics
    ///
    /// When the row spells a number where `void` belongs.
    #[test]
    fn a_void_function_does_not_report_its_leftover_rax() {
        let code = [
            0xc7, 0x01, 0x01, 0x00, 0x00, 0x00, // ASM: mov dword ptr [rcx], 1
            0xc3, // ASM: ret
        ];
        let p = Program::raw_x64(&code);
        let a = Analysis::compute(&p);
        let out = run_tsv(&p, &a, &Overlay::default(), "0x1000/out:4").unwrap();
        assert!(out.contains("\tvoid\treturned\t"), "{out}");
        assert!(out.contains("a1=hex:01000000"), "{out}");
    }

    /// A callee's stack address is no answer to compare: the text calls it
    /// from another depth than the binary does.
    ///
    /// # Panics
    ///
    /// When the run says the text differs.
    #[test]
    fn a_returned_stack_address_is_unchecked() {
        let mut code = vec![0xccu8; 0x20];
        code[..6].copy_from_slice(&[
            0xe8, 0x0b, 0x00, 0x00, 0x00, // ASM: call 0x1010
            0xc3, // ASM: ret
        ]);
        code[0x10..0x16].copy_from_slice(&[
            0x48, 0x8d, 0x44, 0x24, 0x08, // ASM: lea rax,[rsp+8]
            0xc3, // ASM: ret
        ]);
        let p = Program::raw_x64(&code);
        let a = Analysis::compute(&p);
        let out = run_tsv(&p, &a, &Overlay::default(), "0x1000/").unwrap();
        assert!(
            out.contains(
                "	unchecked
"
            ),
            "{out}"
        );
    }

    /// A returned string literal is no answer to compare by its address:
    /// the text spells its bytes, not which copy of them it means.
    ///
    /// # Panics
    ///
    /// When the run says the text differs.
    #[test]
    fn a_returned_literal_is_unchecked_by_its_address() {
        let mut bytes = vec![0xccu8; 0x200];
        bytes[..8].copy_from_slice(&[
            0x48, 0x8d, 0x05, 0x09, 0x10, 0x00, 0x00, // ASM: lea rax,[rip+0x1009]
            0xc3, // ASM: ret
        ]);
        bytes[0x100..0x120].fill(0);
        bytes[0x100..0x104].copy_from_slice(b"abcd");
        bytes[0x110..0x114].copy_from_slice(b"abcd");
        let text = Section::mapped(".text", 0x1000, 0, 0x100, false, true);
        let rdata = Section::mapped(".rdata", 0x2000, 0x100, 0x100, false, false);
        let p = Program::raw(bytes, Arch::X86_64, 0, Some(0x1000), vec![text, rdata]);
        let a = Analysis::compute(&p);
        let out = run_tsv(&p, &a, &Overlay::default(), "0x1000/").unwrap();
        assert!(
            out.contains(
                "	unchecked
"
            ),
            "{out}"
        );
    }

    /// Generated inputs are typed by the signature and the same for the same
    /// seed, and a parameter a run cannot pass is refused.
    ///
    /// # Panics
    ///
    /// When an input has another shape, a repeat differs, or a floating
    /// parameter is taken.
    #[test]
    fn generated_inputs_follow_the_signature_and_the_seed() {
        let kinds = [Kind::Int(8, true), Kind::Pointer, Kind::Int(32, false)];
        let one = generated(&kinds, 16, 7, 0x1000).unwrap();
        assert_eq!(one, generated(&kinds, 16, 7, 0x1000).unwrap());
        assert_ne!(one, generated(&kinds, 16, 8, 0x1000).unwrap());
        for input in &one {
            let [Arg::Int(a), b, Arg::Int(c)] = input.as_slice() else {
                panic!("{input:?}")
            };
            assert!(*a < 0x80 || *a >= 0xffff_ffff_ffff_ff80, "{a:#x}");
            assert!(matches!(b, Arg::Bytes(v) if v.len() == 64) || *b == Arg::Out(64));
            assert!(*c <= 0xffff_ffff);
        }
        assert!(generated(&[Kind::Float], 1, 7, 0x1000).is_err());
    }

    /// A run of a function that returns its argument tabulates each input,
    /// and the same request answers the same.
    ///
    /// # Panics
    ///
    /// When a row is missing or a repeat answers otherwise.
    #[test]
    fn a_run_tabulates_and_repeats() {
        let p = Program::raw_x64(&[0x48, 0x89, 0xc8, 0xc3]);
        let a = Analysis::compute(&p);
        let o = Overlay::default();
        let out = run_tsv(&p, &a, &o, "0x1000/5;0x10").unwrap();
        assert!(out.contains("\n5\t5\treturned\t2\t-\t"), "{out}");
        assert!(out.contains("\n0x10\t0x10\treturned\t2\t-\t"), "{out}");
        assert_eq!(out, run_tsv(&p, &a, &o, "0x1000/5;0x10").unwrap());
    }
}
