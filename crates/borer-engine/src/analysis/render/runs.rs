//! Typed runs: a function called on the inputs a reader names, in the
//! emulator, and its answer checked against the function's printed text.

use super::oracle::compared_constants;
use super::*;
use crate::analysis::decompile::interp::{End, Script, TextRun};
use crate::analysis::decompile::signature::{Kind, Passing, Signature, passing, printed};
use crate::analysis::decompile::{decompile_named, traces, verify};
use crate::emulate::a64::Machine as A64Machine;
use crate::emulate::calls::ApiCall;
use crate::isa::Isa;
use crate::text::one_line;

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

/// Bytes of a buffer a report spells before the rest are counted.
const SHOWN_MAX: usize = 48;

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

/// A parsed run request: the function, the budget, and the inputs.
#[derive(Debug, Clone, PartialEq, Eq)]
struct RunSpec {
    /// The function's entry.
    entry: u64,
    /// Steps each run is given.
    budget: usize,
    /// The inputs, each its arguments in order.
    inputs: Vec<Vec<Arg>>,
}

/// Splits text at a separator outside double quotes, a backslash escaping
/// the character after it inside them.
///
/// # Arguments
///
/// * `text` - The text.
/// * `sep` - The separator.
fn split_unquoted(text: &str, sep: char) -> Vec<&str> {
    let mut out = Vec::new();
    let (mut quoted, mut escaped, mut from) = (false, false, 0);
    for (k, c) in text.char_indices() {
        if escaped {
            escaped = false;
        } else if quoted && c == '\\' {
            escaped = true;
        } else if c == '"' {
            quoted = !quoted;
        } else if c == sep && !quoted {
            out.push(&text[from..k]);
            from = k + c.len_utf8();
        }
    }
    out.push(&text[from..]);
    out
}

/// Reads a quoted text argument's bytes, its terminating zero added.
///
/// # Arguments
///
/// * `body` - The text between the quotes.
///
/// # Errors
///
/// A bad escape.
fn text_bytes(body: &str) -> Result<Vec<u8>, String> {
    let mut out = Vec::with_capacity(body.len() + 1);
    let mut chars = body.chars();
    while let Some(c) = chars.next() {
        if c != '\\' {
            let mut buf = [0u8; 4];
            out.extend_from_slice(c.encode_utf8(&mut buf).as_bytes());
            continue;
        }
        let e = chars.next().ok_or("a text argument ends in a backslash")?;
        out.push(match e {
            'n' => b'\n',
            'r' => b'\r',
            't' => b'\t',
            '0' => 0,
            '\\' => b'\\',
            '"' => b'"',
            'x' => {
                let h: String = chars.by_ref().take(2).collect();
                u8::from_str_radix(&h, 16).map_err(|_| format!("\\x{h} is not two hex digits"))?
            }
            other => {
                return Err(format!(
                    "\\{other} is no escape; use \\n \\r \\t \\0 \\\\ \\\" or \\xNN"
                ));
            }
        });
    }
    out.push(0);
    Ok(out)
}

/// Reads an integer argument: decimal or `0x`-hex, negative ones in two's
/// complement.
///
/// # Arguments
///
/// * `t` - The token.
fn integer(t: &str) -> Option<u64> {
    let (negative, digits) = t.strip_prefix('-').map_or((false, t), |d| (true, d));
    let v = match digits
        .strip_prefix("0x")
        .or_else(|| digits.strip_prefix("0X"))
    {
        Some(h) => u64::from_str_radix(h, 16).ok()?,
        None => digits.parse::<u64>().ok()?,
    };
    Some(if negative { v.wrapping_neg() } else { v })
}

/// Reads one argument.
///
/// # Arguments
///
/// * `t` - The argument as written.
///
/// # Errors
///
/// When it is none of the forms, or a buffer is past [`BUFFER_MAX`].
fn argument(t: &str) -> Result<Arg, String> {
    let t = t.trim();
    let arg = if let Some(body) = t.strip_prefix('"').and_then(|r| r.strip_suffix('"')) {
        Arg::Bytes(text_bytes(body)?)
    } else if let Some(h) = t.strip_prefix("hex:") {
        Arg::Bytes(
            parse_hex_bytes(h)
                .ok_or_else(|| format!("{}: hex: takes pairs of hex digits", one_line(t)))?,
        )
    } else if let Some(n) = t.strip_prefix("out:") {
        Arg::Out(parse_count(n).ok_or_else(|| format!("{}: out: takes a size", one_line(t)))?)
    } else {
        Arg::Int(integer(t).ok_or_else(|| {
            format!(
                "cannot read the argument {}; use a number, \"text\", hex:<bytes> or out:<size>",
                one_line(t)
            )
        })?)
    };
    let len = match &arg {
        Arg::Int(_) => 0,
        Arg::Bytes(b) => b.len(),
        Arg::Out(n) => *n,
    };
    if len > BUFFER_MAX {
        return Err(format!(
            "{}: a buffer is at most {BUFFER_MAX:#x} bytes",
            one_line(t)
        ));
    }
    Ok(arg)
}

/// Reads a run request: `<function>[,steps=N]/<input>[;<input>...]`, each
/// input its arguments in order, separated by commas.
///
/// # Arguments
///
/// * `a` - The analysis, to resolve the function.
/// * `o` - User names.
/// * `spec` - The request.
///
/// # Errors
///
/// When the function does not resolve, a part follows `steps=N` (it was
/// dropped unread), or an input does not read.
fn parse_run(a: &Analysis, o: &Overlay, spec: &str) -> Result<RunSpec, String> {
    let (head, inputs) = spec
        .split_once('/')
        .ok_or("run takes <function>[,steps=N]/<input>[;<input>...]")?;
    let (target, mut rest) = spec_head(head);
    let start = locate(a, o, target).ok_or_else(|| unresolved(target))?;
    let entry = a
        .function_at(start)
        .ok_or_else(|| format!("no function contains {start:#x}"))?
        .entry;
    let mut budget = BUDGET;
    if let Some(option) = rest.next().map(str::trim) {
        let n = option
            .strip_prefix("steps=")
            .and_then(parse_count)
            .ok_or_else(|| format!("cannot read {}; use steps=N", one_line(option)))?;
        if n == 0 || n > BUDGET_MAX {
            return Err(format!("steps is 1 to {BUDGET_MAX}"));
        }
        budget = n;
    }
    if let Some(extra) = rest.next() {
        return Err(format!(
            "run takes <function>[,steps=N]/<input>[;<input>...]; {} is one part too many",
            crate::text::quoted(extra.trim())
        ));
    }
    let mut out = Vec::new();
    for set in split_unquoted(inputs, ';') {
        let args: Vec<Arg> = if set.trim().is_empty() {
            Vec::new()
        } else {
            split_unquoted(set, ',')
                .into_iter()
                .map(argument)
                .collect::<Result<_, _>>()?
        };
        if args.len() > ARGS_MAX {
            return Err(format!("an input passes at most {ARGS_MAX} arguments"));
        }
        out.push(args);
    }
    if out.len() > INPUTS_MAX {
        return Err(format!("at most {INPUTS_MAX} inputs a run"));
    }
    Ok(RunSpec {
        entry,
        budget,
        inputs: out,
    })
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
    if let (Some((Kind::Int(..) | Kind::Pointer, bits)), Some(text), Some(machine)) =
        (ret, returned, m.value)
        && text != machine
    {
        let stack = |v: u64| {
            v <= t.entry_sp.wrapping_add(STACK_ABOVE)
                && t.entry_sp - v.min(t.entry_sp) <= STACK_BELOW
        };
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
        if let Some(i) = text.iter().zip(after).position(|(x, y)| x != y) {
            let place = from_usize(i);
            let writer = t.writers.get(&addr.wrapping_add(place)).copied();
            let what = format!(
                "a{}[{i}] is {:#04x} after the text, {:#04x} after the binary{}",
                k + 1,
                text.get(i).copied().unwrap_or(0),
                after.get(i).copied().unwrap_or(0),
                if writer.is_some() {
                    ""
                } else {
                    "; no line of the text writes it"
                }
            );
            return Verdict::Differs(writer.unwrap_or(line), what);
        }
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
/// The binary's row says what it returned (at the declared width), how it
/// stopped, the steps, and what it left in each buffer it changed. The
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

/// One input's traced run, what a diff reports from.
struct DiffRun {
    /// How it ended, in words.
    stop: String,
    /// Steps taken.
    steps: usize,
    /// What it returned, `None` when it did not.
    value: Option<u64>,
    /// The traced instructions, in the order they ran.
    trace: Vec<String>,
    /// Each serviced call as `api(args) -> ret`, in order.
    call_lines: Vec<String>,
    /// What each changed buffer argument holds after, as
    /// [`buffer_writes`] leaves it.
    writes: Vec<(usize, Vec<u8>, usize)>,
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
            Some(Isa::X86 { .. }) | None => format!(
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
        let returns = x.value.map_or_else(|| "-".to_owned(), small_hex);
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
/// and the bytes, with what it wrote past the end; `-` for nothing.
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
            format!("a{}={}{tail}", k + 1, bytes_shown(b))
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
        "# api calls: showing {} of {total}, api(args) -> ret, by input",
        total.min(RUN_CALLS_SHOWN)
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

/// The seed the lifter's check runs from when a run differs, fixed so the
/// report is the same every time.
const VERIFY_SEED: u64 = 1;

/// The values a generated integer argument is drawn from besides random
/// ones: the edges a check compares against.
const EDGES: [u64; 12] = [
    0,
    1,
    2,
    7,
    0x10,
    0x7f,
    0x80,
    0xff,
    0x7fff_ffff,
    0x8000_0000,
    0xffff_ffff,
    u64::MAX,
];

/// Bytes a generated buffer argument holds.
const GENERATED_BUFFER: usize = 64;

/// Longest text a generated buffer argument holds before its zeros.
const GENERATED_TEXT: u64 = 40;

/// The characters a generated text is spelled with.
const GENERATED_CHARS: &[u8] = b"abcdefghijklmnopqrstuvwxyz0123456789 ,.-_/";

/// A value cut to a parameter's width and extended as its sign says.
///
/// # Arguments
///
/// * `v` - The value.
/// * `bits` - The parameter's width, 1 to 64.
/// * `signed` - Whether the parameter is signed.
fn cut(v: u64, bits: u8, signed: bool) -> u64 {
    let shift = 64 - u32::from(bits.clamp(1, 64));
    if signed {
        ((v << shift).cast_signed() >> shift).cast_unsigned()
    } else {
        (v << shift) >> shift
    }
}

/// Inputs generated for a function from the kinds of its parameters.
///
/// Each input is a pure function of the seed, the function's entry and the
/// input's position: an integer is an edge value, a small number, a small
/// negative one or a random word, cut to the parameter's width and extended
/// as its sign says; a pointer is a buffer of [`GENERATED_BUFFER`] bytes
/// holding a short text, random bytes, or zeros.
///
/// # Arguments
///
/// * `kinds` - The parameters' kinds, in order.
/// * `count` - How many inputs.
/// * `seed` - The seed.
/// * `entry` - The function's entry, stirred into the seed.
///
/// # Errors
///
/// When a parameter is floating, or of a type a run does not pass.
fn generated(kinds: &[Kind], count: usize, seed: u64, entry: u64) -> Result<Vec<Vec<Arg>>, String> {
    /// Stirs the seed, as `splitmix64` does.
    const GOLDEN: u64 = 0x9e37_79b9_7f4a_7c15;
    let mut out = Vec::with_capacity(count);
    for j in 0..count {
        let mut state = seed ^ entry.wrapping_mul(GOLDEN) ^ from_usize(j).wrapping_mul(GOLDEN << 1);
        let mut next = move || {
            state = state.wrapping_add(GOLDEN);
            let mut z = state;
            z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
            z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
            z ^ (z >> 31)
        };
        let mut input = Vec::with_capacity(kinds.len());
        for (k, kind) in kinds.iter().enumerate() {
            input.push(match *kind {
                Kind::Int(bits, signed) => {
                    let v = match next() % 4 {
                        0 => EDGES
                            .get(usize::try_from(next() % from_usize(EDGES.len())).unwrap_or(0))
                            .copied()
                            .unwrap_or(0),
                        1 => next() % 16,
                        2 => (next() % 16).wrapping_neg(),
                        _ => next(),
                    };
                    Arg::Int(cut(v, bits, signed))
                }
                Kind::Pointer => match next() % 3 {
                    0 => {
                        let mut b = vec![0u8; GENERATED_BUFFER];
                        for slot in b
                            .iter_mut()
                            .take(usize::try_from(next() % GENERATED_TEXT).unwrap_or(0))
                        {
                            let c = usize::try_from(next() % from_usize(GENERATED_CHARS.len()))
                                .unwrap_or(0);
                            *slot = GENERATED_CHARS.get(c).copied().unwrap_or(b'a');
                        }
                        Arg::Bytes(b)
                    }
                    1 => Arg::Bytes(
                        (0..GENERATED_BUFFER)
                            .map(|_| crate::num::lo8(next()))
                            .collect(),
                    ),
                    _ => Arg::Out(GENERATED_BUFFER),
                },
                Kind::Float => {
                    return Err(format!("a{} is floating, which a run does not pass", k + 1));
                }
                Kind::Other => {
                    return Err(format!("a{} is of a type a run does not pass", k + 1));
                }
            });
        }
        out.push(input);
    }
    Ok(out)
}

/// Checks a function's printed text against the binary on inputs generated
/// from its signature.
///
/// The text the tools print ([`decompile_named`]) runs as C on each input
/// beside the binary in the emulator, as [`run_tsv`] runs them, from inputs
/// that are a pure function of `seed` and the function ([`generated`]):
/// the same call answers the same.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `a` - The analysis.
/// * `o` - User names.
/// * `entry` - The function's entry.
/// * `count` - How many inputs.
/// * `seed` - The inputs' seed.
/// * `budget` - Steps each run is given, on either side.
///
/// # Returns
///
/// Each input's arguments as a report row spells them, with the text's
/// verdict on it.
///
/// # Errors
///
/// When the function does not decompile, its signature does not read, or a
/// parameter is of a type a run does not pass.
pub fn check_generated(
    p: &Program,
    a: &Analysis,
    o: &Overlay,
    entry: u64,
    count: usize,
    seed: u64,
    budget: usize,
) -> Result<Vec<(String, Verdict)>, String> {
    let text = decompile_named(p, a, o, entry).ok_or("the function does not decompile")?;
    let word = u8::try_from(p.arch.bitness().unwrap_or(64)).unwrap_or(64);
    let sig = printed(&text, word)?;
    let inputs = generated(&sig.parameter_kinds(), count, seed, entry)?;
    let shared = Shared {
        script: Script::read(p, a, o, entry, &text),
        sig: Ok(sig),
        pass: Some(passing(p, a, o, entry)),
    };
    Ok(inputs
        .iter()
        .map(|input| {
            let shown: Vec<String> = input.iter().map(Arg::shown).collect();
            let outcome = run_one(p, &shared, entry, input, budget);
            (shown.join(" "), outcome.verdict)
        })
        .collect())
}

/// Inputs a vector request runs unless its spec says how many.
const VECTORS: usize = 16;

/// The seed a vector request's generated inputs are drawn from, fixed so
/// the same request answers the same.
const VECTORS_SEED: u64 = 0x7e57_7ec7;

/// Vectors the harness asserts before the rest are left to the table.
const HARNESS_MAX: usize = 16;

/// The inputs of a vector request, each input once.
///
/// One per constant the function compares against, then inputs generated
/// from its signature ([`generated`]); twice as many are generated as are
/// needed, so a repeat dropped does not cut the count. A constant fills every integer parameter, cut to its width, and every
/// pointer parameter as a [`GENERATED_BUFFER`]-byte buffer opening with the
/// constant's little-endian bytes, so a check of a buffer's first word sees
/// the value it compares with. The constants take at most half the inputs.
///
/// # Arguments
///
/// * `kinds` - The parameters' kinds, in order.
/// * `constants` - The values the function compares against, in order.
/// * `count` - How many inputs.
/// * `entry` - The function's entry, which stirs the generated inputs.
///
/// # Errors
///
/// When a parameter is floating, or of a type a run does not pass.
fn vector_inputs(
    kinds: &[Kind],
    constants: &[u64],
    count: usize,
    entry: u64,
) -> Result<Vec<Vec<Arg>>, String> {
    let mut out: Vec<Vec<Arg>> = Vec::with_capacity(count);
    for &c in constants.iter().take(count.div_ceil(2)) {
        let mut input = Vec::with_capacity(kinds.len());
        for (k, kind) in kinds.iter().enumerate() {
            input.push(match *kind {
                Kind::Int(bits, signed) => Arg::Int(cut(c, bits, signed)),
                Kind::Pointer => {
                    let mut b = c.to_le_bytes().to_vec();
                    b.resize(GENERATED_BUFFER, 0);
                    Arg::Bytes(b)
                }
                Kind::Float => {
                    return Err(format!("a{} is floating, which a run does not pass", k + 1));
                }
                Kind::Other => {
                    return Err(format!("a{} is of a type a run does not pass", k + 1));
                }
            });
        }
        if !out.contains(&input) {
            out.push(input);
        }
    }
    for input in generated(kinds, count.saturating_mul(2), VECTORS_SEED, entry)? {
        if out.len() >= count {
            break;
        }
        if !out.contains(&input) {
            out.push(input);
        }
    }
    Ok(out)
}

/// The C type a harness declares a parameter or result of a kind as.
///
/// # Arguments
///
/// * `kind` - The kind.
fn c_type(kind: Kind) -> String {
    match kind {
        Kind::Int(bits, signed) => format!(
            "{}int{}_t",
            if signed { "" } else { "u" },
            bits.clamp(8, 64).next_power_of_two()
        ),
        Kind::Pointer => "uint8_t *".to_owned(),
        Kind::Float => "double".to_owned(),
        Kind::Other => "uint64_t".to_owned(),
    }
}

/// A function's name as a C identifier: its last `::` segment, every
/// character that cannot be in one made `_`.
///
/// # Arguments
///
/// * `name` - The name.
fn c_name(name: &str) -> String {
    let mut out: String = name
        .rsplit("::")
        .next()
        .unwrap_or(name)
        .chars()
        .map(|c| if c.is_ascii_alphanumeric() { c } else { '_' })
        .collect();
    if out.is_empty() || out.starts_with(|c: char| c.is_ascii_digit()) {
        out.insert(0, '_');
    }
    out
}

/// Bytes as a C array initializer, its trailing zeros left to the array's
/// size.
///
/// # Arguments
///
/// * `b` - The bytes.
fn c_bytes(b: &[u8]) -> String {
    let end = b.iter().rposition(|c| *c != 0).map_or(0, |i| i + 1);
    let body: Vec<String> = b
        .get(..end)
        .unwrap_or(b)
        .iter()
        .map(|c| format!("{c:#04x}"))
        .collect();
    if body.is_empty() {
        "{0}".to_owned()
    } else {
        format!("{{{}}}", body.join(", "))
    }
}

/// The C a harness opens with after its header comment: the includes, the
/// failure count and the two helpers each vector's line reports through.
const HARNESS_HEAD: &str = "#include <stdint.h>
#include <stdio.h>
#include <string.h>

static int failed;

/* Reports a vector whose result differs. */
static void differs(int vector, unsigned long long got, unsigned long long want) {
    printf(\"vector %d: returned %#llx, want %#llx\\n\", vector, got, want);
    failed++;
}

/* Reports a vector that left other bytes in a buffer. */
static void changed(int vector, int arg) {
    printf(\"vector %d: a%d holds other bytes\\n\", vector, arg);
    failed++;
}
";

/// Writes a C program asserting the vectors that returned, a line each:
/// the call's result at its declared width and the bytes it left in each
/// buffer it changed.
///
/// # Arguments
///
/// * `name` - The function's name, as a C identifier.
/// * `sig` - Its signature.
/// * `inputs` - Every input, in table order.
/// * `outcomes` - Each input's run.
fn harness(name: &str, sig: &Signature, inputs: &[Vec<Arg>], outcomes: &[Arc<Outcome>]) -> String {
    let kinds = sig.parameter_kinds();
    let ret = sig.return_kind();
    let params: Vec<String> = kinds
        .iter()
        .enumerate()
        .map(|(k, kind)| match kind {
            Kind::Pointer => format!("uint8_t *a{}", k + 1),
            Kind::Int(..) | Kind::Float | Kind::Other => format!("{} a{}", c_type(*kind), k + 1),
        })
        .collect();
    let params = if params.is_empty() {
        "void".to_owned()
    } else {
        params.join(", ")
    };
    let (ret_type, got) = match ret {
        None => ("void".to_owned(), None),
        Some((Kind::Int(bits, signed), _)) => (
            c_type(Kind::Int(bits, signed)),
            Some(if signed {
                format!("({})got", c_type(Kind::Int(bits, false)))
            } else {
                "got".to_owned()
            }),
        ),
        Some((kind @ (Kind::Pointer | Kind::Float | Kind::Other), _)) => (c_type(kind), None),
    };
    let returned: Vec<usize> = (0..outcomes.len())
        .filter(|&n| outcomes.get(n).is_some_and(|x| x.value.is_some()))
        .collect();
    let mut out = format!(
        "/* {} of the {} vectors that returned, for {}, as borer's emulator ran the binary.\n   Link with a reimplementation of {name}: the run prints each vector that differs and exits 1 if any did. */\n{HARNESS_HEAD}\n{ret_type} {name}({params});\n\nint main(void) {{\n",
        returned.len().min(HARNESS_MAX),
        returned.len(),
        sig.text
    );
    if got.is_none() && ret.is_some() {
        out.push_str("    /* the result is not an integer, so only the buffers are compared */\n");
    }
    for &n in returned.iter().take(HARNESS_MAX) {
        let (Some(input), Some(x)) = (inputs.get(n), outcomes.get(n)) else {
            continue;
        };
        let vector = n + 1;
        let mut line = String::from("    {");
        let mut args = Vec::with_capacity(input.len());
        for (k, arg) in input.iter().enumerate() {
            match arg {
                Arg::Int(v) => args.push(format!("{v:#x}")),
                Arg::Bytes(_) | Arg::Out(_) => {
                    let initial = arg.initial();
                    let _ = write!(
                        line,
                        " uint8_t b{}[{}] = {};",
                        k + 1,
                        initial.len().max(1),
                        c_bytes(&initial)
                    );
                    args.push(format!("b{}", k + 1));
                }
            }
        }
        let call = format!("{name}({})", args.join(", "));
        match (&got, x.value) {
            (Some(got), Some(v)) => {
                let _ = write!(
                    line,
                    " {ret_type} got = {call}; if ({got} != {v:#x}) differs({vector}, {got}, {v:#x});"
                );
            }
            (Some(_) | None, _) => {
                let _ = write!(line, " {call};");
            }
        }
        for (k, after, _) in &x.writes {
            let _ = write!(
                line,
                " static const uint8_t w{0}[{1}] = {2}; if (memcmp(b{0}, w{0}, sizeof w{0})) changed({vector}, {0});",
                k + 1,
                after.len().max(1),
                c_bytes(after)
            );
        }
        line.push_str(" }\n");
        out.push_str(&line);
    }
    out.push_str("    printf(\"%d vectors differ\\n\", failed);\n    return failed != 0;\n}\n");
    out
}

/// Records test vectors for reimplementing a function: inputs typed by
/// its recovered signature, each run in the emulator, and a C harness that
/// asserts what the binary answered.
///
/// The inputs open with the constants the function compares against (the
/// values `solve` tries, [`compared_constants`]), then ones generated from
/// the signature ([`generated`]), each a pure function of the function and
/// a fixed seed, so the same request answers the same, byte for byte. Each
/// runs as [`run_tsv`] runs it, through the same memo. The table gives a
/// row per input; the harness asserts the first [`HARNESS_MAX`] that
/// returned: the result at its declared width, and the bytes each changed
/// buffer holds after.
///
/// # Arguments
///
/// * `p` - The loaded image.
/// * `a` - The analysis.
/// * `o` - User names.
/// * `spec` - `<function>[,count=N][,steps=N]`: at most [`INPUTS_MAX`]
///   inputs, [`VECTORS`] by default.
///
/// # Returns
///
/// A header with the signature and the counts, the table, then the
/// harness under a `# harness` line.
///
/// # Errors
///
/// When the spec does not read, the function does not decompile or has no
/// signature, a parameter is of a type a run does not pass, or the code is
/// arm64.
pub fn vectors_tsv(p: &Program, a: &Analysis, o: &Overlay, spec: &str) -> Result<String, String> {
    x86_only(p, "vectors")?;
    let (target, rest) = spec_head(spec);
    let start = locate(a, o, target).ok_or_else(|| unresolved(target))?;
    let entry = a
        .function_at(start)
        .ok_or_else(|| format!("no function contains {start:#x}"))?
        .entry;
    let (mut count, mut budget) = (VECTORS, BUDGET);
    for option in rest.map(str::trim) {
        match option.split_once('=') {
            Some(("count", n)) => {
                count = parse_count(n)
                    .filter(|n| (1..=INPUTS_MAX).contains(n))
                    .ok_or_else(|| format!("count is 1 to {INPUTS_MAX}"))?;
            }
            Some(("steps", n)) => {
                budget = parse_count(n)
                    .filter(|n| (1..=BUDGET_MAX).contains(n))
                    .ok_or_else(|| format!("steps is 1 to {BUDGET_MAX}"))?;
            }
            _ => {
                return Err(format!(
                    "vectors takes <function>[,count=N][,steps=N]; cannot read {}",
                    one_line(option)
                ));
            }
        }
    }
    let text = decompile_named(p, a, o, entry).ok_or("the function does not decompile")?;
    let word = u8::try_from(p.arch.bitness().unwrap_or(64)).unwrap_or(64);
    let sig = printed(&text, word)?;
    let constants: Vec<u64> =
        compared_constants(&function_instructions(p, a, entry), Vec::new(), INPUTS_MAX)
            .iter()
            .map(|c| c.value)
            .collect();
    let inputs = vector_inputs(&sig.parameter_kinds(), &constants, count, entry)?;
    let seeded = constants.len().min(count.div_ceil(2));
    let shared = Shared {
        script: Script::read(p, a, o, entry, &text),
        pass: Some(passing(p, a, o, entry)),
        sig: Ok(sig.clone()),
    };
    let names = o.fingerprint();
    let outcomes: Vec<Arc<Outcome>> = inputs
        .iter()
        .map(|input| {
            a.derived.get_or_build_item(
                "fn_run",
                names,
                (entry, budget, input.clone()),
                || run_one(p, &shared, entry, input, budget),
                Outcome::bytes,
            )
        })
        .collect();
    let returned = outcomes.iter().filter(|x| x.value.is_some()).count();
    let mut out = format!(
        "# vectors for {}: {} input{} ({seeded} from the constants it compares, the rest generated from its signature), at most {budget} steps each; {returned} returned\n",
        sig.text,
        inputs.len(),
        plural(inputs.len())
    );
    out.push_str("# args\treturns\tstop\twrites\n");
    for (input, x) in inputs.iter().zip(&outcomes) {
        let _ = writeln!(
            out,
            "{}\t{}\t{}\t{}",
            args_shown(input),
            x.value.map_or_else(|| "-".to_owned(), small_hex),
            x.stop,
            writes_shown(x)
        );
    }
    out.push_str("# harness: C, asserting the vectors that returned\n");
    out.push_str(&harness(
        &c_name(&short_name(a, o, entry)),
        &sig,
        &inputs,
        &outcomes,
    ));
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::{
        Arg, Kind, args_shown, generated, parse_run, run_tsv, small_hex, vector_inputs, vectors_tsv,
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
