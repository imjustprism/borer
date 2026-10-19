//! Reading a run's spec: the function, its arguments as the reader writes
//! them (integers, strings, buffers), and where each lands.

use super::{ARGS_MAX, Arg, BUDGET, BUDGET_MAX, BUFFER_MAX, INPUTS_MAX};
use crate::analysis::render::*;
use crate::text::one_line;

/// A parsed run request: the function, the budget, and the inputs.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct RunSpec {
    /// The function's entry.
    pub(super) entry: u64,
    /// Steps each run is given.
    pub(super) budget: usize,
    /// The inputs, each its arguments in order.
    pub(super) inputs: Vec<Vec<Arg>>,
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
pub(super) fn integer(t: &str) -> Option<u64> {
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
pub(super) fn argument(t: &str) -> Result<Arg, String> {
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
pub(super) fn parse_run(a: &Analysis, o: &Overlay, spec: &str) -> Result<RunSpec, String> {
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
