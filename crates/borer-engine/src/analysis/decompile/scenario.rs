//! Scenario decompiles: a function under stated argument values, and a
//! dispatcher exploded into one row per behaviour.

use super::*;

/// Decompiles a function under a scenario: each parameter it names fixed
/// to a constant at the entry.
///
/// Every branch and switch on a fixed parameter folds, and what no path
/// reaches under the scenario is left out, so a dispatcher reads as the
/// one case it takes. The first line says the scenario and how many
/// blocks it cut: `// scenario: a2 = 2; 3 of 5 blocks cannot run`. A
/// parameter passed on the stack is not fixed, and the line says so.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Discovery results the function comes from.
/// * `overlay` - User names and comments.
/// * `entry` - The function's entry.
/// * `assume` - Parameter slots from 0 (`a1` is 0) and their values, as
///   [`parse_scenario`] reads them.
///
/// # Returns
///
/// The pseudo-C, or `None` when the function does not decompile.
#[must_use]
pub fn decompile_scenario(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    entry: u64,
    assume: &[(u8, u64)],
) -> Option<String> {
    let bitness = program.arch.bitness().unwrap_or(64);
    let registers = lift::conv(program, bitness).args.len();
    let d = decompile_with(program, analysis, overlay, entry, true, assume, false)?;
    let text = polish(&d.text, bitness, &analysis.packs);
    let said: Vec<String> = assume
        .iter()
        .map(|&(slot, v)| {
            let value = match i64::from_ne_bytes(v.to_ne_bytes()) {
                n if (-9..=9).contains(&n) => n.to_string(),
                n if n < 0 => format!("-{:#x}", n.unsigned_abs()),
                _ => format!("{v:#x}"),
            };
            let note = if usize::from(slot) < registers {
                ""
            } else {
                " (passed on the stack, not fixed)"
            };
            format!("a{} = {value}{note}", u32::from(slot) + 1)
        })
        .collect();
    Some(format!(
        "// scenario: {}; {} of {} blocks cannot run\n{text}",
        said.join(", "),
        d.cut,
        d.blocks
    ))
}

/// Most values one explosion runs a scenario for.
pub const EXPLODE_MAX: usize = 4096;

/// What a function does for the values of one parameter that behave
/// alike: an exploded scenario's row.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ScenarioCase {
    /// The values, in order.
    pub values: Vec<u64>,
    /// Blocks that can run under them.
    pub kept: usize,
    /// Blocks in the function.
    pub blocks: usize,
    /// The functions called, in text order, each once.
    pub calls: Vec<String>,
    /// What the function returns under them, each distinct `return` once.
    pub returns: Vec<String>,
}

/// Runs a scenario for each value of one parameter, grouping the alike.
///
/// Values behave alike when they keep the same blocks, make the same calls
/// and return the same things, so a dispatcher on the parameter reads as a
/// table of what each command does.
///
/// # Arguments
///
/// * `program` - The loaded image.
/// * `analysis` - Discovery results the function comes from.
/// * `overlay` - User names and comments.
/// * `entry` - The function's entry.
/// * `slot` - The parameter, from 0.
/// * `values` - The values to try, at most [`EXPLODE_MAX`].
///
/// # Returns
///
/// A row per behaviour, in the order its first value was tried.
#[must_use]
pub fn explode(
    program: &Program,
    analysis: &Analysis,
    overlay: &Overlay,
    entry: u64,
    slot: u8,
    values: &[u64],
) -> Vec<ScenarioCase> {
    let bitness = program.arch.bitness().unwrap_or(64);
    let mut out: Vec<ScenarioCase> = Vec::new();
    for &value in values.iter().take(EXPLODE_MAX) {
        let Some(d) = decompile_with(
            program,
            analysis,
            overlay,
            entry,
            true,
            &[(slot, value)],
            false,
        ) else {
            continue;
        };
        let text = polish(&d.text, bitness, &analysis.packs);
        let mut calls: Vec<String> = Vec::new();
        for c in crate::analysis::schema::calls_in_order(&blank_strings(&text)) {
            if !calls.contains(&c.callee) {
                calls.push(c.callee);
            }
        }
        let mut returns: Vec<String> = Vec::new();
        for line in text.lines().map(str::trim) {
            if let Some(r) = line
                .strip_prefix("return")
                .map(|r| r.trim().trim_end_matches(';'))
                && (line == "return;" || line.starts_with("return "))
            {
                let r = if r.is_empty() { "(nothing)" } else { r };
                if !returns.iter().any(|x| x == r) {
                    returns.push(r.to_owned());
                }
            }
        }
        let kept = d.blocks.saturating_sub(d.cut);
        match out
            .iter_mut()
            .find(|c| c.kept == kept && c.calls == calls && c.returns == returns)
        {
            Some(c) => c.values.push(value),
            None => out.push(ScenarioCase {
                values: vec![value],
                kept,
                blocks: d.blocks,
                calls,
                returns,
            }),
        }
    }
    out
}

/// The text with every string literal's contents blanked, so a call's
/// name inside a message (`"Foo::Bar(): failed"`) is not read as a call.
///
/// # Arguments
///
/// * `text` - The pseudo-C.
pub(super) fn blank_strings(text: &str) -> String {
    let mut out = String::with_capacity(text.len());
    let mut inside = false;
    let mut escaped = false;
    for c in text.chars() {
        if inside {
            if escaped {
                escaped = false;
            } else if c == '\\' {
                escaped = true;
            } else if c == '"' {
                inside = false;
                out.push(c);
            }
            continue;
        }
        if c == '"' {
            inside = true;
        }
        out.push(c);
    }
    out
}

/// Writes values compactly: runs of consecutive ones as `a-b`.
///
/// # Arguments
///
/// * `values` - The values, ascending within each run.
pub(super) fn value_runs(values: &[u64]) -> String {
    let mut parts: Vec<String> = Vec::new();
    let mut i = 0;
    while let Some(&start) = values.get(i) {
        let mut end = start;
        while values
            .get(i + 1)
            .is_some_and(|&n| Some(n) == end.checked_add(1))
        {
            i += 1;
            end = values.get(i).copied().unwrap_or(end);
        }
        let show = |v: u64| {
            if v < 10 {
                v.to_string()
            } else {
                format!("{v:#x}")
            }
        };
        parts.push(if start == end {
            show(start)
        } else {
            format!("{}-{}", show(start), show(end))
        });
        i += 1;
    }
    parts.join(",")
}

/// An exploded scenario as a table: a `#` summary, then a row per
/// behaviour with its values, blocks kept, calls and returns.
///
/// # Arguments
///
/// * `cases` - What [`explode`] found.
/// * `slot` - The parameter, from 0.
/// * `tried` - How many values were tried.
#[must_use]
pub fn explode_tsv(cases: &[ScenarioCase], slot: u8, tried: usize) -> String {
    let blocks = cases.first().map_or(0, |c| c.blocks);
    let mut out = format!(
        "# a{} over {tried} values: {} behaviours in a function of {blocks} blocks\n",
        u32::from(slot) + 1,
        cases.len()
    );
    out.push_str("values\tkept\tcalls\treturns\n");
    for c in cases {
        let calls = if c.calls.is_empty() {
            "-".to_owned()
        } else {
            c.calls.join(", ")
        };
        let returns = if c.returns.is_empty() {
            "-".to_owned()
        } else {
            c.returns.join(" | ")
        };
        let _ = writeln!(
            out,
            "{}\t{}\t{calls}\t{returns}",
            value_runs(&c.values),
            c.kept
        );
    }
    out
}

/// Reads the values an explosion tries: `a2=0..16` (the end excluded),
/// `a2=1|5|0x20`.
///
/// # Arguments
///
/// * `spec` - One parameter and its values.
///
/// # Returns
///
/// The parameter slot from 0 and the values, at most [`EXPLODE_MAX`].
///
/// # Errors
///
/// When the spec does not read, or asks for more than [`EXPLODE_MAX`]
/// values.
pub fn parse_explosion(spec: &str) -> Result<(u8, Vec<u64>), String> {
    let (name, values) = spec
        .split_once('=')
        .ok_or_else(|| format!("`{spec}` is not a<n>=<from>..<to> or a<n>=<v>|<v>"))?;
    let one = |v: &str| -> Result<u64, String> {
        let pairs = parse_scenario(&format!("{}={}", name.trim(), v.trim()))?;
        pairs
            .first()
            .map(|&(_, v)| v)
            .ok_or_else(|| format!("`{v}` is not a number"))
    };
    let slot = parse_scenario(&format!("{}=0", name.trim()))?
        .first()
        .map_or(0, |&(s, _)| s);
    let out: Vec<u64> = if let Some((from, to)) = values.split_once("..") {
        let (from, to) = (one(from)?, one(to)?);
        if to.saturating_sub(from) > EXPLODE_MAX as u64 {
            return Err(format!("at most {EXPLODE_MAX} values at a time"));
        }
        (from..to).collect()
    } else {
        values.split('|').map(one).collect::<Result<_, _>>()?
    };
    if out.is_empty() || out.len() > EXPLODE_MAX {
        return Err(format!("between 1 and {EXPLODE_MAX} values"));
    }
    Ok((slot, out))
}

/// Reads a scenario: `a2=5`, `a1=0x10,a3=-1`.
///
/// # Arguments
///
/// * `spec` - Comma-separated `a<n>=<value>` pairs, values decimal or hex,
///   negative ones in two's complement.
///
/// # Returns
///
/// Parameter slots from 0 and their values.
///
/// # Errors
///
/// When a pair does not read, names no parameter, or there is none.
pub fn parse_scenario(spec: &str) -> Result<Vec<(u8, u64)>, String> {
    let out: Vec<(u8, u64)> = spec
        .split(',')
        .map(str::trim)
        .filter(|p| !p.is_empty())
        .map(|part| {
            let (name, value) = part
                .split_once('=')
                .ok_or_else(|| format!("`{part}` is not a<n>=<value>"))?;
            let n: u8 = name
                .trim()
                .strip_prefix('a')
                .and_then(|d| d.parse().ok())
                .filter(|n| *n >= 1)
                .ok_or_else(|| format!("`{}` is not a parameter (a1, a2, ...)", name.trim()))?;
            let value = value.trim();
            let (negative, digits) = value
                .strip_prefix('-')
                .map_or((false, value), |rest| (true, rest));
            let v = digits
                .strip_prefix("0x")
                .or_else(|| digits.strip_prefix("0X"))
                .map_or_else(
                    || digits.parse::<u64>().ok(),
                    |h| u64::from_str_radix(h, 16).ok(),
                )
                .ok_or_else(|| format!("`{value}` is not a number"))?;
            Ok((n - 1, if negative { v.wrapping_neg() } else { v }))
        })
        .collect::<Result<_, String>>()?;
    if out.is_empty() {
        return Err("a scenario fixes at least one parameter, such as a2=5".to_owned());
    }
    Ok(out)
}
