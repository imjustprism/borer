//! Byte-counting loops rendered as the `strlen` or `wcslen` they compile
//! from.

use super::*;

/// Renders byte-counting loops as the `strlen` they compile from.
///
/// `v |= -1; do { v += 1; } while (*(uint8_t*)(b + v) != 0);` walks `b`
/// from its first byte to its terminator and leaves the length in `v`, so
/// it becomes `v = strlen(b);`; over `uint16_t` elements it is `wcslen`.
/// The seed may sit a few lines above the loop as long as nothing between
/// mentions `v` or opens a block.
///
/// # Arguments
///
/// * `lines` - The body, edited in place.
///
/// # Returns
///
/// Whether a loop was replaced.
pub(super) fn strlen_loops(lines: &mut Vec<String>) -> bool {
    let mut changed = false;
    let mut i = 0;
    while i + 2 < lines.len() {
        let Some(found) = strlen_while_at(lines, i).or_else(|| strlen_at(lines, i)) else {
            i += 1;
            continue;
        };
        let pad = pad_of(&lines[i]).to_owned();
        let StrlenLoop {
            seed,
            var,
            base,
            width,
            brk,
        } = found;
        let mut with = vec![format!("{pad}{var} = {}({base});", width.call())];
        let end = match brk {
            Some(brk) => {
                with.extend(
                    lines
                        .get(i + 3..brk)
                        .unwrap_or_default()
                        .iter()
                        .map(|l| format!("{pad}{}", l.trim())),
                );
                brk + 1
            }
            None => i + 2,
        };
        lines.splice(i..=end, with);
        lines.remove(seed);
        changed = true;
    }
    changed
}

/// The width of the characters a byte-counting loop walks.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum CharWidth {
    /// Bytes: `strlen`.
    Narrow,
    /// 16-bit elements: `wcslen`.
    Wide,
}

impl CharWidth {
    /// The library call that counts characters of this width.
    fn call(self) -> &'static str {
        match self {
            CharWidth::Narrow => "strlen",
            CharWidth::Wide => "wcslen",
        }
    }
}

/// A byte-counting loop read off the text, and the lines it spans.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct StrlenLoop {
    /// Index of the line seeding the counter with `-1`.
    seed: usize,
    /// The counter.
    var: String,
    /// The buffer walked.
    base: String,
    /// The width of its characters.
    width: CharWidth,
    /// Index of the `break;` leaving the `while (1)` form; `None` for the
    /// `do { } while` form, which spans three lines.
    brk: Option<usize>,
}

/// A `strlen` loop the structurer closed as `while (1)`, with the line of
/// its `break`.
///
/// When the code after the loop is only reached from it, the exit folds
/// into the body: `while (1) { v += 1; if (*(uint8_t*)(b + v) != 0)
/// continue; x = v; break; }`. The statements between the test and the
/// `break` run once, after the count, and must not open a block.
///
/// # Arguments
///
/// * `lines` - The body.
/// * `i` - Index of a `while (1) {` line.
pub(super) fn strlen_while_at(lines: &[String], i: usize) -> Option<StrlenLoop> {
    /// Most statements between the test and the `break`.
    const TAIL_MAX: usize = 4;
    if lines.get(i)?.trim() != "while (1) {" {
        return None;
    }
    let ind = indent_of(lines.get(i)?);
    let var = lines.get(i + 1)?.trim().strip_suffix(" += 1;")?;
    if !is_ident(var) {
        return None;
    }
    let cond = lines
        .get(i + 2)?
        .trim()
        .strip_prefix("if (")?
        .strip_suffix(" != 0) continue;")?;
    let (base, width) = strlen_operand(cond, var)?;
    let brk = (i + 3..(i + 4 + TAIL_MAX).min(lines.len())).find(|&k| {
        lines
            .get(k)
            .is_some_and(|l| l.trim() == "break;" && indent_of(l) == ind + 2)
    })?;
    let plain = lines.get(i + 3..brk)?.iter().all(|l| {
        let t = l.trim();
        indent_of(l) == ind + 2
            && !t.contains(['{', '}'])
            && !t.ends_with(':')
            && !starts_with_keyword(t, "continue")
            && !is_return(t)
            && !starts_with_keyword(t, "goto")
    });
    let closes = lines
        .get(brk + 1)
        .is_some_and(|l| l.trim() == "}" && indent_of(l) == ind);
    if !(plain && closes) {
        return None;
    }
    let seed = strlen_seed(lines, i, var)?;
    Some(StrlenLoop {
        seed,
        var: var.to_owned(),
        base,
        width,
        brk: Some(brk),
    })
}

/// The buffer a byte or 16-bit element test reads at `var`, and the width
/// of its characters.
///
/// `*(uint8_t*)(b + v)` or `*(uint8_t*)(v + b)` reads byte `v` of `b`;
/// `((uint16_t*)b)[v]` reads element `v` of a wide string.
///
/// # Arguments
///
/// * `cond` - The tested expression.
/// * `var` - The counter.
pub(super) fn strlen_operand(cond: &str, var: &str) -> Option<(String, CharWidth)> {
    let (base, width) = if let Some(addr) = cond
        .strip_prefix("*(uint8_t*)(")
        .and_then(|r| r.strip_suffix(')'))
    {
        (
            addr.strip_suffix(&format!(" + {var}"))
                .or_else(|| addr.strip_prefix(&format!("{var} + ")))?,
            CharWidth::Narrow,
        )
    } else if let Some(addr) = cond
        .strip_prefix("((uint16_t*)")
        .and_then(|r| r.strip_suffix(&format!(")[{var}]")))
    {
        (addr, CharWidth::Wide)
    } else {
        return None;
    };
    let mut depth = 0i32;
    for c in base.chars() {
        depth += match c {
            '(' => 1,
            ')' => -1,
            _ => 0,
        };
        if depth < 0 {
            return None;
        }
    }
    (depth == 0 && !base.is_empty() && !mentions_ident(base, var)).then(|| (base.to_owned(), width))
}

/// The line that seeds a `strlen` counter with `-1` a few lines above `i`,
/// with nothing between that mentions the counter or opens a block.
///
/// # Arguments
///
/// * `lines` - The body.
/// * `i` - Index of the loop's first line.
/// * `var` - The counter.
pub(super) fn strlen_seed(lines: &[String], i: usize, var: &str) -> Option<usize> {
    let seeds = [
        format!("{var} |= -1;"),
        format!("{var} = -1;"),
        format!("{var} = 0xffffffff;"),
    ];
    let mut k = i;
    while k > 0 && i - k < 4 {
        k -= 1;
        let t = lines[k].trim();
        if seeds.iter().any(|s| s == t) {
            return Some(k);
        }
        if mentions_ident(t, var) || t.contains('{') || t.contains('}') || t.ends_with(':') {
            return None;
        }
    }
    None
}

/// A `strlen` loop in `do { } while` form opening at `i`.
///
/// # Arguments
///
/// * `lines` - The body.
/// * `i` - Index of a `do {` line.
pub(super) fn strlen_at(lines: &[String], i: usize) -> Option<StrlenLoop> {
    if lines.get(i)?.trim() != "do {" {
        return None;
    }
    let var = lines.get(i + 1)?.trim().strip_suffix(" += 1;")?;
    if !is_ident(var) {
        return None;
    }
    let cond = lines
        .get(i + 2)?
        .trim()
        .strip_prefix("} while (")?
        .strip_suffix(" != 0);")?;
    let (base, width) = strlen_operand(cond, var)?;
    let seed = strlen_seed(lines, i, var)?;
    Some(StrlenLoop {
        seed,
        var: var.to_owned(),
        base,
        width,
        brk: None,
    })
}
