//! Loop recovery on the finished text: `while` and `for` from the guarded
//! `do`/`while` a compiler's loop inversion leaves, and `for` from a
//! counted `while`.

use super::ctext::{Ast, Bin, expression, named_type, tokens as c_tokens};
use super::*;

/// Lines the scan for a later write of a moved variable reads before it
/// gives up.
const DEAD_SCAN_MAX: usize = 200;

/// Rewrites the inverted and counted loops of a body as `while` and `for`.
///
/// A compiler tests a loop's condition once before entering it and then
/// at its bottom: `if (C) { do { B } while (C); }` is `while (C) { B }`.
/// When the guard is the condition with the loop variable's first value
/// put in (`if (p->list != 0) { v = p->list; do { B; v = *v; } while (v !=
/// 0); }`), the loop is `for (v = p->list; v != 0; v = *v) { B }`, and with
/// no step at the body's end it is `v = p->list; while (v != 0) { B }`;
/// either way `v` is assigned on the path that skipped the loop too, so
/// it must be dead there ([`dead_after`]); other first values set beside
/// `v` stay in front of the loop under the same rule, when neither the
/// condition nor `v`'s value reads them and they do not read `v`.
/// `v = k; while (C) { B; v += 1; }` is a `for` as it stands. A loop body
/// that continues at its own level
/// keeps its form when a `for` would run the step on the way to the test
/// where the `do` did not, and no rewrite takes a loop that holds a label.
///
/// # Arguments
///
/// * `lines` - The body lines, rewritten in place.
///
/// # Returns
///
/// Whether anything was rewritten.
pub(super) fn recover_loops(lines: &mut Vec<String>) -> bool {
    let mut changed = false;
    let mut k = 0;
    while k < lines.len() {
        if guarded_loop(lines, k)
            || positive_guarded_for(lines, k)
            || counted_do_const(lines, k)
            || counted_while(lines, k)
            || returning_while(lines, k)
            || exit_arm(lines, k)
        {
            changed = true;
            continue;
        }
        k += 1;
    }
    changed
}

/// Rewrites the `if (G) { inits; do { B } while (C); }` at line `k`.
///
/// # Arguments
///
/// * `lines` - The body lines.
/// * `k` - The line of the `if`.
///
/// # Returns
///
/// Whether the `if` was a guarded loop and became a `while` or a `for`.
fn guarded_loop(lines: &mut Vec<String>, k: usize) -> bool {
    let Some(open) = lines.get(k) else {
        return false;
    };
    let pad = indent_of(open);
    let Some(guard) = if_opener(open.trim()).map(str::to_owned) else {
        return false;
    };
    let inner = pad + 2;
    let Some(close) =
        closing(lines, k, pad).filter(|&c| lines.get(c).is_some_and(|l| l.trim() == "}"))
    else {
        return false;
    };
    let Some(latch) = close.checked_sub(1).filter(|&l| l > k) else {
        return false;
    };
    let Some(cond) = lines
        .get(latch)
        .filter(|l| indent_of(l) == inner)
        .and_then(|l| l.trim().strip_prefix("} while (")?.strip_suffix(");"))
        .map(str::to_owned)
    else {
        return false;
    };
    let Some(d) = (k + 1..latch)
        .rev()
        .find(|&j| {
            lines
                .get(j)
                .is_some_and(|l| indent_of(l) <= inner && !l.trim().is_empty())
        })
        .filter(|&j| {
            lines
                .get(j)
                .is_some_and(|l| l.trim() == "do {" && indent_of(l) == inner)
        })
    else {
        return false;
    };
    let region = lines.get(k + 1..close).unwrap_or(&[]);
    if region.iter().any(|l| is_label(l)) {
        return false;
    }
    let inits = lines.get(k + 1..d).unwrap_or(&[]);
    let body = lines.get(d + 1..latch).unwrap_or(&[]);
    let pad_s = " ".repeat(pad);
    let dedent = |l: &String| l.strip_prefix("  ").unwrap_or(l).to_owned();
    let rewritten: Vec<String> = match inits {
        [] if same_condition(&guard, &cond) => std::iter::once(format!("{pad_s}while ({cond}) {{"))
            .chain(body.iter().map(dedent))
            .chain(std::iter::once(format!("{pad_s}}}")))
            .collect(),
        [] => return false,
        inits => {
            let Some(parsed) = inits
                .iter()
                .map(|l| plain_assignment(l).filter(|(_, r)| indent_of(l) == inner && !impure(r)))
                .collect::<Option<Vec<(&str, &str)>>>()
            else {
                return false;
            };
            let Some(at) = parsed.iter().rposition(|(v, _)| mentions_ident(&cond, v)) else {
                return false;
            };
            let Some(&(v, value)) = parsed.get(at) else {
                return false;
            };
            let others: Vec<(&str, &str)> = parsed
                .iter()
                .enumerate()
                .filter(|(i, _)| *i != at)
                .map(|(_, p)| *p)
                .collect();
            let apart = others.iter().all(|(o, r)| {
                *o != v
                    && !mentions_ident(&cond, o)
                    && !mentions_ident(value, o)
                    && !mentions_ident(r, v)
                    && dead_after(lines, close + 1, pad, o)
            });
            if !apart
                || !same_condition(&guard, &rename_word(&cond, v, &format!("({value})")))
                || !dead_after(lines, close + 1, pad, v)
            {
                return false;
            }
            let front: Vec<String> = others
                .iter()
                .map(|(o, r)| format!("{pad_s}{o} = {r};"))
                .collect();
            let looped: Vec<String> = match step_of(body, inner + 2, v) {
                Some(step) => {
                    let head = format!("{pad_s}for ({v} = {value}; {cond}; {step}) {{");
                    std::iter::once(head)
                        .chain(body.get(..body.len() - 1).unwrap_or(&[]).iter().map(dedent))
                        .chain(std::iter::once(format!("{pad_s}}}")))
                        .collect()
                }
                None => [
                    format!("{pad_s}{v} = {value};"),
                    format!("{pad_s}while ({cond}) {{"),
                ]
                .into_iter()
                .chain(body.iter().map(dedent))
                .chain(std::iter::once(format!("{pad_s}}}")))
                .collect(),
            };
            front.into_iter().chain(looped).collect()
        }
    };
    lines.splice(k..=close, rewritten);
    true
}

/// Rewrites `if ((int32_t)n > 0) { v = 0; do { B; v += 1; } while ((uint32_t)n != v); }`
/// at line `k` as `for (v = 0; (int32_t)v < (int32_t)n; v += 1) { B }`.
///
/// # Arguments
///
/// * `lines` - The body lines.
/// * `k` - The line of the `if`.
///
/// # Returns
///
/// Whether the guarded loop became a `for`.
fn positive_guarded_for(lines: &mut Vec<String>, k: usize) -> bool {
    let Some(open) = lines.get(k) else {
        return false;
    };
    let pad = indent_of(open);
    let Some(guard) = if_opener(open.trim()) else {
        return false;
    };
    let Some(n) = guard
        .strip_prefix("(int32_t)")
        .and_then(|s| s.strip_suffix(" > 0"))
        .filter(|s| is_param_name(s) || is_register_name(s) || vars::is_var_name(s))
        .map(str::to_owned)
    else {
        return false;
    };
    let inner = pad + 2;
    let Some(close) =
        closing(lines, k, pad).filter(|&c| lines.get(c).is_some_and(|l| l.trim() == "}"))
    else {
        return false;
    };
    if close < k + 5 {
        return false;
    }
    let Some((v, "0")) = lines
        .get(k + 1)
        .filter(|l| indent_of(l) == inner)
        .and_then(|l| plain_assignment(l))
        .filter(|(lhs, _)| is_register_name(lhs) || vars::is_var_name(lhs))
    else {
        return false;
    };
    let v = v.to_owned();
    let do_ok = lines
        .get(k + 2)
        .is_some_and(|l| indent_of(l) == inner && l.trim() == "do {");
    let latch = close - 1;
    let Some(cond) = lines
        .get(latch)
        .filter(|_| do_ok)
        .filter(|l| indent_of(l) == inner)
        .and_then(|l| l.trim().strip_prefix("} while (")?.strip_suffix(");"))
        .map(str::to_owned)
    else {
        return false;
    };
    let matches_cond = [
        format!("(uint32_t){n} != {v}"),
        format!("{v} != (uint32_t){n}"),
    ]
    .contains(&cond);
    let region = lines.get(k + 1..close).unwrap_or(&[]);
    let body = lines.get(k + 3..latch).unwrap_or(&[]);
    if !matches_cond
        || v == n
        || region.iter().any(|l| is_label(l))
        || region
            .iter()
            .any(|l| l.contains(&format!("&{v}")) || l.contains(&format!("&{n}")))
        || assigned_values(region, &n) > 0
        || assigned_values(body, &v) != 1
        || continues_at_top(body)
        || breaks_at_top(body)
        || !dead_after(lines, close + 1, pad, &v)
    {
        return false;
    }
    let Some(raw_step) = step_of(body, inner + 2, &v) else {
        return false;
    };
    if raw_step != format!("{v} += 1") && raw_step != format!("{v} = {v} + 1") {
        return false;
    }
    let pad_s = " ".repeat(pad);
    let for_cond = format!("(int32_t){v} < (int32_t){n}");
    let dedent = |l: &String| l.strip_prefix("  ").unwrap_or(l).to_owned();
    let rewritten: Vec<String> =
        std::iter::once(format!("{pad_s}for ({v} = 0; {for_cond}; {v} += 1) {{"))
            .chain(body.get(..body.len() - 1).unwrap_or(&[]).iter().map(dedent))
            .chain(std::iter::once(format!("{pad_s}}}")))
            .collect();
    lines.splice(k..=close, rewritten);
    true
}

/// Rewrites `v = 0; do { B; step; } while (v != bound);` at line `k` as a `for`
/// loop.
///
/// Matches when `bound` is a non-zero positive constant and `step` increments
/// `v` by a positive constant at the end of the body.
///
/// # Arguments
///
/// * `lines` - The body lines.
/// * `k` - The line of the counter initialization.
///
/// # Returns
///
/// Whether the `do`/`while` loop became a `for`.
fn counted_do_const(lines: &mut Vec<String>, k: usize) -> bool {
    let (Some(init), Some(head)) = (lines.get(k), lines.get(k + 1)) else {
        return false;
    };
    let pad = indent_of(init);
    if pad != 0 || indent_of(head) != pad || head.trim() != "do {" {
        return false;
    }
    let Some((v, start)) =
        plain_assignment(init).filter(|(lhs, _)| is_register_name(lhs) || vars::is_var_name(lhs))
    else {
        return false;
    };
    let start_val = parse_const(start);
    let start_addr = start.starts_with('&') && is_ident(start.get(1..).unwrap_or(""));
    if start_val.is_none() && !start_addr {
        return false;
    }
    let v = v.to_owned();
    let start = start.to_owned();
    let Some(latch) = closing(lines, k + 1, pad) else {
        return false;
    };
    let Some(cond) = lines
        .get(latch)
        .and_then(|l| l.trim().strip_prefix("} while (")?.strip_suffix(");"))
        .map(str::to_owned)
    else {
        return false;
    };
    let Some(bound_val) = cond
        .strip_prefix(&format!("{v} != "))
        .or_else(|| cond.strip_prefix(&format!("(uint32_t){v} != ")))
        .and_then(parse_const)
    else {
        return false;
    };
    let bound_ok = bound_val > 0 && (bound_val & 0xffff_ffff) != 0;
    let body = lines.get(k + 2..latch).unwrap_or(&[]);
    if !bound_ok
        || body.is_empty()
        || body
            .iter()
            .any(|l| is_label(l) || l.contains(&format!("&{v}")))
        || assigned_values(body, &v) != 1
        || continues_at_top(body)
        || breaks_at_top(body)
    {
        return false;
    }
    let Some((step_idx, inc, inc_val)) = find_do_const_step(body, pad, &v) else {
        return false;
    };
    let start_ok = match start_val {
        Some(0) => true,
        Some(sv) => {
            sv >= 0x1000 && bound_val > sv && (bound_val - sv) % inc_val == 0 && inc_val == 4
        }
        None => start_addr && inc_val == 4,
    };
    if !start_ok {
        return false;
    }
    let pad_s = " ".repeat(pad);
    let mut rewritten = vec![format!(
        "{pad_s}for ({v} = {start}; {cond}; {v} += {inc}) {{"
    )];
    for (idx, line) in body.iter().enumerate() {
        if idx != step_idx {
            rewritten.push(line.clone());
        }
    }
    rewritten.push(format!("{pad_s}}}"));
    lines.splice(k..=latch, rewritten);
    true
}

/// Finds the trailing positive-constant step of `v` in a `do` loop body.
fn find_do_const_step(body: &[String], pad: usize, v: &str) -> Option<(usize, String, u64)> {
    (body.len().saturating_sub(2)..body.len())
        .rev()
        .find_map(|idx| {
            let l = body.get(idx)?;
            if indent_of(l) != pad + 2 {
                return None;
            }
            if idx + 1 < body.len() {
                let tail = body.last()?;
                let tail_lhs = plain_assignment(tail)
                    .or_else(|| tail.trim().strip_suffix(';')?.split_once(" += "))
                    .map(|(lhs, _)| lhs);
                let tail_ok = indent_of(tail) == pad + 2
                    && !mentions_ident(tail, v)
                    && !impure(tail)
                    && tail_lhs.is_some_and(|lhs| is_register_name(lhs) || vars::is_var_name(lhs));
                if !tail_ok {
                    return None;
                }
            }
            let s = l.trim().strip_suffix(';')?;
            let inc = s
                .strip_prefix(&format!("{v} += "))
                .or_else(|| s.strip_prefix(&format!("{v} = {v} + ")))?;
            let inc_val = parse_const(inc).filter(|&c| c > 0)?;
            Some((idx, inc.to_owned(), inc_val))
        })
}

/// Rewrites the `v = init; while (C) { B; step }` at line `k` as a `for`.
///
/// # Arguments
///
/// * `lines` - The body lines.
/// * `k` - The line of the assignment.
///
/// # Returns
///
/// Whether the loop became a `for`.
fn counted_while(lines: &mut Vec<String>, k: usize) -> bool {
    let (Some(init), Some(head)) = (lines.get(k), lines.get(k + 1)) else {
        return false;
    };
    let pad = indent_of(init);
    let Some((lhs_chain, value)) = init
        .trim()
        .strip_suffix(';')
        .and_then(|s| s.rsplit_once(" = "))
    else {
        return false;
    };
    let (prefix, v) = match lhs_chain.rsplit_once(" = ") {
        Some((p, v)) => (Some(p.trim().to_owned()), v.trim().to_owned()),
        None => (None, lhs_chain.trim().to_owned()),
    };
    let value = value.trim().to_owned();
    if !is_ident(&v)
        || impure(&value)
        || prefix.as_ref().is_some_and(|p| {
            !p.split(" = ")
                .all(|lhs| is_ident(lhs) && !mentions_ident(&value, lhs))
                || mentions_ident(&value, &v)
        })
    {
        return false;
    }
    let Some(cond) = head
        .trim()
        .strip_prefix("while (")
        .and_then(|r| r.strip_suffix(") {"))
        .filter(|c| indent_of(head) == pad && mentions_ident(c, &v))
        .map(str::to_owned)
    else {
        return false;
    };
    let Some(close) = closing(lines, k + 1, pad) else {
        return false;
    };
    if lines.get(close).is_none_or(|l| l.trim() != "}") {
        return false;
    }
    let body = lines.get(k + 2..close).unwrap_or(&[]);
    if body.iter().any(|l| is_label(l)) {
        return false;
    }
    let Some(step) = step_of(body, pad + 2, &v).map(str::to_owned) else {
        return false;
    };
    let pad_s = " ".repeat(pad);
    let mut rewritten: Vec<String> = Vec::new();
    if let Some(p) = prefix {
        rewritten.push(format!("{pad_s}{p} = {value};"));
    }
    rewritten.push(format!("{pad_s}for ({v} = {value}; {cond}; {step}) {{"));
    rewritten.extend(body.get(..body.len() - 1).unwrap_or(&[]).iter().cloned());
    rewritten.push(format!("{pad_s}}}"));
    lines.splice(k..=close, rewritten);
    true
}

/// Rewrites a two-return counted `while (1)` at line `k` as a `for` loop.
///
/// The counter initialized on line `k` and checked by an opening
/// `if (C) return R;` and a second `if (C2) { return R; }` becomes a `for`
/// loop with `if (C2) { break; }` and `return R;` after the loop.
///
/// # Arguments
///
/// * `lines` - The body lines.
/// * `k` - The line of the counter initialization.
///
/// # Returns
///
/// Whether the loop became a `for`.
fn returning_while(lines: &mut Vec<String>, k: usize) -> bool {
    let (Some(init), Some(head)) = (lines.get(k), lines.get(k + 1)) else {
        return false;
    };
    let pad = indent_of(init);
    if indent_of(head) != pad || head.trim() != "while (1) {" {
        return false;
    }
    let Some((lhs_chain, value)) = init
        .trim()
        .strip_suffix(';')
        .and_then(|s| s.rsplit_once(" = "))
    else {
        return false;
    };
    let (prefix, v) = match lhs_chain.rsplit_once(" = ") {
        Some((p, v)) => (Some(p.trim().to_owned()), v.trim().to_owned()),
        None => (None, lhs_chain.trim().to_owned()),
    };
    let value = value.trim().to_owned();
    if !is_ident(&v)
        || impure(&value)
        || prefix
            .as_ref()
            .is_some_and(|p| !p.split(" = ").all(is_ident))
    {
        return false;
    }
    let Some(close) =
        closing(lines, k + 1, pad).filter(|&c| lines.get(c).is_some_and(|l| l.trim() == "}"))
    else {
        return false;
    };
    if close < k + 7
        || (k + 2..close).any(|j| {
            lines.get(j).is_some_and(|l| is_label(l))
                || (lines.get(j).is_some_and(|l| breaks(l.trim())) && breaks_loop(lines, k + 1, j))
        })
    {
        return false;
    }
    let Some((exit_cond, ret)) = lines
        .get(k + 2)
        .filter(|l| indent_of(l) == pad + 2)
        .and_then(|l| l.trim().strip_prefix("if (")?.split_once(") return "))
        .and_then(|(c, r)| Some((c.to_owned(), r.strip_suffix(';')?.to_owned())))
        .filter(|(c, _)| mentions_ident(c, &v) && !impure(c))
    else {
        return false;
    };
    let Some(c2) = lines
        .get(k + 3)
        .filter(|l| indent_of(l) == pad + 2)
        .and_then(|l| if_opener(l.trim()))
        .map(str::to_owned)
    else {
        return false;
    };
    let same_ret = lines
        .get(k + 4)
        .is_some_and(|l| indent_of(l) == pad + 4 && l.trim() == format!("return {ret};"))
        && lines
            .get(k + 5)
            .is_some_and(|l| indent_of(l) == pad + 2 && l.trim() == "}");
    let Some(raw_step) = lines
        .get(k + 6..close)
        .filter(|_| same_ret)
        .and_then(|b| step_of(b, pad + 2, &v))
    else {
        return false;
    };
    let step = if raw_step == format!("{v} = {v} + 1") {
        format!("{v} += 1")
    } else {
        raw_step.to_owned()
    };
    let pad_s = " ".repeat(pad);
    let cond = invert_condition(&exit_cond);
    let mut rewritten: Vec<String> = Vec::new();
    if let Some(p) = prefix {
        rewritten.push(format!("{pad_s}{p} = {value};"));
    }
    rewritten.push(format!("{pad_s}for ({v} = {value}; {cond}; {step}) {{"));
    rewritten.push(format!("{pad_s}  if ({c2}) {{"));
    rewritten.push(format!("{pad_s}    break;"));
    rewritten.push(format!("{pad_s}  }}"));
    rewritten.extend(lines.get(k + 6..close - 1).unwrap_or(&[]).iter().cloned());
    rewritten.push(format!("{pad_s}}}"));
    rewritten.push(format!("{pad_s}return {ret};"));
    lines.splice(k..=close, rewritten);
    true
}

/// Moves the statements an endless loop runs on its way out after it:
/// `while (1) { A; if (C) { T; break; } B }` is `while (1) { A; if (C) {
/// break; } B } T`.
///
/// The `break` is the loop's only one, so the line after the loop is
/// reached only through it and `T` runs there exactly when it ran before.
/// `T` may hold no label, `break`, `continue` or `case`, which would bind
/// to something else once moved.
///
/// # Arguments
///
/// * `lines` - The body lines.
/// * `k` - The line of the `while (1) {`.
///
/// # Returns
///
/// Whether the exit's statements moved.
fn exit_arm(lines: &mut Vec<String>, k: usize) -> bool {
    let Some(open) = lines.get(k).filter(|l| l.trim() == "while (1) {") else {
        return false;
    };
    let pad = indent_of(open);
    let Some(close) =
        closing(lines, k, pad).filter(|&c| lines.get(c).is_some_and(|l| l.trim() == "}"))
    else {
        return false;
    };
    let owned: Vec<usize> = (k + 1..close)
        .filter(|&j| lines.get(j).is_some_and(|l| breaks(l.trim())) && breaks_loop(lines, k, j))
        .collect();
    let &[j] = owned.as_slice() else {
        return false;
    };
    let at = |n: usize, text: &str, ind: usize| {
        lines
            .get(n)
            .is_some_and(|l| l.trim() == text && indent_of(l) == ind)
    };
    if !at(j, "break;", pad + 4) || !at(j + 1, "}", pad + 2) {
        return false;
    }
    let Some(o) = (k + 1..j)
        .rev()
        .find(|&o| lines.get(o).is_some_and(|l| indent_of(l) <= pad + 2))
        .filter(|&o| lines.get(o).is_some_and(|l| if_opener(l.trim()).is_some()))
    else {
        return false;
    };
    let exit = lines.get(o + 1..j).unwrap_or(&[]);
    if exit.is_empty()
        || exit.iter().any(|l| {
            let t = l.trim();
            is_label(l) || t.contains("break;") || t.contains("continue;") || is_case(t)
        })
    {
        return false;
    }
    let moved: Vec<String> = exit
        .iter()
        .map(|l| l.get(4..).unwrap_or(l.trim_start()).to_owned())
        .collect();
    lines.splice(close + 1..close + 1, moved);
    lines.drain(o + 1..j);
    true
}

/// Tells whether the `break` on line `j` leaves the loop opened on line
/// `k`, not a loop or `switch` nested in it.
///
/// # Arguments
///
/// * `lines` - The body lines.
/// * `k` - The loop's opening line.
/// * `j` - The `break`'s line.
fn breaks_loop(lines: &[String], k: usize, j: usize) -> bool {
    let Some(line) = lines.get(j) else {
        return false;
    };
    if is_case(line.trim()) {
        return false;
    }
    let mut ind = indent_of(line);
    for o in (k..j).rev() {
        let Some(l) = lines.get(o).filter(|l| !l.trim().is_empty()) else {
            continue;
        };
        if indent_of(l) >= ind {
            continue;
        }
        if o == k {
            return true;
        }
        ind = indent_of(l);
        let t = l.trim();
        if ["while (", "for (", "do {", "switch ("]
            .iter()
            .any(|p| t.starts_with(p))
            || is_case(t)
        {
            return false;
        }
    }
    false
}

/// Finds the line that closes the block opened on line `k`: the first
/// later line at or left of the opener's indentation.
///
/// # Arguments
///
/// * `lines` - The body lines.
/// * `k` - The opening line.
/// * `pad` - Its indentation.
pub(super) fn closing(lines: &[String], k: usize, pad: usize) -> Option<usize> {
    (k + 1..lines.len())
        .find(|&j| {
            lines
                .get(j)
                .is_some_and(|l| !l.trim().is_empty() && indent_of(l) <= pad)
        })
        .filter(|&j| {
            lines
                .get(j)
                .is_some_and(|l| indent_of(l) == pad && l.trim().starts_with('}'))
        })
}

/// The step a loop body ends with, for a `for` header.
///
/// It is the body's last line at its own level, when that line assigns
/// `v` and calls nothing, and the body never continues at its own level (a
/// `for` runs the step on the way to the test, which a `continue` in the
/// original skipped).
///
/// # Arguments
///
/// * `body` - The loop body's lines.
/// * `level` - The indentation of the body's own statements.
/// * `v` - The loop variable.
///
/// # Returns
///
/// The step without its semicolon, or `None`.
fn step_of<'b>(body: &'b [String], level: usize, v: &str) -> Option<&'b str> {
    let last = body.last()?;
    let t = last.trim();
    let step = t.strip_suffix(';')?;
    let (lhs, rhs) = step.split_once(' ')?;
    let assigns = matches!(
        rhs.split_once(' ').map(|(op, _)| op),
        Some("=" | "+=" | "-=" | "*=" | "<<=" | ">>=" | "&=" | "|=" | "^=")
    );
    (indent_of(last) == level && lhs == v && assigns && !impure(rhs) && !continues_at_top(body))
        .then_some(step)
}

/// Tells whether `v` is dead from line `from` on, where the text leaves
/// the block at indentation `pad`: written before any read on every path.
///
/// The scan is straight-line and conservative: it follows the text down,
/// out of an `if` arm it ends inside (skipping an `else`), and answers yes
/// at a plain assignment to `v` that does not read it, a `return` at the
/// level it scans that does not name `v`, or the end of the text. Such an
/// assignment inside a nested block skips the rest of that block, which
/// reads the new value. A label, a jump, a `case`, the end of a loop or a
/// switch, a read of `v` anywhere, or [`DEAD_SCAN_MAX`] lines say no.
///
/// # Arguments
///
/// * `lines` - The body lines.
/// * `from` - The first line after the rewritten region.
/// * `pad` - The indentation the region stood at.
/// * `v` - The variable.
fn dead_after(lines: &[String], from: usize, pad: usize, v: &str) -> bool {
    let mut level = pad;
    let mut j = from;
    let end = from.saturating_add(DEAD_SCAN_MAX);
    while j < lines.len() {
        if j >= end {
            return false;
        }
        let Some(l) = lines.get(j) else {
            return false;
        };
        let t = l.trim();
        let ind = indent_of(l);
        j += 1;
        if t.is_empty() {
            continue;
        }
        if is_label(l) || t.contains("goto ") || breaks(t) || continues(t) || is_case(t) {
            return false;
        }
        if ind < level {
            let Some(opener) = (0..j - 1)
                .rev()
                .find(|&o| {
                    lines
                        .get(o)
                        .is_some_and(|m| indent_of(m) == ind && !m.trim().is_empty())
                })
                .and_then(|o| lines.get(o))
            else {
                return false;
            };
            let o = opener.trim();
            let arm = o.starts_with("if (") || o.starts_with("} else if (") || o == "} else {";
            match t {
                "}" if arm => level = ind,
                "} else {" if arm => match closing(lines, j - 1, ind) {
                    Some(c) if lines.get(c).is_some_and(|m| m.trim() == "}") => {
                        level = ind;
                        j = c + 1;
                    }
                    _ => return false,
                },
                _ => return false,
            }
            continue;
        }
        if mentions_ident(t, v) {
            let write =
                plain_assignment(t).is_some_and(|(lhs, rhs)| lhs == v && !mentions_ident(rhs, v));
            if !write || ind == level {
                return write;
            }
            while let Some(m) = lines
                .get(j)
                .filter(|m| m.trim().is_empty() || indent_of(m) >= ind)
            {
                if is_label(m) {
                    return false;
                }
                j += 1;
            }
        }
        if ind == level && is_return(t) {
            return true;
        }
    }
    true
}

/// Tells whether two rendered conditions are the same test: equal as
/// expressions once `a > b` is read as `b < a` and an integer bound as the
/// strict one beside it (`x >= 65` is `x > 64`).
///
/// # Arguments
///
/// * `a` - One condition.
/// * `b` - The other.
fn same_condition(a: &str, b: &str) -> bool {
    let read = |s: &str| {
        let toks = c_tokens(s).ok()?;
        expression(&toks, &|n| named_type(n, 64).is_none(), 64)
            .ok()
            .map(strict)
    };
    matches!((read(a), read(b)), (Some(x), Some(y)) if x == y)
}

/// Writes a comparison as `<` with a strict integer bound where it can:
/// `a > b` as `b < a`, `a >= b` as `b <= a`, and `k <= x` as `k - 1 < x`,
/// `x <= k` as `x < k + 1` for an integer literal `k`.
///
/// # Arguments
///
/// * `e` - The expression.
fn strict(e: Ast) -> Ast {
    let e = match e {
        Ast::Bin(Bin::Gt, l, r) => Ast::Bin(Bin::Lt, r, l),
        Ast::Bin(Bin::Ge, l, r) => Ast::Bin(Bin::Le, r, l),
        other => other,
    };
    match e {
        Ast::Bin(Bin::Le, l, r) => match (*l, *r) {
            (Ast::Int(k, ty), x) if k > 0 => {
                Ast::Bin(Bin::Lt, Box::new(Ast::Int(k - 1, ty)), Box::new(x))
            }
            (x, Ast::Int(k, ty)) if k < u64::MAX => {
                Ast::Bin(Bin::Lt, Box::new(x), Box::new(Ast::Int(k + 1, ty)))
            }
            (l, r) => Ast::Bin(Bin::Le, Box::new(l), Box::new(r)),
        },
        other => other,
    }
}

#[cfg(test)]
#[expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]
mod tests {
    //! The loop rewrites on hand-written text, each beside the case that
    //! must keep its form.

    use super::recover_loops;

    /// Runs the rewrites over a body.
    ///
    /// # Arguments
    ///
    /// * `body` - The text, one statement per line.
    ///
    /// # Returns
    ///
    /// The text after the rewrites.
    fn run(body: &str) -> String {
        let mut lines: Vec<String> = body.lines().map(str::to_owned).collect();
        recover_loops(&mut lines);
        lines.join("\n") + "\n"
    }

    /// A guard that is the loop's own test makes the `do` a `while`.
    #[test]
    fn a_do_guarded_by_its_own_test_is_a_while() {
        let text = "if (rcx != 0) {\n  do {\n    rax += 1;\n    rcx -= 1;\n  } while (rcx != 0);\n}\nreturn rax;\n";
        assert_eq!(
            run(text),
            "while (rcx != 0) {\n  rax += 1;\n  rcx -= 1;\n}\nreturn rax;\n"
        );
        let bound = "if ((int32_t)rdi >= 65) {\n  do {\n    rdi -= 1;\n  } while ((int32_t)rdi > 64);\n}\nreturn 0;\n";
        assert_eq!(
            run(bound),
            "while ((int32_t)rdi > 64) {\n  rdi -= 1;\n}\nreturn 0;\n"
        );
        let other =
            "if (rdx != 0) {\n  do {\n    rcx -= 1;\n  } while (rcx != 0);\n}\nreturn rcx;\n";
        assert_eq!(run(other), other);
    }

    /// A guard that is the test with the first value put in makes a `for`,
    /// when the variable is dead on the path that skipped the loop.
    #[test]
    fn a_do_guarded_by_its_first_test_is_a_for() {
        let text = "if (*(uint64_t*)(r12 + 0x40) != 0) {\n  rbx = *(uint64_t*)(r12 + 0x40);\n  do {\n    sub_1(rbx);\n    rbx = *(uint64_t*)rbx;\n  } while (rbx != 0);\n}\nrbx = 0;\nreturn 0;\n";
        assert_eq!(
            run(text),
            "for (rbx = *(uint64_t*)(r12 + 0x40); rbx != 0; rbx = *(uint64_t*)rbx) {\n  sub_1(rbx);\n}\nrbx = 0;\nreturn 0;\n"
        );
        let read = "if (*(uint64_t*)(r12 + 0x40) != 0) {\n  rbx = *(uint64_t*)(r12 + 0x40);\n  do {\n    sub_1(rbx);\n    rbx = *(uint64_t*)rbx;\n  } while (rbx != 0);\n}\nreturn rbx;\n";
        assert_eq!(run(read), read);
        let continued = "if (a1 != 0) {\n  rcx = a1;\n  do {\n    if (rax != 0) continue;\n    rcx -= 1;\n  } while (rcx != 0);\n}\nreturn 0;\n";
        assert_eq!(
            run(continued),
            "rcx = a1;\nwhile (rcx != 0) {\n  if (rax != 0) continue;\n  rcx -= 1;\n}\nreturn 0;\n"
        );
    }

    /// The other first values set beside the loop variable stay in front of
    /// the `for`, each dead where the loop was skipped: a write inside a
    /// later block is a write on the paths through it.
    #[test]
    fn the_other_first_values_stay_in_front() {
        let text = "if (a1 != 0) {\n  rsi = a2;\n  rax = a1;\n  do {\n    sub_1(rax, rsi);\n    rax = *(uint64_t*)rax;\n  } while (rax != 0);\n}\nif (a3 != 0) {\n  rax = a3;\n  rsi = 0;\n  sub_2(rax);\n}\nreturn 0;\n";
        assert_eq!(
            run(text),
            "rsi = a2;\nfor (rax = a1; rax != 0; rax = *(uint64_t*)rax) {\n  sub_1(rax, rsi);\n}\nif (a3 != 0) {\n  rax = a3;\n  rsi = 0;\n  sub_2(rax);\n}\nreturn 0;\n"
        );
        let read = text.replace("  rsi = 0;\n", "  sub_3(rsi);\n");
        assert_eq!(run(&read), read);
    }

    /// What an endless loop runs on its one way out moves after it; with a
    /// second `break` out of the loop it stays, while a `break` out of a
    /// nested `switch` does not count.
    #[test]
    fn an_exit_arm_moves_after_its_loop() {
        let text = "while (1) {\n  rax = sub_1(rbx);\n  if (rax == 0) {\n    sub_2(rbx);\n    break;\n  }\n  switch (rax) {\n  case 1: break;\n  }\n}\nreturn 0;\n";
        assert_eq!(
            run(text),
            "while (1) {\n  rax = sub_1(rbx);\n  if (rax == 0) {\n    break;\n  }\n  switch (rax) {\n  case 1: break;\n  }\n}\nsub_2(rbx);\nreturn 0;\n"
        );
        let two = text.replace(
            "  case 1: break;\n",
            "  case 1: break;\n  }\n  if (rax == 2) {\n    break;\n",
        );
        assert_eq!(run(&two), two);
    }

    /// A `while` whose variable is set right before it and stepped at the
    /// end of its body is a `for`; one with a label in its body is not.
    #[test]
    fn a_counted_while_is_a_for() {
        let text = "rcx = 0;\nwhile (rcx < a1) {\n  rax += rcx;\n  rcx += 1;\n}\nreturn rax;\n";
        assert_eq!(
            run(text),
            "for (rcx = 0; rcx < a1; rcx += 1) {\n  rax += rcx;\n}\nreturn rax;\n"
        );
        let labelled =
            "rcx = 0;\nwhile (rcx < a1) {\n  rax += rcx;\n  L_1:\n  rcx += 1;\n}\nreturn rax;\n";
        assert_eq!(run(labelled), labelled);
        let returning = "rax = rcx = 0;\nwhile (1) {\n  if (rcx >= 7) return 0;\n  if (table[rcx] == a1) {\n    return 0;\n  }\n  sub_1(rcx);\n  rcx = rcx + 1;\n}\n";
        assert_eq!(
            run(returning),
            "rax = 0;\nfor (rcx = 0; rcx < 7; rcx += 1) {\n  if (table[rcx] == a1) {\n    break;\n  }\n  sub_1(rcx);\n}\nreturn 0;\n"
        );
        let pos_guard = "if ((int32_t)a1 > 0) {\n  rbx = 0;\n  do {\n    sub_1(rbx);\n    rbx = rbx + 1;\n  } while ((uint32_t)a1 != rbx);\n}\nreturn 0;\n";
        assert_eq!(
            run(pos_guard),
            "for (rbx = 0; (int32_t)rbx < (int32_t)a1; rbx += 1) {\n  sub_1(rbx);\n}\nreturn 0;\n"
        );
        let do_const = "rax = 0;\ndo {\n  sub_1(rax);\n  rdx = rdx + 2;\n  rax = rax + 1;\n} while (rax != 0x100);\n";
        assert_eq!(
            run(do_const),
            "for (rax = 0; rax != 0x100; rax += 1) {\n  sub_1(rax);\n  rdx = rdx + 2;\n}\n"
        );
    }
}
