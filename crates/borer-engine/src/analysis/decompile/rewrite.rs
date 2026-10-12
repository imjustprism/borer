//! Text rewrites after emission: strlen loops, merged chains, folded copies,
//! inverted conditions, and dead code.

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

/// Finds the closing braces of `while (1)` loops that contain no `break` of their own.
///
/// Nothing after such a loop ever runs. Breaks inside nested loops or
/// switches belong to those, not to the outer loop, which is why each
/// nested one is tracked by the indent its closing brace stands at. A break
/// under a condition (`if (c) break;`) leaves the loop like any other.
///
/// # Arguments
///
/// * `lines` - The body lines.
///
/// # Returns
///
/// Indices into `lines` of those closing braces.
pub(super) fn endless_loop_closers(lines: &[String]) -> BTreeSet<usize> {
    let mut out = BTreeSet::new();
    for (k, l) in lines.iter().enumerate() {
        if l.trim() != "while (1) {" {
            continue;
        }
        let d = indent_of(l);
        let mut nested: Vec<Scope> = Vec::new();
        let mut leaves = false;
        for (j, m) in lines.iter().enumerate().skip(k + 1) {
            let t = m.trim();
            let ind = indent_of(m);
            if ind <= d {
                if t == "}" && ind == d && !leaves {
                    out.insert(j);
                }
                break;
            }
            if at_loop_level(m, &mut nested) && breaks(t) {
                leaves = true;
            }
        }
    }
    out
}

/// Chains duplicate spills into one assignment per value.
///
/// Runs of consecutive independent assignments (no right-hand side reads any
/// target in the run, all targets distinct, no right-hand side a call) are
/// regrouped by value, first appearance first, and each group becomes one
/// chained assignment: debug codegen spills the same register into every
/// binding's slot, and `a = b = c = rdx;` says so once. A call ends a run:
/// two calls with the same text are two calls, and a call may change what a
/// later value in the run reads.
///
/// # Arguments
///
/// * `lines` - The body lines, rewritten in place.
///
/// # Returns
///
/// Whether two assignments were merged.
pub(super) fn merge_chains(lines: &mut Vec<String>) -> bool {
    /// A plain assignment whose right side calls nothing.
    fn pure(line: &str) -> Option<(&str, &str)> {
        plain_assignment(line).filter(|(_, r)| !impure(r))
    }
    let mut out: Vec<String> = Vec::with_capacity(lines.len());
    let mut changed = false;
    let mut i = 0;
    while i < lines.len() {
        let Some(first) = pure(&lines[i]) else {
            out.push(lines[i].clone());
            i += 1;
            continue;
        };
        let indent = pad_of(&lines[i]).to_owned();
        let mut run: Vec<(String, String)> = vec![(first.0.to_owned(), first.1.to_owned())];
        let mut j = i + 1;
        while j < lines.len()
            && let Some((l, r)) = pure(&lines[j])
            && !run
                .iter()
                .any(|(tl, tr)| tl == l || mentions_ident(tr, l) || mentions_ident(r, tl))
            && !mentions_ident(r, l)
        {
            run.push((l.to_owned(), r.to_owned()));
            j += 1;
        }
        if run.len() == 1 {
            out.push(lines[i].clone());
            i += 1;
            continue;
        }
        let mut groups: Vec<(String, Vec<String>)> = Vec::new();
        for (l, r) in run {
            match groups.iter_mut().find(|(gr, _)| *gr == r) {
                Some((_, ls)) => {
                    ls.push(l);
                    changed = true;
                }
                None => groups.push((r, vec![l])),
            }
        }
        for (r, ls) in groups {
            out.push(format!("{indent}{} = {r};", ls.join(" = ")));
        }
        i = j;
    }
    *lines = out;
    changed
}

/// Drops the temporaries that only copy a variable: `tmp_1 = rcx = rax;`
/// or `tmp_1 = rcx;`.
///
/// A register parked in a temporary before it was overwritten often lands
/// in the same chain as the copy that kept it, and then the temporary and
/// the copy hold one value. Every read of the temporary becomes the
/// variable and the temporary leaves the chain, when the temporary is
/// written only there, the variable (a register or a parameter, which no
/// call behind the text changes) is not written again before the last
/// read, and nothing in between leaves the block, opens a loop or is a
/// label another path could enter by.
///
/// # Arguments
///
/// * `lines` - The body lines, rewritten in place.
///
/// # Returns
///
/// Whether a temporary was dropped.
pub(super) fn fold_temp_copies(lines: &mut Vec<String>) -> bool {
    let is_param = |w: &str| w == "this" || is_param_name(w);
    let mut changed = false;
    let mut i = 0;
    while i < lines.len() {
        let t = lines[i].trim();
        let Some(stmt) = t.strip_suffix(';') else {
            i += 1;
            continue;
        };
        let parts: Vec<&str> = stmt.split(" = ").collect();
        let Some((value, targets)) = parts.split_last() else {
            i += 1;
            continue;
        };
        let tmp = targets.iter().copied().find(|w| is_temp_name(w));
        let var = targets
            .iter()
            .copied()
            .find(|w| !is_temp_name(w) && is_ident(w))
            .or_else(|| {
                (targets.len() == 1 && is_ident(value) && !is_temp_name(value)).then_some(*value)
            });
        let (Some(tmp), Some(var)) = (tmp, var) else {
            i += 1;
            continue;
        };
        let plain_targets = targets.iter().all(|w| is_ident(w));
        let fits = plain_targets
            && (is_register_name(var) || is_param(var))
            && lines
                .iter()
                .enumerate()
                .all(|(j, l)| j == i || !writes_var(l.trim(), tmp))
            && !lines.iter().take(i).any(|l| mentions_ident(l, tmp));
        let last = lines
            .iter()
            .enumerate()
            .skip(i + 1)
            .filter(|(_, l)| mentions_ident(l, tmp))
            .map(|(j, _)| j)
            .next_back();
        let ind = indent_of(&lines[i]);
        let clear = last.is_some_and(|last| {
            lines.iter().take(last + 1).skip(i + 1).all(|l| {
                let lt = l.trim();
                indent_of(l) >= ind
                    && !lt.ends_with(':')
                    && !lt.starts_with("while (")
                    && !lt.starts_with("do {")
                    && !lt.starts_with("for (")
                    && !writes_var(lt, var)
            })
        });
        if !(fits && clear) {
            i += 1;
            continue;
        }
        let (tmp, var) = (tmp.to_owned(), var.to_owned());
        let kept: Vec<&str> = targets.iter().copied().filter(|w| *w != tmp).collect();
        let pad = " ".repeat(ind);
        let rewritten = if kept.is_empty() {
            None
        } else {
            Some(format!("{pad}{} = {value};", kept.join(" = ")))
        };
        for line in lines.iter_mut().skip(i + 1) {
            if mentions_ident(line, &tmp) {
                *line = rename_word(line, &tmp, &var);
            }
        }
        match rewritten {
            Some(r) => {
                lines[i] = r;
                i += 1;
            }
            None => {
                lines.remove(i);
            }
        }
        changed = true;
    }
    changed
}

/// Rewrites `} else {` whose block is exactly one `if` statement as
/// `} else if ...`, so a ladder reads as a chain instead of nesting one
/// level per case.
///
/// The inner statement runs from the `if` line to the first `}` at its own
/// indentation that does not continue it (`} else` does), and the outer `}`
/// must follow it directly; the statement's lines move out by one level.
/// Labels are gone by the time this runs, so a labeled arm never qualifies.
///
/// # Arguments
///
/// * `lines` - The body lines, rewritten in place.
///
/// # Returns
///
/// Whether anything changed.
pub(super) fn flatten_else_if(lines: &mut Vec<String>) -> bool {
    let mut changed = false;
    let mut i = 0;
    while i < lines.len() {
        if lines[i].trim() != "} else {" {
            i += 1;
            continue;
        }
        let ind = indent_of(&lines[i]);
        let Some(first) = lines.get(i + 1) else {
            break;
        };
        let inner = indent_of(first);
        let head = first.trim().to_owned();
        if inner != ind + 2 || if_opener(&head).is_none() {
            i += 1;
            continue;
        }
        let mut end = None;
        for (k, l) in lines.iter().enumerate().skip(i + 2) {
            let li = indent_of(l);
            if li < inner {
                break;
            }
            if li == inner && l.trim() == "}" {
                end = Some(k);
                break;
            }
        }
        let Some(end) = end else {
            i += 1;
            continue;
        };
        if lines
            .get(end + 1)
            .is_none_or(|l| indent_of(l) != ind || l.trim() != "}")
        {
            i += 1;
            continue;
        }
        lines[i] = format!("{}}} else {head}", " ".repeat(ind));
        for l in &mut lines[i + 2..=end] {
            if l.len() >= 2 {
                l.drain(..2);
            }
        }
        lines.remove(i + 1);
        lines.remove(end);
        changed = true;
        i += 1;
    }
    changed
}

/// Tells whether the text after line `from` reaches the label without
/// running anything.
///
/// Only closing braces of `if`/`else` blocks may lie between them, since
/// falling out of such a block continues right after it, while falling out
/// of a loop body repeats the loop and out of a `case` runs the next one.
///
/// # Arguments
///
/// * `lines` - The body lines.
/// * `from` - Index of the `goto` line.
/// * `label` - The label's name.
pub(super) fn falls_to_label(lines: &[String], from: usize, label: &str) -> bool {
    let mut j = from + 1;
    while let Some(l) = lines.get(j) {
        let t = l.trim();
        if t != "}" {
            return t.strip_suffix(':') == Some(label);
        }
        let ind = indent_of(l);
        let opener = lines
            .get(..j)
            .into_iter()
            .flatten()
            .rev()
            .find(|m| indent_of(m) == ind && m.trim().ends_with('{'))
            .map(|m| m.trim());
        match opener {
            Some(o) if o.starts_with("if (") || o.starts_with("} else") => {}
            _ => return false,
        }
        j += 1;
    }
    false
}

/// Inverts a rendered condition.
///
/// A condition negated as a whole (`!(c)`, `!f(x)`) loses its negation.
/// One comparison outside every bracket and string flips its operator,
/// unless it is an ordered comparison of floating-point operands
/// ([`float_like`]): `a < b` is false on NaN and so is `a >= b`, so its
/// negation is `!(a < b)`. A guard chain negates operand by operand
/// ([`de_morgan`]) where each operand does; anything else (a template
/// name's angle brackets, a bare value) is negated as a whole.
///
/// # Arguments
///
/// * `cond` - The rendered condition.
pub(super) fn invert_condition(cond: &str) -> String {
    if let Some(inner) = negated_whole(cond) {
        return inner.to_owned();
    }
    let mut depth = 0i32;
    let mut in_str = false;
    let mut esc = false;
    let mut found: Option<(usize, usize)> = None;
    let mut count = 0usize;
    let mut logical = false;
    for (i, c) in cond.char_indices() {
        if in_str {
            match c {
                _ if esc => esc = false,
                '\\' => esc = true,
                '"' => in_str = false,
                _ => {}
            }
            continue;
        }
        match c {
            '"' => in_str = true,
            '(' | '[' => depth += 1,
            ')' | ']' => depth -= 1,
            ' ' if depth == 0 => {
                let tok = cond[i + 1..].split(' ').next().unwrap_or("");
                match tok {
                    "&&" | "||" => logical = true,
                    "==" | "!=" | "<" | ">" | "<=" | ">=" => {
                        count += 1;
                        found = Some((i + 1, tok.len()));
                    }
                    _ => {}
                }
            }
            _ => {}
        }
    }
    let flip = |op: &str| match op {
        "==" => "!=",
        "!=" => "==",
        "<" => ">=",
        ">" => "<=",
        "<=" => ">",
        _ => "<",
    };
    match found {
        Some((at, len)) if count == 1 && !logical => {
            let op = &cond[at..at + len];
            let ordered = !matches!(op, "==" | "!=");
            if ordered && (float_like(&cond[..at]) || float_like(&cond[at + len..])) {
                return format!("!({cond})");
            }
            format!("{}{}{}", &cond[..at], flip(op), &cond[at + len..])
        }
        _ => de_morgan(cond).unwrap_or_else(|| format!("!({cond})")),
    }
}

/// The condition a rendered negation negates, when the `!` applies to the
/// whole text: `!(c)` gives `c`, `!f(x)` gives `f(x)`, `!v` gives `v`.
///
/// # Arguments
///
/// * `cond` - The rendered condition.
///
/// # Returns
///
/// The negated part, or `None` when the text is not one negation (`!a && b`
/// negates only `a`).
pub(super) fn negated_whole(cond: &str) -> Option<&str> {
    let inner = cond.strip_prefix('!')?;
    let head = inner
        .find(|c: char| !is_ident_char(c))
        .unwrap_or(inner.len());
    let rest = &inner[head..];
    if rest.is_empty() {
        return (head > 0).then_some(inner);
    }
    if !rest.starts_with('(') {
        return None;
    }
    let mut depth = 0i32;
    let mut in_str = false;
    let mut esc = false;
    for (i, c) in rest.char_indices() {
        if in_str {
            match c {
                _ if esc => esc = false,
                '\\' => esc = true,
                '"' => in_str = false,
                _ => {}
            }
            continue;
        }
        match c {
            '"' => in_str = true,
            '(' => depth += 1,
            ')' => {
                depth -= 1;
                if depth == 0 {
                    if i + 1 != rest.len() {
                        return None;
                    }
                    return Some(if head == 0 { &rest[1..i] } else { inner });
                }
            }
            _ => {}
        }
    }
    None
}

/// Folds the unordered half of a floating-point comparison away.
///
/// `comiss` and `ucomiss` set the parity flag when either operand is NaN,
/// so a C++ `x != y` on floats compiles to `jp` then `jne` and a `x == y`
/// to `jnp` then `je`. The renderer writes the parity test as the C99
/// `isunordered(x, y)` (or, in older text, the marker `/*p*/ (x, y)`),
/// leaving `isunordered(x, y) || x != y`; but C's `!=` on floating point is
/// already true when an operand is NaN and its `==` already false, so each
/// pair is the comparison alone, and `!isunordered(x, y) && x == y` is
/// `x == y`. A marker with no such partner becomes `isunordered(x, y)`, an
/// ordered one its negation; only floating-point operands qualify there,
/// since parity after an integer compare means the parity of a byte.
///
/// # Arguments
///
/// * `lines` - The body lines, rewritten in place.
///
/// # Returns
///
/// Whether anything was folded.
pub(super) fn fold_unordered_compares(lines: &mut [String]) -> bool {
    let mut changed = false;
    for line in lines.iter_mut() {
        let mut from = 0;
        while let Some(found) = line.get(from..).and_then(unordered_test) {
            let (offset, len, unordered, marker) = found;
            let at = from + offset;
            let open = at + len - 1;
            let Some(close) = matching_paren(line, open) else {
                from = open + 1;
                continue;
            };
            let Some((l, r)) = line.get(open + 1..close).and_then(split_pair) else {
                from = close;
                continue;
            };
            let (joiner, rel) = if unordered {
                (" || ", "!=")
            } else {
                (" && ", "==")
            };
            let compare = format!("{joiner}{l} {rel} {r}");
            if marker && !float_like(l) && !float_like(r) {
                from = close;
                continue;
            }
            if line
                .get(close + 1..)
                .is_some_and(|t| t.starts_with(&compare))
            {
                let end = close + 1 + compare.len();
                let text = format!("{l} {rel} {r}");
                line.replace_range(at..end, &text);
                from = at + text.len();
                changed = true;
                continue;
            }
            let head = format!("{l} {rel} {r}{joiner}");
            if line.get(..at).is_some_and(|t| t.ends_with(&head)) {
                let start = at - head.len();
                let text = format!("{l} {rel} {r}");
                line.replace_range(start..close + 1, &text);
                from = start + text.len();
                changed = true;
                continue;
            }
            if !marker {
                from = close;
                continue;
            }
            let text = if unordered {
                format!("isunordered({l}, {r})")
            } else {
                format!("!isunordered({l}, {r})")
            };
            line.replace_range(at..close + 1, &text);
            from = at + text.len();
            changed = true;
        }
    }
    changed
}

/// The first unordered test in a text: the `isunordered(` call, negated or
/// not, or the parity marker `/*p*/ (` or `/*np*/ (`.
///
/// # Arguments
///
/// * `t` - The text searched.
///
/// # Returns
///
/// The test's offset, the length of its head up to and including the `(`,
/// whether it holds on an unordered outcome, and whether it is a marker.
fn unordered_test(t: &str) -> Option<(usize, usize, bool, bool)> {
    let markers = [("/*p*/ (", true), ("/*np*/ (", false)]
        .into_iter()
        .filter_map(|(m, u)| t.find(m).map(|i| (i, m.len(), u, true)));
    let mut calls = Vec::new();
    let mut from = 0;
    while let Some(i) = t
        .get(from..)
        .and_then(|s| s.find("isunordered("))
        .map(|i| from + i)
    {
        from = i + 1;
        let before = t.get(..i).and_then(|h| h.chars().next_back());
        match before {
            Some('!') => calls.push((i - 1, "!isunordered(".len(), false, false)),
            Some(c) if is_ident_char(c) => continue,
            _ => calls.push((i, "isunordered(".len(), true, false)),
        }
        break;
    }
    markers.chain(calls).min_by_key(|(i, ..)| *i)
}

/// Splits `a, b` at the comma that is not inside parentheses.
///
/// # Arguments
///
/// * `inner` - The text between the parentheses.
pub(super) fn split_pair(inner: &str) -> Option<(&str, &str)> {
    let mut depth = 0i32;
    for (i, c) in inner.char_indices() {
        match c {
            '(' | '[' => depth += 1,
            ')' | ']' => depth -= 1,
            ',' if depth == 0 => {
                let l = inner.get(..i)?;
                let r = inner.get(i + 1..)?.strip_prefix(' ')?;
                return (!l.is_empty() && !r.is_empty() && !r.contains(", ")).then_some((l, r));
            }
            _ => {}
        }
    }
    None
}

/// Drops an assignment to a register variable nothing reads.
///
/// The lifter writes a register out when the block's liveness says a
/// successor may read it; when the structuring that follows leaves no
/// reader at all, the assignment is a value computed for nobody. Such a
/// target is dead when its variable appears nowhere in the whole body but
/// on its own line, which covers loops (a back edge's read is a mention)
/// and address-taken stack slots (`&local_18` mentions it), and a right
/// side that reads the target itself (`rdx = f__rdx(rsi, rdx)`) only feeds
/// a value nothing reads; or when the lines that follow it in order
/// replace or abandon the value before anything can read it
/// ([`dead_after`]). A dead target goes when its right side is pure, or a
/// second result (`f__rdx(..)`), which only names what the call on the
/// line before left in a register; a call may do more than return a
/// value, so a lone call whose every target is dead stays as a statement
/// of its own (`f(x);`), and any other right side with a call keeps its
/// line. In a chain, `rcx = rbx = rdi = a1;`, only the dead targets go and
/// the copies something reads stay; the line goes with its last target.
/// The declaration follows on its own, since only names the body still
/// mentions are declared. A register or stack slot assigned its own value
/// (`local_4 = local_4;`, a saved register pushed back where it was
/// popped from) changes nothing and goes too. The register a function
/// hands a second result back in is read by its callers, so its
/// assignments stay.
///
/// # Arguments
///
/// * `lines` - The body lines.
/// * `live_out` - The register the function hands a second result back
///   in, if any (`rdx`).
///
/// # Returns
///
/// The lines without the dead assignments, or `None` when there were none.
pub(super) fn drop_dead_assignments(
    lines: &[String],
    live_out: Option<&str>,
) -> Option<Vec<String>> {
    let mut mentions: BTreeMap<&str, usize> = BTreeMap::new();
    for line in lines {
        for word in tokens(line).filter(|w| is_register_name(w)) {
            *mentions.entry(word).or_default() += 1;
        }
    }
    let own = |name: &str, prefix: &str| {
        name.strip_prefix(prefix)
            .is_some_and(|n| !n.is_empty() && n.bytes().all(|c| c.is_ascii_hexdigit()))
    };
    let mut changed = false;
    let mut out = Vec::with_capacity(lines.len());
    for (at, line) in lines.iter().enumerate() {
        let parts: Vec<&str> = line
            .trim()
            .strip_suffix(';')
            .map(|t| t.split(" = ").collect())
            .unwrap_or_default();
        let Some((rhs, targets)) = parts.split_last().filter(|(_, t)| !t.is_empty()) else {
            out.push(line.clone());
            continue;
        };
        let local = |name: &str| {
            is_register_name(name) || ["local_", "home_", "arg_"].iter().any(|p| own(name, p))
        };
        let pure = !impure(rhs) || second_result(rhs);
        let call = !pure && lone_call(rhs);
        let kept: Vec<&str> = targets
            .iter()
            .copied()
            .filter(|name| {
                let unread = (pure || call)
                    && is_register_name(name)
                    && live_out != Some(*name)
                    && (mentions.get(name) == Some(&tokens(line).filter(|w| w == name).count())
                        || dead_after(lines, at, name, live_out));
                let itself = local(name) && name == rhs;
                !(unread || itself)
            })
            .collect();
        if kept.len() == targets.len() {
            out.push(line.clone());
            continue;
        }
        changed = true;
        if !kept.is_empty() {
            out.push(format!("{}{} = {rhs};", pad_of(line), kept.join(" = ")));
        } else if call {
            out.push(format!("{}{rhs};", pad_of(line)));
        }
    }
    changed.then_some(out)
}

/// Tells whether the value line `at` gives `name` is replaced or left
/// behind before anything can read it.
///
/// The lines after it are followed at its own depth while they run in
/// order: one that assigns `name` without reading it, or a `return` that
/// does not read it (nor hands it back as a second result), settles that
/// nothing does; a line that mentions it, or one that may leave the run (a
/// block opening or closing, a jump, a `case`, an unmodelled instruction),
/// settles nothing. A label on the way is passed: a path that enters there
/// does not carry this value.
///
/// # Arguments
///
/// * `lines` - The body lines.
/// * `at` - The assignment's line.
/// * `name` - The register it assigns.
/// * `live_out` - The register a second result comes back in, if any.
fn dead_after(lines: &[String], at: usize, name: &str, live_out: Option<&str>) -> bool {
    let Some(first) = lines.get(at) else {
        return false;
    };
    let depth = indent_of(first);
    for line in lines.iter().skip(at + 1) {
        let t = line.trim();
        if t.is_empty() || t.starts_with("//") || is_label(line) {
            continue;
        }
        let reads = tokens(t).filter(|w| *w == name).count();
        let leaves = t.starts_with(['{', '}', '/'])
            || tokens(t).next().is_some_and(|w| {
                matches!(
                    w,
                    "if" | "else"
                        | "while"
                        | "for"
                        | "do"
                        | "switch"
                        | "case"
                        | "default"
                        | "goto"
                        | "break"
                        | "continue"
                )
            });
        if indent_of(line) != depth || leaves {
            return false;
        }
        if t == "return;" || t.starts_with("return ") {
            return reads == 0 && live_out != Some(name);
        }
        let Some(stmt) = t.strip_suffix(';') else {
            return false;
        };
        let parts: Vec<&str> = stmt.split(" = ").collect();
        let assigned = parts.split_last().map_or(0, |(_, targets)| {
            targets.iter().filter(|w| **w == name).count()
        });
        if reads > 0 {
            return assigned == reads;
        }
    }
    false
}

/// Tells whether a right side is one call and nothing else, which stands
/// as a statement of its own: `f(x)`, `a1->vtable[2](x)`, `(*rax)(x)`.
///
/// # Arguments
///
/// * `rhs` - The text after the last ` = `, without the `;`.
fn lone_call(rhs: &str) -> bool {
    let Some(open) = rhs
        .len()
        .checked_sub(1)
        .filter(|_| rhs.ends_with(')'))
        .and_then(|close| opening_paren(rhs, close))
    else {
        return false;
    };
    let callee = rhs.get(..open).unwrap_or("");
    if callee.starts_with('(') {
        return callee.ends_with(')')
            && callee
                .len()
                .checked_sub(1)
                .and_then(|c| opening_paren(callee, c))
                == Some(0);
    }
    let mut depth = 0i32;
    let mut prev = ' ';
    for c in callee.chars() {
        let fits = match c {
            '(' | '[' => {
                depth += 1;
                true
            }
            ')' | ']' => {
                depth -= 1;
                true
            }
            '>' => depth > 0 || prev == '-',
            _ => depth > 0 || is_ident_char(c) || matches!(c, ':' | '~' | '.' | '-'),
        };
        if !fits {
            return false;
        }
        prev = c;
    }
    !callee.is_empty() && depth == 0
}

/// Tells whether a right side is a second result, `f__rdx(args)` with pure
/// arguments: no call of its own, only the register the call on the line
/// before left a value in.
///
/// # Arguments
///
/// * `rhs` - The text after the last ` = `, without the `;`.
fn second_result(rhs: &str) -> bool {
    let Some((callee, rest)) = rhs.split_once('(') else {
        return false;
    };
    let args = rest.strip_suffix(')').unwrap_or(rest);
    callee.ends_with("__rdx")
        && callee
            .chars()
            .all(|c| is_ident_char(c) || matches!(c, ':' | '~'))
        && rest.ends_with(')')
        && !impure(args)
}

/// Turns the trailing `goto` of an `if` arm into an `else` around the run
/// the jump skips.
///
/// `if (c) { ...; goto L; }`, a run, then `L:` at the `if`'s own
/// indentation: the run executes exactly when `c` is false and both paths
/// reach `L`, so the run is the `else` arm and the jump goes. The arm must
/// end in the jump and carry no `else` already; the run must be
/// self-contained, its lines at or below the `if`'s indentation with
/// balanced braces, no `case` or `default` line, and a label inside it
/// only when every jump to it comes from inside the run. Runs longer than
/// 200 lines are left alone. The arm may close an `if`/`else if` chain
/// only when every earlier arm ends in a transfer ([`earlier_arms_leave`]):
/// an earlier arm that falls out of the chain runs the run too, which the
/// `else` would skip.
///
/// # Arguments
///
/// * `lines` - The body lines, rewritten in place.
///
/// # Returns
///
/// Whether anything was absorbed.
pub(super) fn absorb_else(lines: &mut Vec<String>) -> bool {
    /// Longest run absorbed into an `else`.
    const RUN_MAX: usize = 200;
    let mut jumps = goto_index(lines);
    let mut changed = false;
    let mut i = 0;
    while i + 2 < lines.len() {
        let here = i;
        i += 1;
        let i = here;
        let t = lines[i].trim();
        let Some(target) = is_goto(t).then(|| goto_target(t)).flatten() else {
            continue;
        };
        let ind = indent_of(&lines[i]);
        if ind < 2 || lines[i + 1].trim() != "}" || indent_of(&lines[i + 1]) + 2 != ind {
            continue;
        }
        let outer = ind - 2;
        let Some(open) = lines[..i]
            .iter()
            .rposition(|l| !l.trim().is_empty() && indent_of(l) <= outer)
        else {
            continue;
        };
        let head = lines[open].trim();
        if indent_of(&lines[open]) != outer
            || !head.ends_with(") {")
            || !(head.starts_with("if (")
                || (head.starts_with("} else if (") && earlier_arms_leave(lines, open)))
        {
            continue;
        }
        let target = format!("{target}:");
        let Some((end, inner)) =
            run_to_label(lines, i + 2, outer, &target, RunLabels::Contained, RUN_MAX)
                .filter(|(e, _)| *e > i + 2)
        else {
            continue;
        };
        if !jumps_contained(&jumps, &inner, i, end) {
            continue;
        }
        let pad = " ".repeat(outer);
        let mut arm = vec![format!("{pad}}} else {{")];
        arm.extend(
            lines
                .get(i + 2..end)
                .unwrap_or(&[])
                .iter()
                .map(|l| format!("  {l}")),
        );
        arm.push(format!("{pad}}}"));
        lines.splice(i..end, arm);
        jumps = goto_index(lines);
        changed = true;
    }
    changed
}

/// Tells whether every arm of an `if`/`else if` chain before the
/// `} else if (...) {` line at `at` ends in a transfer, so that no earlier
/// arm falls out of the chain to the code after it.
///
/// Each arm's last line at the arm's own indentation must leave (`return`,
/// `goto`, `break`, `continue`); an empty arm, or one ending in a nested
/// block, falls out.
///
/// # Arguments
///
/// * `lines` - The body lines.
/// * `at` - Index of a `} else if (...) {` line.
pub(super) fn earlier_arms_leave(lines: &[String], at: usize) -> bool {
    let outer = indent_of(&lines[at]);
    let mut k = at;
    loop {
        let t = lines[k].trim();
        if k != at && t.starts_with("if (") && t.ends_with(") {") {
            return true;
        }
        if !t.starts_with("} else if (") {
            return false;
        }
        let near = |l: &String| !l.trim().is_empty() && indent_of(l) <= outer + 2;
        let Some(last) = lines[..k].iter().rposition(near) else {
            return false;
        };
        if indent_of(&lines[last]) != outer + 2 || !transfers(&lines[last]) {
            return false;
        }
        let Some(opener) = lines[..last]
            .iter()
            .rposition(|l| !l.trim().is_empty() && indent_of(l) <= outer)
        else {
            return false;
        };
        if indent_of(&lines[opener]) != outer {
            return false;
        }
        k = opener;
    }
}

/// How a run folded under a guard may hold labels.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum RunLabels {
    /// No label at all: the first one ends the attempt.
    Forbidden,
    /// Labels only the run itself jumps to.
    Contained,
}

/// Finds the label `target` at indentation `ind` that ends a balanced run
/// starting at `from`, with no `case` or `default` line and no dedent on
/// the way.
///
/// # Arguments
///
/// * `lines` - The body lines.
/// * `from` - The first line of the run.
/// * `ind` - The indentation the label must stand at.
/// * `target` - The label line, `L_x:`.
/// * `labels` - Whether the run may hold labels of its own.
/// * `max` - Longest run looked at.
///
/// # Returns
///
/// The label's index and the names of the labels inside the run, or
/// `None` when no such run ends at the label.
fn run_to_label(
    lines: &[String],
    from: usize,
    ind: usize,
    target: &str,
    labels: RunLabels,
    max: usize,
) -> Option<(usize, Vec<String>)> {
    let mut depth = 0i32;
    let mut inner: Vec<String> = Vec::new();
    for (j, l) in lines
        .iter()
        .enumerate()
        .take((from + max).min(lines.len()))
        .skip(from)
    {
        let t = l.trim();
        if t.is_empty() {
            continue;
        }
        if depth == 0 && indent_of(l) == ind && t == target {
            return Some((j, inner));
        }
        if indent_of(l) < ind || is_case(t) {
            return None;
        }
        if let Some(name) = label_name(l) {
            if labels == RunLabels::Forbidden {
                return None;
            }
            inner.push(name.to_owned());
        }
        depth += brace_delta(t);
        if depth < 0 {
            return None;
        }
    }
    None
}

/// Folds a conditional `goto` that skips a run into an `if` around the run.
///
/// The run is every line from the jump to its label at the jump's own
/// indentation: nested blocks are allowed as long as their braces balance,
/// and, with [`RunLabels::Contained`], a label inside the run is allowed
/// when every jump to it comes from inside the run too, so nothing enters
/// the run from outside; a `case` or `default` line ends the attempt. The strict form
/// runs with every other cleanup and the inner-label form only once those
/// have settled, so an outer guard never wraps a region before the guards
/// inside it have had their own turn. Falling out of such a jump runs the
/// whole run and reaches the label, so the run becomes the arm of the
/// inverted condition and the label is left for the pruning pass. Runs
/// longer than 200 lines are left alone.
///
/// # Arguments
///
/// * `lines` - The body lines, rewritten in place.
/// * `labels` - Whether a run may hold labels that only it targets.
///
/// # Returns
///
/// Whether anything was folded.
pub(super) fn fold_conditional_gotos(lines: &mut Vec<String>, labels: RunLabels) -> bool {
    /// Longest run folded into the arm.
    const SPAN_MAX: usize = 200;
    let mut jumps = goto_index(lines);
    let mut changed = false;
    let mut i = 0;
    while i < lines.len() {
        let here = i;
        i += 1;
        let i = here;
        let Some((cond, label)) = lines.get(i).and_then(|l| {
            let (c, g) = conditional_goto(l.trim())?;
            Some((c.to_owned(), g.to_owned()))
        }) else {
            continue;
        };
        let ind = lines.get(i).map_or(0, |l| indent_of(l));
        let target = format!("{label}:");
        let Some((end, inner)) =
            run_to_label(lines, i + 1, ind, &target, labels, SPAN_MAX).filter(|(e, _)| *e > i + 1)
        else {
            continue;
        };
        if !jumps_contained(&jumps, &inner, i, end) {
            continue;
        }
        let pad = " ".repeat(ind);
        let mut arm = vec![format!("{pad}if ({}) {{", invert_condition(&cond))];
        arm.extend(
            lines
                .get(i + 1..end)
                .unwrap_or(&[])
                .iter()
                .map(|l| format!("  {l}")),
        );
        arm.push(format!("{pad}}}"));
        lines.splice(i..end, arm);
        jumps = goto_index(lines);
        changed = true;
    }
    changed
}
