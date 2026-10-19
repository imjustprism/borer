//! Text rewrites after emission: strlen loops, merged chains, folded copies,
//! inverted conditions, and dead code.

use super::fcmp::FPred;
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
    let mut out: Option<Vec<String>> = None;
    let mut changed = false;
    let mut i = 0;
    while i < lines.len() {
        let Some(first) = pure(&lines[i]) else {
            if let Some(out) = out.as_mut() {
                out.push(lines[i].clone());
            }
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
            if let Some(out) = out.as_mut() {
                out.push(lines[i].clone());
            }
            i += 1;
            continue;
        }
        let out = out.get_or_insert_with(|| {
            let mut head = Vec::with_capacity(lines.len());
            head.extend(lines.iter().take(i).cloned());
            head
        });
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
    if let Some(out) = out {
        *lines = out;
    }
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
    let mut uses = temp_uses(lines);
    if uses.is_empty() {
        return false;
    }
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
        let named = uses.get(tmp).map_or(&[][..], Vec::as_slice);
        let fits = plain_targets
            && (is_register_name(var) || is_param(var))
            && named
                .iter()
                .all(|&j| j == i || !writes_var(lines[j].trim(), tmp))
            && named.first().is_none_or(|&j| j >= i);
        if !fits {
            i += 1;
            continue;
        }
        let last = named.last().copied().filter(|&j| j > i);
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
        if !clear {
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
        uses = temp_uses(lines);
        changed = true;
    }
    changed
}

/// The lines each temporary is named on, in order.
///
/// # Arguments
///
/// * `lines` - The body lines.
fn temp_uses(lines: &[String]) -> BTreeMap<String, Vec<usize>> {
    let mut uses: BTreeMap<String, Vec<usize>> = BTreeMap::new();
    for (k, l) in lines.iter().enumerate().filter(|(_, l)| l.contains("tmp_")) {
        for tok in tokens(l).filter(|w| is_temp_name(w)) {
            let at = uses.entry(tok.to_owned()).or_default();
            if at.last() != Some(&k) {
                at.push(k);
            }
        }
    }
    uses
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

/// Sends every jump to a label whose code is only another jump straight
/// to that jump's label.
///
/// `goto L;` where `L:` is followed by `goto M;`, across nothing but other
/// labels and the closing braces of `if`/`else` blocks, is `goto M;`. A
/// chain resolves to its last label; a cycle is left as it is. The label
/// line stays, so a path falling into it still takes the jump; once no
/// jump names it the label pass drops it.
///
/// # Arguments
///
/// * `lines` - The body lines, rewritten in place.
///
/// # Returns
///
/// Whether any jump was redirected.
pub(super) fn thread_jumps(lines: &mut [String]) -> bool {
    if !lines.iter().any(|l| l.contains("goto ")) {
        return false;
    }
    let mut next: BTreeMap<String, String> = BTreeMap::new();
    for (k, l) in lines.iter().enumerate() {
        let Some(name) = label_name(l) else {
            continue;
        };
        let mut j = k + 1;
        let target = loop {
            let Some(m) = lines.get(j) else {
                break None;
            };
            let t = m.trim();
            if label_name(m).is_some() {
                j += 1;
                continue;
            }
            if t == "}" {
                let ind = indent_of(m);
                let opener = lines[..j]
                    .iter()
                    .rev()
                    .find(|o| indent_of(o) == ind && o.trim().ends_with('{'))
                    .map(|o| o.trim());
                if opener.is_some_and(|o| o.starts_with("if (") || o.starts_with("} else")) {
                    j += 1;
                    continue;
                }
                break None;
            }
            break t
                .strip_prefix("goto ")
                .and_then(|g| g.strip_suffix(';'))
                .filter(|g| g.starts_with("L_"));
        };
        if let Some(target) = target
            && target != name
        {
            next.insert(name.to_owned(), target.to_owned());
        }
    }
    if next.is_empty() {
        return false;
    }
    let resolve = |start: &str| -> Option<String> {
        let mut at = next.get(start)?;
        for _ in 0..next.len() {
            match next.get(at.as_str()) {
                Some(m) if m == start => return None,
                Some(m) => at = m,
                None => return Some(at.clone()),
            }
        }
        None
    };
    let mut changed = false;
    for l in lines.iter_mut() {
        let Some(target) = goto_target(l).map(str::to_owned) else {
            continue;
        };
        let Some(last) = resolve(&target) else {
            continue;
        };
        let Some(cut) = l.strip_suffix(&format!("{target};")).map(str::len) else {
            continue;
        };
        l.truncate(cut);
        l.push_str(&last);
        l.push(';');
        changed = true;
    }
    changed
}

/// Where each line's block opens and where each line's block closes,
/// found in one walk.
///
/// `opener[k]` is the nearest earlier line, label lines apart, at a smaller
/// indentation than line `k`: the line that opens the block `k` sits in.
/// `closer[k]` is the first later line at line `k`'s indentation or less,
/// labels included: for an opener, the line that ends its block. `above[k]`
/// is the last earlier line at line `k`'s indentation or less, labels
/// included. A walk with three stacks of indentations finds them all,
/// where a scan per line would cost a pass over the text each.
#[derive(Debug, Default)]
struct Nest {
    /// The opener of each line's block.
    opener: Vec<Option<usize>>,
    /// The first later line not deeper than each line.
    closer: Vec<Option<usize>>,
    /// The last earlier line not deeper than each line.
    above: Vec<Option<usize>>,
}

impl Nest {
    /// Indexes the blocks of a body.
    ///
    /// # Arguments
    ///
    /// * `lines` - The body lines.
    fn of(lines: &[String]) -> Self {
        let mut nest = Self {
            opener: vec![None; lines.len()],
            closer: vec![None; lines.len()],
            above: vec![None; lines.len()],
        };
        let mut open: Vec<(usize, usize)> = Vec::new();
        let mut shallow: Vec<(usize, usize)> = Vec::new();
        let mut level: Vec<(usize, usize)> = Vec::new();
        for (k, l) in lines.iter().enumerate() {
            if l.trim().is_empty() {
                continue;
            }
            let d = indent_of(l);
            while let Some(&(ind, at)) = shallow.last()
                && ind >= d
            {
                nest.closer[at] = Some(k);
                shallow.pop();
            }
            shallow.push((d, k));
            while level.last().is_some_and(|&(ind, _)| ind > d) {
                level.pop();
            }
            nest.above[k] = level.last().map(|&(_, at)| at);
            level.push((d, k));
            if label_name(l).is_some() {
                nest.opener[k] = open
                    .iter()
                    .rev()
                    .find(|(ind, _)| *ind < d)
                    .map(|&(_, at)| at);
                continue;
            }
            while open.last().is_some_and(|&(ind, _)| ind >= d) {
                open.pop();
            }
            nest.opener[k] = open.last().map(|&(_, at)| at);
            open.push((d, k));
        }
        nest
    }
}

/// Tells whether a trimmed line opens a loop body.
///
/// # Arguments
///
/// * `t` - The line without indentation.
fn opens_loop(t: &str) -> bool {
    (t.starts_with("while (") || t.starts_with("for (") || t == "do {") && t.ends_with('{')
}

/// The loop a line belongs to through nothing but `if`/`else` blocks, and
/// that loop's closing line.
///
/// # Arguments
///
/// * `lines` - The body lines.
/// * `nest` - Their blocks ([`Nest::of`]).
/// * `at` - A line inside the loop.
///
/// # Returns
///
/// The opener and closer indices, or `None` when a `switch`, a `case` or
/// the function's top level comes first.
fn enclosing_loop(lines: &[String], nest: &Nest, at: usize) -> Option<(usize, usize)> {
    let mut k = at;
    let open = loop {
        let o = (*nest.opener.get(k)?)?;
        let t = lines[o].trim();
        if opens_loop(t) {
            break o;
        }
        if !(t.starts_with("if (") || t.starts_with("} else")) || !t.ends_with('{') {
            return None;
        }
        k = o;
    };
    let ind = indent_of(&lines[open]);
    let close = (*nest.closer.get(open)?)?;
    (indent_of(&lines[close]) == ind && lines[close].trim().starts_with('}'))
        .then_some((open, close))
}

/// Writes the loop exits the jumps spell as `break`, and a body's closing
/// `if (c) continue;` before a jump as a test of the jump.
///
/// A `goto L;` (bare or under a condition) inside a loop, through nothing
/// but `if`/`else` blocks, where `L:` follows the loop's closing line
/// across nothing that runs ([`falls_to_label`]), leaves the loop where
/// its end does: it is `break;`. A body that ends `if (c) continue;` then
/// `goto L;` or `break;` repeats exactly when `c` holds, as falling off
/// the body does, so the two lines are `if (!c) goto L;` or
/// `if (!c) break;` ([`invert_condition`]).
///
/// # Arguments
///
/// * `lines` - The body lines, rewritten in place.
///
/// # Returns
///
/// Whether anything was rewritten.
pub(super) fn loop_exits(lines: &mut Vec<String>) -> bool {
    if !lines
        .iter()
        .any(|l| l.contains("goto ") || l.ends_with(" continue;"))
    {
        return false;
    }
    let mut changed = false;
    let mut nest = Nest::of(lines);
    for i in 0..lines.len() {
        let t = lines[i].trim();
        let Some(target) = goto_target(t).filter(|_| is_goto(t) || conditional_goto(t).is_some())
        else {
            continue;
        };
        let Some((_, close)) = enclosing_loop(lines, &nest, i) else {
            continue;
        };
        if !falls_to_label(lines, close, target) {
            continue;
        }
        let Some(cut) = lines[i]
            .strip_suffix(&format!("goto {target};"))
            .map(str::len)
        else {
            continue;
        };
        lines[i].truncate(cut);
        lines[i].push_str("break;");
        changed = true;
    }
    let mut j = 2;
    while j < lines.len() {
        let body = indent_of(&lines[j - 1]);
        let leave = lines[j - 1].trim();
        let cond = lines[j - 2]
            .trim()
            .strip_prefix("if (")
            .and_then(|c| c.strip_suffix(") continue;"));
        let exit = (leave == "break;" || (is_goto(leave) && leave.ends_with(';')))
            .then(|| leave.to_owned());
        let shaped = lines[j].trim().starts_with('}') && indent_of(&lines[j - 2]) == body;
        let (Some(cond), Some(exit), true) = (cond, exit, shaped) else {
            j += 1;
            continue;
        };
        if enclosing_loop(lines, &nest, j - 1).is_none_or(|(_, close)| close != j) {
            j += 1;
            continue;
        }
        let line = format!("{}if ({}) {exit}", " ".repeat(body), invert_condition(cond));
        lines.splice(j - 2..j, [line]);
        nest = Nest::of(lines);
        changed = true;
    }
    changed
}

/// Swaps the two jumps of `if (c) goto A; goto B;` where the text before
/// `A:` is `if (!c) goto B;`.
///
/// Either order jumps to `A` exactly when `c` holds. Written as
/// `if (!c) goto B; goto A;`, the pair ends in the same test as the path
/// that falls into `A`, so the run between becomes an `else`
/// ([`absorb_else`]) and the shared test moves after it
/// ([`hoist_common_tails`]). The negation must match the other test as
/// written ([`invert_condition`]). A pair whose own test already stands
/// before `B:` is left as it is: it matches that path, and swapping it
/// would only invite the swap back.
///
/// # Arguments
///
/// * `lines` - The body lines, rewritten in place.
///
/// # Returns
///
/// Whether any pair was swapped.
pub(super) fn flip_jump_pairs(lines: &mut [String]) -> bool {
    if !lines.iter().any(|l| l.contains("goto ")) {
        return false;
    }
    let mut changed = false;
    let at_label: BTreeMap<String, usize> = lines
        .iter()
        .enumerate()
        .filter_map(|(k, l)| label_name(l).map(|n| (n.to_owned(), k)))
        .collect();
    for i in 0..lines.len().saturating_sub(1) {
        let ind = indent_of(&lines[i]);
        let Some((cond, first)) = conditional_goto(lines[i].trim()) else {
            continue;
        };
        let second = lines[i + 1].trim();
        let Some(second) = second
            .strip_prefix("goto ")
            .and_then(|g| g.strip_suffix(';'))
        else {
            continue;
        };
        if indent_of(&lines[i + 1]) != ind || first == second {
            continue;
        }
        let Some(&at) = at_label.get(first) else {
            continue;
        };
        let flipped = format!("if ({}) goto {second};", invert_condition(cond));
        if at <= i + 1 || lines[at - 1].trim() != flipped {
            continue;
        }
        let matched = at_label
            .get(second)
            .is_some_and(|&b| b > 0 && lines[b - 1].trim() == lines[i].trim());
        if matched {
            continue;
        }
        let pad = " ".repeat(ind);
        let jump = format!("{pad}goto {first};");
        lines[i] = format!("{pad}{flipped}");
        lines[i + 1] = jump;
        changed = true;
    }
    changed
}

/// Writes an `if` whose whole body is one `goto` as `if (c) goto L;`.
///
/// The braced and the one-line form jump alike; one spelling lets equal
/// tests read as equal lines ([`hoist_common_tails`]). An `if` with an
/// `else` keeps its braces.
///
/// # Arguments
///
/// * `lines` - The body lines, rewritten in place.
///
/// # Returns
///
/// Whether any `if` was collapsed.
pub(super) fn collapse_lone_gotos(lines: &mut Vec<String>) -> bool {
    if !lines.iter().any(|l| l.contains("goto ")) {
        return false;
    }
    let mut changed = false;
    let mut i = 0;
    while i + 2 < lines.len() {
        let ind = indent_of(&lines[i]);
        let head = lines[i].trim();
        let body = lines[i + 1].trim();
        let lone = head.starts_with("if (")
            && head.ends_with(") {")
            && is_goto(body)
            && indent_of(&lines[i + 1]) == ind + 2
            && lines[i + 2].trim() == "}"
            && indent_of(&lines[i + 2]) == ind;
        if !lone {
            i += 1;
            continue;
        }
        let line = format!("{}{} {body}", " ".repeat(ind), head.trim_end_matches(" {"));
        lines.splice(i..i + 3, [line]);
        changed = true;
        i += 1;
    }
    changed
}

/// Moves a statement both arms of an `if`/`else` end with to after it.
///
/// `if (a) { x; s; } else { y; s; }` runs `s` last on either path, so it
/// is `if (a) { x; } else { y; }` then `s`. Two arms ending in the same
/// `if (c) goto L;` leave one test the jump folds can then turn into
/// structure. The statement is one line ending in `;`, and each arm keeps
/// at least one line, so no arm is left empty. An `else if` chain is left
/// as it is.
///
/// # Arguments
///
/// * `lines` - The body lines, rewritten in place.
///
/// # Returns
///
/// Whether anything moved.
pub(super) fn hoist_common_tails(lines: &mut Vec<String>) -> bool {
    let mut changed = false;
    let mut nest: Option<Nest> = None;
    let mut i = 2;
    while i < lines.len() {
        if lines[i].trim() != "} else {" {
            i += 1;
            continue;
        }
        let ind = indent_of(&lines[i]);
        let last = lines[i - 1].trim();
        if indent_of(&lines[i - 1]) != ind + 2
            || !last.ends_with(';')
            || last.starts_with('}')
            || is_label(last)
        {
            i += 1;
            continue;
        }
        let b = nest.get_or_insert_with(|| Nest::of(lines));
        let (Some(&Some(open)), Some(&Some(close))) = (b.above.get(i), b.closer.get(i)) else {
            i += 1;
            continue;
        };
        let head = lines[open].trim();
        let shared = indent_of(&lines[open]) == ind
            && head.starts_with("if (")
            && head.ends_with(") {")
            && indent_of(&lines[close]) == ind
            && lines[close].trim() == "}"
            && i - open > 2
            && close - i > 2
            && indent_of(&lines[i - 1]) == ind + 2
            && indent_of(&lines[close - 1]) == ind + 2
            && lines[i - 1] == lines[close - 1];
        let t = lines[i - 1].trim();
        if !shared || !t.ends_with(';') || t.starts_with('}') || is_label(t) {
            i += 1;
            continue;
        }
        let moved = format!("{}{t}", " ".repeat(ind));
        lines.remove(close - 1);
        lines.insert(close, moved);
        lines.remove(i - 1);
        nest = None;
        changed = true;
        i -= 1;
    }
    changed
}

/// Tells whether the text after line `from` reaches the label without
/// running anything.
///
/// Only closing braces of `if`/`else` blocks and other labels may lie
/// between them, since falling out of such a block continues right after
/// it and a label runs nothing, while falling out of a loop body repeats
/// the loop and out of a `case` runs the next one.
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
            if t.strip_suffix(':') == Some(label) {
                return true;
            }
            if label_name(l).is_some() {
                j += 1;
                continue;
            }
            return false;
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
/// A condition negated as a whole (`!(c)`, `!f(x)`) loses its negation,
/// and a lone call (`f(x)`) gains one.
/// One comparison outside every bracket and string flips its operator: a
/// float relation is a comparison macro until the text is final
/// ([`spell_float_relations`]), so every operator here compares integers,
/// or floats by `==` and `!=`, which flip exactly. A guard chain negates
/// operand by operand
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
    if cond.ends_with(')') && !cond.starts_with('(') && negated_whole(&format!("!{cond}")).is_some()
    {
        return format!("!{cond}");
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
/// `isunordered(x, y)`, leaving `isunordered(x, y) || x != y`; but C's
/// `!=` on floating point is already true when an operand is NaN and its
/// `==` already false, so each pair is the comparison alone, and
/// `!isunordered(x, y) && x == y` is `x == y`.
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
            let (offset, len, unordered) = found;
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
            from = close;
        }
    }
    changed
}

/// The C99 comparison macros the renderer spells an ordered float relation
/// with, each with the predicate it asks; the longer names come first, so
/// `isgreater` is never found inside `isgreaterequal`.
const RELATION_MACROS: [(&str, FPred); 4] = [
    ("isgreaterequal", FPred::Oge),
    ("islessequal", FPred::Ole),
    ("isgreater", FPred::Ogt),
    ("isless", FPred::Olt),
];

/// Writes each float relation macro of finished text as the C operator.
///
/// The renderer spells `a < b` over floats as `isless(a, b)` so that no
/// text pass inverts it into `a >= b`, which NaN tells apart from
/// `!(a < b)` ([`super::fcmp::FPred`]). Once no pass inverts anything, the
/// call reads better as the operator: `isless(a, b)` becomes `a < b` and
/// `!isless(a, b)` becomes `!(a < b)`. The relation is parenthesized
/// unless what surrounds the call binds looser than a comparison, and an
/// operand is parenthesized when it holds an operator as loose.
///
/// # Arguments
///
/// * `text` - The finished function.
///
/// # Returns
///
/// The text with the macros spelled as operators.
pub(super) fn spell_float_relations(text: &str) -> String {
    if !RELATION_MACROS.iter().any(|(name, _)| text.contains(name)) {
        return text.to_owned();
    }
    text.split_inclusive('\n').map(spell_relations_in).collect()
}

/// Writes each float relation macro of one line as the C operator
/// ([`spell_float_relations`]).
///
/// # Arguments
///
/// * `line` - One line.
fn spell_relations_in(line: &str) -> String {
    let mut out = line.to_owned();
    let mut from = 0;
    while let Some((at, name, p)) = next_relation_macro(&out, from) {
        let open = at + name.len();
        let Some(close) = matching_paren(&out, open) else {
            from = open;
            continue;
        };
        let Some(((l, r), Some((rel, false)))) = out
            .get(open + 1..close)
            .and_then(split_pair)
            .map(|pair| (pair, p.operator()))
        else {
            from = close;
            continue;
        };
        let side = |t: &str| {
            if loose(t) {
                format!("({t})")
            } else {
                t.to_owned()
            }
        };
        let relation = format!("{} {rel} {}", side(l), side(r));
        let negated = out[..at].ends_with('!');
        let start = if negated { at - 1 } else { at };
        let text = if negated || !looser_around(&out[..start], &out[close + 1..]) {
            let not = if negated { "!" } else { "" };
            format!("{not}({relation})")
        } else {
            relation
        };
        out.replace_range(start..=close, &text);
        from = start + text.len();
    }
    out
}

/// The first float relation macro called at or after an offset.
///
/// # Arguments
///
/// * `line` - The text.
/// * `from` - The byte offset to search from.
///
/// # Returns
///
/// The call's offset, the macro's name and the predicate it asks.
fn next_relation_macro(line: &str, from: usize) -> Option<(usize, &'static str, FPred)> {
    RELATION_MACROS
        .iter()
        .filter_map(|&(name, p)| {
            let mut at = from;
            loop {
                let i = at + line.get(at..)?.find(name)?;
                at = i + 1;
                let before = line[..i].chars().next_back();
                let called = line[i + name.len()..].starts_with('(');
                if called && !before.is_some_and(is_ident_char) {
                    return Some((i, name, p));
                }
            }
        })
        .min_by_key(|(i, ..)| *i)
}

/// Tells whether an operand holds, outside brackets, an operator that binds
/// as loosely as a comparison or looser, so that it needs parentheses as one
/// side of one.
///
/// # Arguments
///
/// * `t` - The operand's text.
fn loose(t: &str) -> bool {
    const LOOSE: [&str; 13] = [
        " < ", " > ", " <= ", " >= ", " == ", " != ", " & ", " | ", " ^ ", " && ", " || ", " ? ",
        " = ",
    ];
    let mut depth = 0i32;
    t.char_indices().any(|(i, c)| {
        match c {
            '(' | '[' => depth += 1,
            ')' | ']' => depth -= 1,
            _ => {}
        }
        depth == 0 && LOOSE.iter().any(|op| t[i..].starts_with(op))
    })
}

/// Tells whether what surrounds a value binds looser than a comparison, so
/// that a comparison put in the value's place needs no parentheses.
///
/// # Arguments
///
/// * `before` - The text before the value.
/// * `after` - The text after it.
fn looser_around(before: &str, after: &str) -> bool {
    let b = before.trim_end();
    let a = after.trim_start();
    let assigns = b.ends_with('=') && !["==", "!=", "<=", ">="].iter().any(|op| b.ends_with(op));
    let left = b.is_empty()
        || assigns
        || ["(", ",", "&&", "||", "?", ":", "{", ";", "return"]
            .iter()
            .any(|t| b.ends_with(t));
    let right = a.is_empty()
        || [")", ",", "&&", "||", "?", ":", ";", "]"]
            .iter()
            .any(|t| a.starts_with(t));
    left && right
}

/// The first unordered test in a text: the `isunordered(` call, negated or
/// not.
///
/// # Arguments
///
/// * `t` - The text searched.
///
/// # Returns
///
/// The test's offset, the length of its head up to and including the `(`,
/// and whether it holds on an unordered outcome.
fn unordered_test(t: &str) -> Option<(usize, usize, bool)> {
    let mut from = 0;
    while let Some(i) = t
        .get(from..)
        .and_then(|s| s.find("isunordered("))
        .map(|i| from + i)
    {
        from = i + 1;
        match t.get(..i).and_then(|h| h.chars().next_back()) {
            Some('!') => return Some((i - 1, "!isunordered(".len(), false)),
            Some(c) if is_ident_char(c) => {}
            _ => return Some((i, "isunordered(".len(), true)),
        }
    }
    None
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
/// a value nothing reads; or, for a call's result, when no other line
/// reads it at all, every other mention assigning it (a register several
/// calls write and a condition no longer reads); or when the lines that
/// follow it in order
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
    let mut mentions: FxHashMap<&str, usize> = FxHashMap::default();
    let mut reads: FxHashMap<&str, usize> = FxHashMap::default();
    for line in lines {
        for word in tokens(line).filter(|w| is_register_name(w)) {
            *mentions.entry(word).or_default() += 1;
        }
        let t = line.trim();
        let read = t
            .strip_suffix(';')
            .and_then(|s| s.rsplit_once(" = "))
            .filter(|(targets, _)| targets.split(" = ").all(is_ident))
            .map_or(t, |(_, rhs)| rhs);
        for word in tokens(read).filter(|w| is_register_name(w)) {
            *reads.entry(word).or_default() += 1;
        }
    }
    let own = |name: &str, prefix: &str| {
        name.strip_prefix(prefix)
            .is_some_and(|n| !n.is_empty() && n.bytes().all(|c| c.is_ascii_hexdigit()))
    };
    let mut out: Option<Vec<String>> = None;
    for (at, line) in lines.iter().enumerate() {
        let parts: Vec<&str> = line
            .trim()
            .strip_suffix(';')
            .map(|t| t.split(" = ").collect())
            .unwrap_or_default();
        let Some((rhs, targets)) = parts.split_last().filter(|(_, t)| !t.is_empty()) else {
            if let Some(out) = out.as_mut() {
                out.push(line.clone());
            }
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
                        || (call
                            && reads.get(name).copied().unwrap_or(0)
                                == tokens(rhs).filter(|w| w == name).count())
                        || dead_after(lines, at, name, live_out));
                let itself = local(name) && name == rhs;
                !(unread || itself)
            })
            .collect();
        if kept.len() == targets.len() {
            if let Some(out) = out.as_mut() {
                out.push(line.clone());
            }
            continue;
        }
        let out = out.get_or_insert_with(|| {
            let mut head = Vec::with_capacity(lines.len());
            head.extend(lines.iter().take(at).cloned());
            head
        });
        if !kept.is_empty() {
            out.push(format!("{}{} = {rhs};", pad_of(line), kept.join(" = ")));
        } else if call {
            out.push(format!("{}{rhs};", pad_of(line)));
        }
    }
    out
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
pub(super) fn lone_call(rhs: &str) -> bool {
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
pub(super) fn second_result(rhs: &str) -> bool {
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
/// only when every jump to it comes from inside the run. A run may also
/// end by leaving its block when the closing braces from there fall to
/// `L` ([`run_to_dedent`], [`falls_to_label`]); it then holds no label.
/// Runs longer than 200 lines are left alone. The arm may close an `if`/`else if` chain
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
    if !lines.iter().any(|l| l.contains("goto ")) {
        return false;
    }
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
        let name = target;
        let target = format!("{target}:");
        let end = match run_to_label(lines, i + 2, outer, &target, RunLabels::Contained, RUN_MAX)
            .filter(|(e, _)| *e > i + 2)
        {
            Some((end, inner)) => {
                if !jumps_contained(&jumps, &inner, i, end) {
                    continue;
                }
                end
            }
            None => match run_to_dedent(lines, i + 2, outer, RUN_MAX) {
                Some(end) if falls_to_label(lines, end - 1, name) => end,
                Some(_) | None => continue,
            },
        };
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

/// Finds the closing brace that ends a label-free run starting at `from`
/// by leaving the block the run sits in.
///
/// Every line of the run stands at `ind` or deeper, and none is a label,
/// a `case` or a `default`; the run does not open with a brace that
/// closes a block from before it.
///
/// # Arguments
///
/// * `lines` - The body lines.
/// * `from` - The first line of the run.
/// * `ind` - The run's indentation.
/// * `max` - Longest run looked at.
///
/// # Returns
///
/// The index of the `}` line below `ind`, when the run is not empty.
fn run_to_dedent(lines: &[String], from: usize, ind: usize, max: usize) -> Option<usize> {
    if lines.get(from)?.trim().starts_with('}') {
        return None;
    }
    for (j, l) in lines.iter().enumerate().skip(from).take(max) {
        let t = l.trim();
        if indent_of(l) < ind {
            return (t == "}" && j > from).then_some(j);
        }
        if is_label(l) || t.starts_with("case ") || t.starts_with("default:") {
            return None;
        }
    }
    None
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
/// inverted condition and the label is left for the pruning pass. A run
/// may also end by leaving its block when the closing braces from there
/// fall to the label ([`run_to_dedent`]); it then holds no label. Runs
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
    if !lines.iter().any(|l| l.contains(") goto ")) {
        return false;
    }
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
        let end = match run_to_label(lines, i + 1, ind, &target, labels, SPAN_MAX)
            .filter(|(e, _)| *e > i + 1)
        {
            Some((end, inner)) => {
                if !jumps_contained(&jumps, &inner, i, end) {
                    continue;
                }
                end
            }
            None => match run_to_dedent(lines, i + 1, ind, SPAN_MAX) {
                Some(end) if falls_to_label(lines, end - 1, &label) => end,
                Some(_) | None => continue,
            },
        };
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

#[cfg(test)]
mod jump_tests {
    use super::{Nest, flip_jump_pairs, loop_exits, thread_jumps};

    /// Each line's block opener skips labels, and each opener's closer is
    /// the first line back at its depth, a label included.
    #[test]
    #[expect(
        clippy::missing_panics_doc,
        reason = "assertions are the point of a test"
    )]
    fn the_nest_finds_openers_and_closers() {
        let lines = body(&[
            "while (1) {",
            "  if (a1 != 0) {",
            "    a1 -= 1;",
            "  L_1:",
            "    a2 += 1;",
            "  }",
            "}",
            "L_2:",
            "return 0;",
        ]);
        let nest = Nest::of(&lines);
        assert_eq!(nest.opener[2], Some(1));
        assert_eq!(nest.opener[4], Some(1));
        assert_eq!(nest.opener[3], Some(0));
        assert_eq!(nest.opener[1], Some(0));
        assert_eq!(nest.opener[0], None);
        assert_eq!(nest.closer[1], Some(3));
        assert_eq!(nest.closer[0], Some(6));
        assert_eq!(nest.closer[6], Some(7));
        assert_eq!(nest.above[5], Some(3));
        assert_eq!(nest.above[3], Some(1));
        assert_eq!(nest.above[6], Some(0));
        assert_eq!(nest.above[0], None);
    }

    /// A jump to the label after a loop is `break`, and a body that ends
    /// `if (c) continue; goto L;` tests the jump instead.
    #[test]
    #[expect(
        clippy::missing_panics_doc,
        reason = "assertions are the point of a test"
    )]
    fn a_jump_past_the_loop_end_is_a_break() {
        let mut lines = body(&[
            "while (1) {",
            "  if (a1[i] == x) goto L_1;",
            "  i += 1;",
            "  if (n != i) continue;",
            "  goto L_2;",
            "}",
            "L_1:",
            "return i;",
            "L_2:",
            "return 0;",
        ]);
        assert!(loop_exits(&mut lines));
        assert_eq!(lines[1], "  if (a1[i] == x) break;");
        assert_eq!(lines[3], "  if (n == i) goto L_2;");
        assert_eq!(lines[4], "}");
    }

    /// A jump out of an inner loop, or out of a `switch`, is no `break` of
    /// the outer loop.
    #[test]
    #[expect(
        clippy::missing_panics_doc,
        reason = "assertions are the point of a test"
    )]
    fn a_jump_past_an_outer_loop_stays() {
        let mut lines = body(&[
            "while (1) {",
            "  while (a2 != 0) {",
            "    if (a1 == 0) goto L_1;",
            "    a2 -= 1;",
            "  }",
            "  switch (a3) {",
            "  case 1:",
            "    goto L_1;",
            "  }",
            "}",
            "L_1:",
            "return 0;",
        ]);
        assert!(!loop_exits(&mut lines));
    }

    /// The lines of a body, one per entry.
    ///
    /// # Arguments
    ///
    /// * `text` - The lines.
    fn body(text: &[&str]) -> Vec<String> {
        text.iter().map(|l| (*l).to_owned()).collect()
    }

    /// A jump to a label whose code is one more jump goes to that jump's
    /// label, through a chain, and a closing brace between does not stop it.
    #[test]
    #[expect(
        clippy::missing_panics_doc,
        reason = "assertions are the point of a test"
    )]
    fn a_jump_to_a_jump_goes_to_its_label() {
        let mut lines = body(&[
            "if (a1 == 0) goto L_1;",
            "sub_1(a1);",
            "if (a2 != 0) {",
            "  L_1:",
            "}",
            "goto L_2;",
            "L_2:",
            "goto L_3;",
            "L_3:",
            "return 0;",
        ]);
        assert!(thread_jumps(&mut lines));
        assert_eq!(lines[0], "if (a1 == 0) goto L_3;");
        assert_eq!(lines[5], "goto L_3;");
    }

    /// A jump that is its own target is left alone.
    #[test]
    #[expect(
        clippy::missing_panics_doc,
        reason = "assertions are the point of a test"
    )]
    fn a_cycle_of_jumps_is_left_alone() {
        let mut lines = body(&["L_1:", "goto L_2;", "L_2:", "goto L_1;"]);
        assert!(!thread_jumps(&mut lines));
    }

    /// A jump pair swaps to the order of the test before its label, and
    /// only then.
    #[test]
    #[expect(
        clippy::missing_panics_doc,
        reason = "assertions are the point of a test"
    )]
    fn a_jump_pair_takes_the_order_of_the_test_before_its_label() {
        let mut lines = body(&[
            "if (a1 != 0) {",
            "  if (a2 == 0) goto L_1;",
            "  goto L_2;",
            "}",
            "if (a2 != 0) goto L_2;",
            "L_1:",
            "return 0;",
        ]);
        assert!(flip_jump_pairs(&mut lines));
        assert_eq!(lines[1], "  if (a2 != 0) goto L_2;");
        assert_eq!(lines[2], "  goto L_1;");
        let mut other = body(&[
            "if (a2 == 0) goto L_1;",
            "goto L_2;",
            "if (a3 != 0) goto L_2;",
            "L_1:",
        ]);
        assert!(!flip_jump_pairs(&mut other));
        let mut both = body(&[
            "if (a2 == 0) goto L_1;",
            "goto L_2;",
            "if (a2 == 0) goto L_1;",
            "L_2:",
            "sub_2(a1);",
            "if (a2 != 0) goto L_2;",
            "L_1:",
        ]);
        assert!(!flip_jump_pairs(&mut both));
    }
}

#[cfg(test)]
mod spell_tests {
    use super::spell_float_relations;

    /// A comparison macro becomes the operator, parenthesized where what
    /// surrounds it or one of its operands binds as tightly, and a negated
    /// macro becomes the negated comparison.
    #[test]
    #[expect(
        clippy::missing_panics_doc,
        reason = "assertions are the point of a test"
    )]
    fn float_relations_spell_as_operators() {
        let cases = [
            ("if (isless(a1, a2)) {\n", "if (a1 < a2) {\n"),
            ("return !isgreater(a1, a2);\n", "return !(a1 > a2);\n"),
            ("x = isless(a1, a2) + 1;\n", "x = (a1 < a2) + 1;\n"),
            (
                "if (isgreaterequal(a1 + 1.0, a2) && a3 != 0) {\n",
                "if (a1 + 1.0 >= a2 && a3 != 0) {\n",
            ),
            (
                "v = islessequal(a1 ? a2 : a3, 2.0);\n",
                "v = (a1 ? a2 : a3) <= 2.0;\n",
            ),
            ("thisless(a1, a2);\n", "thisless(a1, a2);\n"),
            (
                "if (!islessequal(a1, a2) || isunordered(a1, a2)) {\n",
                "if (!(a1 <= a2) || isunordered(a1, a2)) {\n",
            ),
        ];
        for (text, want) in cases {
            assert_eq!(spell_float_relations(text), want, "{text}");
        }
    }
}
