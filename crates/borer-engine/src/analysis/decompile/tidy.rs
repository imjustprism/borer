//! The last cleanup: dropped results and dead code, single-use blocks moved,
//! early exits flattened.

use super::*;

/// Summarizes what a body mutates, from its cleaned text.
///
/// Writes through a parameter or `this` at a constant offset (`*(uint32_t*)
/// (a1 + 0x38) = ...`, compound assignments and atomic intrinsics included)
/// are listed as `a1+0x38`; globals assigned are listed by name; globals
/// only read are listed as reads; stores through any other pointer, an
/// indexed field included, are counted. An agent
/// deciding whether to read a body gets the answer in one line.
///
/// # Arguments
///
/// * `body` - The cleaned body text.
///
/// # Returns
///
/// The `effects:` line's content, or `None` when the body stores nothing
/// and reads no global.
pub fn effects_line(body: &str) -> Option<String> {
    /// Most items named per list before `+N more`.
    const SHOWN: usize = 8;
    let mut writes: Vec<String> = Vec::new();
    let mut global_writes: Vec<String> = Vec::new();
    let mut global_reads: BTreeSet<String> = BTreeSet::new();
    let mut other = 0usize;
    let field = |lhs: &str| -> Option<String> {
        let inner = lhs.strip_prefix("*(")?;
        let (_, target) = inner.split_once(')')?;
        let target = target.trim();
        let (base, off) = match target.strip_prefix('(').and_then(|t| t.strip_suffix(')')) {
            Some(t) => match t.split_once(" + ") {
                Some((b, o)) => (b, Some(o)),
                None => (t, None),
            },
            None => (target, None),
        };
        let param = base == "this" || is_param_name(base);
        let constant = off.is_none_or(|o| parse_const(o).is_some());
        (param && constant).then(|| match off {
            Some(o) => format!("{base}+{o}"),
            None => base.to_owned(),
        })
    };
    for line in body.lines() {
        let t = line.trim();
        for word in tokens(t).filter(|w| is_global_name(w)) {
            global_reads.insert(word.to_owned());
        }
        let lhs = if let Some(call) = t
            .strip_prefix("tmp_")
            .and_then(|r| r.split_once(" = atomic_"))
            .map(|(_, call)| call)
            .or_else(|| t.strip_prefix("atomic_"))
        {
            call.split_once('(')
                .map(|(_, args)| args.split_once(", ").map_or(args, |(a, _)| a))
        } else {
            t.find('=')
                .filter(|&i| {
                    let before = t.as_bytes().get(i.wrapping_sub(1)).copied();
                    let after = t.as_bytes().get(i + 1).copied();
                    after != Some(b'=') && !matches!(before, Some(b'!' | b'<' | b'>' | b'='))
                })
                .map(|i| {
                    t[..i]
                        .trim_end_matches(['+', '-', '|', '&', '^', '*', '/', '%'])
                        .trim()
                })
        };
        let Some(lhs) = lhs else { continue };
        if lhs.starts_with("if ") || is_return(lhs) || starts_with_keyword(lhs, "while") {
            continue;
        }
        if is_global_name(lhs) {
            if !global_writes.iter().any(|w| w == lhs) {
                global_writes.push(lhs.to_owned());
            }
        } else if let Some(f) = field(lhs) {
            if !writes.contains(&f) {
                writes.push(f);
            }
        } else if lhs.starts_with("*(") {
            other += 1;
        }
    }
    for w in &global_writes {
        global_reads.remove(w);
    }
    let list = |items: &[String]| {
        let shown: Vec<&str> = items.iter().take(SHOWN).map(String::as_str).collect();
        let more = items.len().saturating_sub(SHOWN);
        if more > 0 {
            format!("{} (+{more} more)", shown.join(", "))
        } else {
            shown.join(", ")
        }
    };
    let mut parts: Vec<String> = Vec::new();
    let mut all_writes = writes;
    all_writes.extend(global_writes);
    if !all_writes.is_empty() {
        parts.push(format!("writes {}", list(&all_writes)));
    }
    let reads: Vec<String> = global_reads.into_iter().collect();
    if !reads.is_empty() {
        parts.push(format!("reads {}", list(&reads)));
    }
    if other > 0 {
        parts.push(format!(
            "{other} other store{}",
            if other == 1 { "" } else { "s" }
        ));
    }
    (!parts.is_empty()).then(|| parts.join("; "))
}

/// Drops the value from a function's returns when no caller reads it.
///
/// Discovery records a verdict per function: whether any call site uses the
/// result. A function every caller ignores hands nothing back, so its
/// `return rax;` is a value computed for nobody, and saying `return;`
/// lets the dead-assignment pass drop whatever fed it and the header call
/// the function `void`. A declared signature overrules the verdict.
///
/// # Arguments
///
/// * `body` - The emitted body, before cleanup.
///
/// # Returns
///
/// The body with every returned value dropped.
pub(super) fn drop_returned_values(body: &str) -> String {
    let mut out = String::with_capacity(body.len());
    for line in body.lines() {
        let t = line.trim();
        let returned = t
            .strip_prefix("return ")
            .and_then(|e| e.strip_suffix(';'))
            .filter(|e| !e.is_empty());
        let Some(expr) = returned else {
            let _ = writeln!(out, "{line}");
            continue;
        };
        let pad = pad_of(line);
        if impure(expr) {
            let _ = writeln!(out, "{pad}{expr};");
        }
        let _ = writeln!(out, "{pad}return;");
    }
    out
}

/// Drops the assignment of a call's result to the return register right
/// before a `return;`, in a function that returns nothing.
///
/// The join before a shared epilogue needed the register on every path
/// while the function's own result was unknown, and the return then found
/// nothing to hand back: `rax = f(); return;` reads `f(); return;`. The
/// `return;` that ends the body is the end of the function and goes too
/// unless a label before it would be left closing the body or the block
/// right before it also ends in `return;`, and a final `default: {
/// return; }` closing a `switch` at the end of the body goes with it.
///
/// # Arguments
///
/// * `body` - The emitted body.
/// * `reg` - The return register's name, `rax` or `eax`.
///
/// # Returns
///
/// The body with the dead assignments dropped, newline-terminated.
pub(super) fn drop_dead_results(body: &str, reg: &str) -> String {
    let mut lines: Vec<&str> = body.lines().collect();
    if let [ref earlier @ .., before, last] = lines[..]
        && last == "return;"
        && !before.trim_end().ends_with(':')
        && before.trim() != "return;"
        && earlier.last().is_none_or(|l| l.trim() != "return;")
    {
        lines.pop();
    } else if let [.., inner_ret, close_brace, last] = lines[..]
        && last == "return;"
        && close_brace == "}"
        && inner_ret.trim() == "return;"
        && indent_of(inner_ret) == 2
        && lines
            .iter()
            .rev()
            .skip(2)
            .find(|l| indent_of(l) == 0)
            .is_some_and(|l| l.starts_with("if (") && l.ends_with(") {"))
    {
        let n = lines.len();
        lines.remove(n - 1);
        lines.remove(n - 3);
    }
    if let [.., d_open, d_ret, d_close, sw_close] = lines[..]
        && d_open.trim() == "default: {"
        && d_ret.trim() == "return;"
        && d_close.trim() == "}"
        && sw_close == "}"
    {
        let n = lines.len();
        lines.drain(n - 4..n - 1);
    }
    let mut out = String::with_capacity(body.len());
    let prefix = format!("{reg} = ");
    for (i, line) in lines.iter().enumerate() {
        let before_return = lines
            .get(i + 1)
            .is_some_and(|n| n.trim() == "return;" && indent_of(n) == indent_of(line));
        match line.trim().strip_prefix(&prefix) {
            Some(rhs) if before_return && rhs.ends_with(';') && impure(rhs) => {
                let _ = writeln!(out, "{}{rhs}", pad_of(line));
            }
            _ => {
                let _ = writeln!(out, "{line}");
            }
        }
    }
    out
}

/// Which loop or switch line `at` stands in, by the line that opens it.
///
/// `break` and `continue` bind to the innermost one, so text that carries
/// either only means the same thing where this is the same loop. Two loops
/// nested equally deep are still two loops.
///
/// # Arguments
///
/// * `lines` - The body lines.
/// * `at` - Index of the line asked about.
///
/// # Returns
///
/// The index of the line opening the innermost loop or switch around `at`,
/// or `None` when the line is in none.
pub(super) fn enclosing_loop(lines: &[String], at: usize) -> Option<usize> {
    let mut open: Vec<(Scope, usize)> = Vec::new();
    for (i, l) in lines.iter().take(at).enumerate() {
        let t = l.trim();
        if closes_scope(t) {
            open.pop();
        }
        if let Some(s) = opens_scope(t) {
            open.push((s, i));
        }
    }
    open.iter()
        .rev()
        .find(|(s, _)| *s != Scope::Block)
        .map(|&(_, i)| i)
}

/// Tells whether a run of lines leaves a loop around it, rather than one it
/// opens itself.
///
/// # Arguments
///
/// * `body` - The lines that would move.
pub(super) fn carries_a_transfer(body: &[String]) -> bool {
    let mut open: Vec<Scope> = Vec::new();
    body.iter().any(|l| {
        let level = at_loop_level(l, &mut open);
        let t = l.trim();
        level && (breaks(t) || continues(t))
    })
}

/// Moves a block only one jump reaches to where that jump is.
///
/// A label with a single `goto` to it, whose own code cannot be fallen into
/// from above and ends in a transfer, is not a shared exit: it is the
/// continuation of that one jump, parked below. Moving it up removes the
/// jump and the label together, and duplicates nothing, since the block had
/// one reader. `goto L;` becomes the block, `if (c) goto L;` becomes
/// `if (c) { block }`, and a switch arm takes it the same way.
///
/// The block runs from the label to the first line at a lower indentation
/// or the next label at its own, and it moves only when the line above the
/// label transfers away (so nothing falls into it), the jump is forward,
/// the jump sits at or below the label's indentation, and no label inside
/// the block is reached from outside it. A block that breaks or continues
/// a loop around it moves only within that same loop, since those words
/// would otherwise leave a different one.
///
/// # Arguments
///
/// * `lines` - The body lines, rewritten in place.
///
/// # Returns
///
/// Whether a block moved.
pub(super) fn move_single_use_blocks(lines: &mut Vec<String>) -> bool {
    if !lines.iter().any(|l| l.contains("goto ")) {
        return false;
    }
    let jumps = goto_index(lines);
    for (at, line) in lines.iter().enumerate() {
        let Some(label) = label_name(line) else {
            continue;
        };
        let Some([src]) = jumps.get(label).map(Vec::as_slice) else {
            continue;
        };
        let src = *src;
        let ind = indent_of(line);
        if src >= at || indent_of(&lines[src]) < ind {
            continue;
        }
        if at > 0
            && let Some(prev) = lines[..at].iter().rfind(|l| !l.trim().is_empty())
            && !transfers(prev)
        {
            continue;
        }
        let mut end = at + 1;
        while end < lines.len() {
            let t = lines[end].trim();
            if t.is_empty() {
                end += 1;
                continue;
            }
            if indent_of(&lines[end]) < ind
                || (indent_of(&lines[end]) == ind && is_label(&lines[end]))
            {
                break;
            }
            end += 1;
        }
        let body: Vec<String> = lines[at + 1..end]
            .iter()
            .filter(|l| !l.trim().is_empty())
            .cloned()
            .collect();
        let Some(last) = body.last() else {
            continue;
        };
        if !transfers(last) {
            continue;
        }
        if carries_a_transfer(&body) && enclosing_loop(lines, src) != enclosing_loop(lines, at) {
            continue;
        }
        let inner: Vec<String> = body
            .iter()
            .filter_map(|l| label_name(l).map(str::to_owned))
            .collect();
        if !jumps_contained(&jumps, &inner, at, end) {
            continue;
        }
        let shift = indent_of(&lines[src]).saturating_sub(ind);
        let moved: Vec<String> = body
            .iter()
            .map(|l| format!("{}{l}", " ".repeat(shift)))
            .collect();
        let t = lines[src].trim();
        let pad = pad_of(&lines[src]);
        let mut arm: Vec<String> = Vec::new();
        if is_goto(t) {
            arm = moved;
        } else if let Some(head) = t.strip_suffix(&format!("goto {label};")) {
            let head = head.trim_end();
            if head.starts_with("if (") || is_case(head) {
                arm.push(format!("{pad}{head} {{"));
                arm.extend(moved.iter().map(|l| format!("  {l}")));
                arm.push(format!("{pad}}}"));
            } else {
                continue;
            }
        } else {
            continue;
        }
        lines.drain(at..end);
        lines.splice(src..=src, arm);
        return true;
    }
    false
}

/// Copies a short returning tail to the jumps that target it.
///
/// A label followed by a run of at most eight lines ending in a `return`
/// at its own indentation is a shared exit (`errno = 22; return 0;`). The
/// run may nest, as long as its braces balance before that `return`, so a
/// tail that tests something on its way out counts too. Every `if (c) goto L;` that targets it becomes `if (c) {
/// tail }`, every plain `goto L;` becomes the tail itself, and a switch arm
/// that dispatches to one (`case 3: goto L;`) takes the tail in place, so
/// the reader sees what happens instead of where to look. The original stays where it
/// is for whatever falls into it; once nothing jumps there the label is
/// pruned and, when the text before it has already left, the dead-text
/// rule removes it. The rule runs only once the other cleanups have
/// settled, so a jump they can drop or fold outright is never copied. A
/// tail that breaks or continues a loop around it is left alone, since the
/// copies would land in other loops.
///
/// # Arguments
///
/// * `lines` - The body lines, rewritten in place.
///
/// # Returns
///
/// Whether anything was copied.
pub(super) fn inline_terminal_tails(lines: &mut Vec<String>) -> bool {
    /// Longest tail worth copying.
    const TAIL_MAX: usize = 8;
    if !lines.iter().any(|l| l.contains("goto ")) {
        return false;
    }
    let mut tails: BTreeMap<String, Vec<String>> = BTreeMap::new();
    for (i, line) in lines.iter().enumerate() {
        let Some(label) = label_name(line) else {
            continue;
        };
        let ind = indent_of(line);
        let mut run: Vec<String> = Vec::new();
        let mut depth = 0i32;
        for l in lines.iter().skip(i + 1).take(TAIL_MAX) {
            let t = l.trim();
            if t.is_empty()
                || is_label(l)
                || t.starts_with("case ")
                || t.contains(" goto ")
                || is_goto(t)
                || (depth == 0 && indent_of(l) != ind)
            {
                break;
            }
            run.push(format!(
                "{}{t}",
                " ".repeat(indent_of(l).saturating_sub(ind))
            ));
            depth += brace_delta(t);
            if depth < 0 {
                break;
            }
            if depth == 0 && is_return(t) {
                if !carries_a_transfer(&run) {
                    tails.insert(label.to_owned(), run);
                }
                break;
            }
        }
    }
    if tails.is_empty() {
        return false;
    }
    let mut out: Vec<String> = Vec::with_capacity(lines.len());
    let mut changed = false;
    for line in lines.iter() {
        let t = line.trim();
        let pad = pad_of(line);
        match goto_target(t).and_then(|l| tails.get(l)) {
            Some(tail) if is_goto(t) => {
                out.extend(tail.iter().map(|s| format!("{pad}{s}")));
                changed = true;
            }
            Some(tail) if t.starts_with("if (") => {
                let cond = &t[..t.len() - t.rsplit_once(" goto ").map_or(0, |(_, g)| g.len() + 6)];
                out.push(format!("{pad}{cond} {{"));
                out.extend(tail.iter().map(|s| format!("{pad}  {s}")));
                out.push(format!("{pad}}}"));
                changed = true;
            }
            Some(tail) if t.starts_with("case ") || t.starts_with("default:") => {
                let label = &t[..t.len() - t.rsplit_once("goto ").map_or(0, |(_, g)| g.len() + 5)];
                match tail.as_slice() {
                    [one] => out.push(format!("{pad}{label}{one}")),
                    many => {
                        out.push(format!("{pad}{label}{{"));
                        out.extend(many.iter().map(|s| format!("{pad}  {s}")));
                        out.push(format!("{pad}}}"));
                    }
                }
                changed = true;
            }
            _ => out.push(line.clone()),
        }
    }
    if changed {
        *lines = out;
    }
    changed
}

/// Turns a long `if` whose body never falls out, followed by a short tail
/// ending in a terminal line, into an early exit with the body at the same
/// level.
///
/// The shape is `if (c) { BODY } TAIL` where BODY's last statement at its
/// own level is a `return`, `goto`, `break` or `continue`, so no path
/// through BODY reaches the line after the block, and TAIL is at most a
/// few plain statements ending in a `return`, `break` or `continue`. Then
/// `if (!c) { TAIL } BODY` is the same control flow one level flatter; a
/// compare ladder nesting once per compare becomes a run of early
/// returns, and a message dispatch that handles one id in two lines and
/// nests the rest reads as a run of handlers. Bodies shorter than four
/// lines keep the natural form; a tail that jumps stays where the
/// label-following rule can still cancel the jump, and one that opens a
/// block or carries a label stays put.
///
/// # Arguments
///
/// * `lines` - The body lines, rewritten in place.
///
/// # Returns
///
/// Whether anything was rewritten.
pub(super) fn flatten_early_exits(lines: &mut Vec<String>) -> bool {
    /// Shortest body worth inverting.
    const EARLY_EXIT_MIN: usize = 4;
    /// Longest tail moved into the early arm.
    const EARLY_TAIL_MAX: usize = 3;
    let terminal = |t: &str| is_return(t) || is_goto(t) || t == "break;" || t == "continue;";
    let mut nest: Option<Nest> = None;
    let mut i = 0;
    while i < lines.len() {
        let Some((cond, ind)) = lines
            .get(i)
            .and_then(|l| Some((if_opener(l.trim())?.to_owned(), indent_of(l))))
        else {
            i += 1;
            continue;
        };
        let closer = nest.get_or_insert_with(|| Nest::of(lines));
        let close = closer.closer.get(i).copied().flatten().filter(|&j| {
            lines
                .get(j)
                .is_some_and(|l| l.trim() == "}" && indent_of(l) == ind)
        });
        let Some(close) = close else {
            i += 1;
            continue;
        };
        let body_ok = close > i + EARLY_EXIT_MIN
            && lines
                .get(i + 1..close)
                .and_then(|body| {
                    body.iter()
                        .rev()
                        .find(|l| !l.trim().is_empty() && indent_of(l) == ind + 2)
                })
                .is_some_and(|l| terminal(l.trim()));
        let tail: Option<Vec<String>> = {
            let mut tail = Vec::new();
            let mut ends = false;
            for l in lines.iter().skip(close + 1).take(EARLY_TAIL_MAX) {
                let t = l.trim();
                if indent_of(l) != ind
                    || t.is_empty()
                    || t.ends_with('{')
                    || t.ends_with(':')
                    || t.starts_with('}')
                    || is_goto(t)
                {
                    break;
                }
                tail.push(l.clone());
                if is_return(t) || t == "break;" || t == "continue;" {
                    ends = true;
                    break;
                }
            }
            ends.then_some(tail)
        };
        let (true, Some(tail)) = (body_ok, tail) else {
            i += 1;
            continue;
        };
        let pad = " ".repeat(ind);
        let moved = tail.len();
        let mut rewritten = vec![format!("{pad}if ({}) {{", invert_condition(&cond))];
        rewritten.extend(tail.into_iter().map(|l| format!("  {l}")));
        rewritten.push(format!("{pad}}}"));
        rewritten.extend(
            lines
                .get(i + 1..close)
                .unwrap_or(&[])
                .iter()
                .map(|l| l.strip_prefix("  ").unwrap_or(l).to_owned()),
        );
        lines.splice(i..=close + moved, rewritten);
        return true;
    }
    false
}

/// Runs the cleanup over a body on its own.
///
/// The same steps [`decompile`] applies after emission (the jumps folded
/// on the tree, [`super::cir::fold`], then the text passes: label
/// cancellation, folds, early exits, copied tails, dead text), exposed so
/// a rendering can be normalized or a cleanup rule pinned without a
/// binary. No call is known to end its path here.
///
/// # Arguments
///
/// * `body` - Pseudo-C lines as the emitter writes them.
///
/// # Returns
///
/// The cleaned text.
pub fn cleanup(body: &str) -> String {
    cleanup_text(&cir::fold(body, &[], Some(&BTreeSet::new())), None)
}

/// The passes behind [`cleanup`], run to a fixpoint or to the pass budget
/// ([`CLEANUP_PASSES`]).
///
/// The tree has folded the structurer's own jumps already
/// ([`super::cir::fold`]); these passes fold the ones the text
/// passes expose. Duplicate spills are chained; a statement both arms of an
/// `if`/`else` end with moves after it ([`hoist_common_tails`]); a pair of
/// jumps takes the order of the test before its label
/// ([`flip_jump_pairs`]); a conditional `goto` whose label ends a run whose
/// own labels only it enters becomes an `if` around that run
/// ([`fold_conditional_gotos`]); a long `if` body that never falls out,
/// followed by a terminal line, becomes an early exit with the body one
/// level flatter ([`flatten_early_exits`]); a short returning tail is
/// copied to the jumps that target it ([`inline_terminal_tails`]); labels
/// no goto references are dropped; and
/// text after an unconditional transfer or the closing brace of
/// a break-less `while (1)`, down to the next label at the same depth or a
/// dedent, is dropped when it holds no label at all (a block every path to
/// which was absorbed into a structure; a label anywhere inside means the
/// span is entered by a goto). That last pass walks from the end, so a
/// removal only moves lines already handled and the precomputed closer
/// indices stay valid. Once the passes settle, inverted and counted loops
/// read as the `while` and `for` they were ([`super::loops::recover_loops`]).
///
/// # Arguments
///
/// * `body` - Pseudo-C lines as the emitter writes them.
/// * `live_out` - The register the function hands a second result back
///   in, whose assignments its callers read ([`drop_dead_assignments`]).
///
/// # Returns
///
/// The cleaned body, newline-terminated.
pub(super) fn cleanup_text(body: &str, live_out: Option<&str>) -> String {
    cleanup_settled(body, live_out, Passes::NONE).0
}

/// [`cleanup_text`], with how its passes ended.
///
/// # Arguments
///
/// * `body` - Pseudo-C lines as the emitter writes them.
/// * `live_out` - The register a second result comes back in, if any.
/// * `skip` - The passes left out ([`Passes`]).
///
/// # Returns
///
/// The cleaned body, newline-terminated, and its [`Settle`].
pub(super) fn cleanup_settled(
    body: &str,
    live_out: Option<&str>,
    skip: Passes,
) -> (String, Settle) {
    let mut lines: Vec<String> = body.lines().map(str::to_owned).collect();
    let fuel = CLEANUP_PASSES.saturating_add(lines.len());
    let settle = cleanup_passes(&mut lines, fuel, live_out, skip);
    if skip.runs(Pass::RecoverLoops) {
        loops::recover_loops(&mut lines);
    }
    let mut text = lines.join("\n");
    text.push('\n');
    (text, settle)
}

/// Drops each `goto` (bare or `if (...) goto`) whose label follows it
/// across nothing that runs ([`falls_to_label`]).
///
/// # Arguments
///
/// * `lines` - The body lines, rewritten in place.
///
/// # Returns
///
/// Whether any jump went.
fn drop_fallthrough_gotos(lines: &mut Vec<String>) -> bool {
    let mut changed = false;
    let mut i = 0;
    while i + 1 < lines.len() {
        let t = lines[i].trim();
        let goto = t
            .strip_prefix("goto ")
            .or_else(|| t.rsplit_once(") goto ").map(|(_, g)| g))
            .and_then(|r| r.strip_suffix(';'));
        if let Some(g) = goto
            && falls_to_label(lines, i, g)
        {
            lines.remove(i);
            changed = true;
            continue;
        }
        i += 1;
    }
    changed
}

/// Folds the jumps the passes after [`cleanup_text`] leave foldable.
///
/// Typing and variable passes drop dead stores, which can leave an `if`
/// around a lone `goto` or two arms that now end alike. This reruns only
/// the folds that move no value: one-line jumps
/// ([`collapse_lone_gotos`]), shared arm tails ([`hoist_common_tails`]),
/// loop exits ([`loop_exits`]),
/// jumps to the next line ([`drop_fallthrough_gotos`]), labels nothing
/// names, `else` arms ([`absorb_else`]) and guarded runs
/// ([`fold_conditional_gotos`]), until one changes nothing or the pass
/// budget ([`CLEANUP_PASSES`]) is spent. Blank lines and the header stay.
///
/// # Arguments
///
/// * `text` - A polished function.
///
/// # Returns
///
/// The text with those jumps folded, newline-terminated.
pub(super) fn refold_jumps(text: &str) -> String {
    let mut lines: Vec<String> = text.lines().map(str::to_owned).collect();
    if !lines.iter().any(|l| l.contains("goto ")) {
        return text.to_owned();
    }
    for _ in 0..CLEANUP_PASSES {
        let mut changed = collapse_lone_gotos(&mut lines);
        changed |= hoist_common_tails(&mut lines);
        changed |= loop_exits(&mut lines);
        changed |= drop_fallthrough_gotos(&mut lines);
        let handlers = handler_labels(&lines);
        changed |= thread_label_gotos(&mut lines, &handlers);
        let mut referenced: BTreeSet<String> = goto_index(&lines).into_keys().collect();
        referenced.extend(handlers);
        let before = lines.len();
        lines.retain(|l| label_name(l).is_none_or(|name| referenced.contains(name)));
        changed |= lines.len() != before;
        changed |= drop_unreachable_runs(&mut lines);
        changed |= absorb_else(&mut lines);
        changed |= fold_conditional_gotos(&mut lines, RunLabels::Forbidden);
        if !changed {
            break;
        }
    }
    if lines
        .iter()
        .take(5)
        .any(|l| l.starts_with("// signature: void "))
        && let [ref earlier @ .., ref before, ref last] = lines[..]
        && last == "return;"
        && !before.trim_end().ends_with(':')
        && before.trim() != "return;"
        && earlier.last().is_none_or(|l| l.trim() != "return;")
    {
        lines.pop();
    }
    let mut out = lines.join("\n");
    out.push('\n');
    out
}

/// How one run of the cleanup passes ended.
///
/// The passes stop when one changes nothing or when the budget is spent
/// ([`CLEANUP_PASSES`]). A text that spends it is written as it stands; that
/// is a rule and its undoing trading the text back and forth, which costs a
/// pass per line and leaves jumps a settled run would fold, so a sweep
/// checks that no function spends it ([`Settle::spent`]).
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Settle {
    /// Passes run.
    pub passes: usize,
    /// Passes the text was allowed.
    pub fuel: usize,
    /// The passes that still changed the text in the last pass run; empty
    /// when the text settled.
    pub churn: Vec<&'static str>,
}

impl Settle {
    /// Tells whether the budget ran out before the text settled.
    #[must_use]
    pub fn spent(&self) -> bool {
        !self.churn.is_empty()
    }
}

/// Passes [`cleanup_passes`] may run beyond one per line of the text.
///
/// Every pass that runs another changed something, and once the folds
/// have settled each change is one block moved to its one jump or one
/// tail copied to its jumps, so a text of `n` lines settles within a few
/// passes plus `n`: kernel32's longest function takes nineteen, borer's
/// own binary eighty-five. The budget guarantees that no rule and its
/// undoing can trade the text back and forth forever; a text that spends
/// it is written as it stands, every remaining jump a `goto`.
pub(super) const CLEANUP_PASSES: usize = 64;

/// Runs the cleanup passes over `lines` until one changes nothing, or
/// `fuel` passes have run.
///
/// # Arguments
///
/// * `lines` - The body lines, rewritten in place.
/// * `fuel` - Most passes run.
/// * `live_out` - The register a second result comes back in, if any.
///
/// # Returns
///
/// How many passes ran, out of how many, and what still changed when the
/// budget ran out ([`Settle`]).
pub(super) fn cleanup_passes(
    lines: &mut Vec<String>,
    fuel: usize,
    live_out: Option<&str>,
    skip: Passes,
) -> Settle {
    let mut passes = 0;
    let mut round = Round {
        skip,
        idle: Passes::NONE,
        churn: Vec::new(),
    };
    while passes < fuel {
        passes += 1;
        round.churn.clear();
        let mut changed = round.run(Pass::MergeChains, lines, merge_chains);
        changed |= round.run(Pass::FoldTempCopies, lines, fold_temp_copies);
        changed |= round.run(
            Pass::MergeReturnAssignments,
            lines,
            merge_return_assignments,
        );
        changed |= round.run(Pass::UnnamedLabels, lines, |lines| {
            let handlers = handler_labels(lines);
            let threaded = thread_label_gotos(lines, &handlers);
            let mut referenced: BTreeSet<String> = goto_index(lines).into_keys().collect();
            referenced.extend(handlers);
            let before = lines.len();
            lines.retain(|l| match label_name(l) {
                Some(name) => referenced.contains(name),
                None => !l.trim().is_empty(),
            });
            threaded || lines.len() != before
        });
        changed |= round.run(Pass::FlattenElseIf, lines, flatten_else_if);
        changed |= round.run(Pass::HoistCommonTails, lines, hoist_common_tails);
        changed |= round.run(Pass::FlipJumpPairs, lines, |l| flip_jump_pairs(l));
        changed |= round.run(Pass::FlattenEarlyExits, lines, flatten_early_exits);
        changed |= round.run(Pass::AbsorbElse, lines, absorb_else);
        changed |= round.run(Pass::FoldUnorderedCompares, lines, |l| {
            fold_unordered_compares(l)
        });
        changed |= round.run(Pass::DropDeadAssignments, lines, |lines| {
            drop_dead_assignments(lines, live_out)
                .map(|kept| *lines = kept)
                .is_some()
        });
        changed |= round.run(Pass::StrlenLoops, lines, strlen_loops);
        if !changed {
            changed |= round.run(Pass::FoldContainedGotos, lines, |lines| {
                fold_conditional_gotos(lines, RunLabels::Contained)
            });
        }
        if !changed {
            changed |= round.run(Pass::InlineTerminalTails, lines, inline_terminal_tails);
        }
        if !changed {
            changed |= round.run(Pass::MoveSingleUseBlocks, lines, move_single_use_blocks);
        }
        changed |= round.run(Pass::UnreachableRuns, lines, drop_unreachable_runs);
        if !changed {
            round.churn.clear();
            break;
        }
    }
    let churn = round.churn;
    Settle {
        passes,
        fuel,
        churn,
    }
}

/// Lists the labels of the handler code a guarded region left unwrapped
/// runs: the entries its comment names (`catch (...) at 0x1000`), which
/// only the runtime enters, so no `goto` names them.
///
/// The structurer writes that code after the body under its label
/// ([`cir::wrap`]); without the label, the code would read as dead text
/// after a `return` and go.
///
/// # Arguments
///
/// * `lines` - The body lines.
///
/// # Returns
///
/// The labels, as `L_<addr>`.
pub(super) fn handler_labels(lines: &[String]) -> BTreeSet<String> {
    lines
        .iter()
        .filter_map(|l| l.trim_start().strip_prefix("// "))
        .filter(|c| {
            (c.starts_with("try ") || c.starts_with("__try ")) && c.contains(" not structured, ")
        })
        .flat_map(|c| c.split(" at 0x").skip(1))
        .map(|rest| {
            let hex: String = rest.chars().take_while(char::is_ascii_hexdigit).collect();
            format!("L_{hex}")
        })
        .collect()
}

/// Redirects `goto L_a;` to `L_b` when `L_a:` stands right before `goto L_b;`
/// at the same indentation.
///
/// # Arguments
///
/// * `lines` - The body lines, rewritten in place.
/// * `keep` - Handler labels that may not be redirected.
///
/// # Returns
///
/// Whether any `goto` was redirected.
fn thread_label_gotos(lines: &mut [String], keep: &BTreeSet<String>) -> bool {
    let mut map: BTreeMap<String, String> = BTreeMap::new();
    for w in lines.windows(2) {
        if let Some(a) = label_name(&w[0]).filter(|a| !keep.contains(*a))
            && indent_of(&w[0]) == indent_of(&w[1])
            && let Some(b) = w[1]
                .trim()
                .strip_prefix("goto ")
                .and_then(|r| r.strip_suffix(';'))
            && a != b
        {
            map.insert(a.to_owned(), b.to_owned());
        }
    }
    if map.is_empty() {
        return false;
    }
    let mut changed = false;
    for l in lines.iter_mut() {
        let t = l.trim();
        let pad = pad_of(l);
        if let Some(a) = t.strip_prefix("goto ").and_then(|r| r.strip_suffix(';'))
            && let Some(b) = map.get(a)
        {
            *l = format!("{pad}goto {b};");
            changed = true;
        } else if let Some((cond, a)) = conditional_goto(t)
            && let Some(b) = map.get(a)
        {
            *l = format!("{pad}if ({cond}) goto {b};");
            changed = true;
        }
    }
    changed
}

/// The state of one run of [`cleanup_passes`]: which passes it leaves
/// out, which would find nothing to change, and what changed this round.
#[derive(Debug)]
struct Round {
    /// The passes left out ([`Passes`]).
    skip: Passes,
    /// The passes that last ran on the text as it stands and changed
    /// nothing: a pass is a function of the lines alone, so running one
    /// again before another pass changes them would change nothing again.
    idle: Passes,
    /// The passes that changed the text this round.
    churn: Vec<&'static str>,
}

impl Round {
    /// Runs one pass unless it is left out or idle, and records what it did.
    ///
    /// # Arguments
    ///
    /// * `pass` - The pass.
    /// * `lines` - The body lines, rewritten in place.
    /// * `f` - The pass's rewrite, telling whether it changed the lines.
    ///
    /// # Returns
    ///
    /// Whether the pass changed the lines; `false` when it did not run.
    fn run(
        &mut self,
        pass: Pass,
        lines: &mut Vec<String>,
        f: impl FnOnce(&mut Vec<String>) -> bool,
    ) -> bool {
        if !self.skip.runs(pass) || !self.idle.runs(pass) {
            return false;
        }
        let did = f(lines);
        if did {
            self.idle = Passes::NONE;
        } else {
            self.idle = self.idle.without(pass);
        }
        note(&mut self.churn, pass.name(), did)
    }
}

/// Drops the text after an unconditional transfer or the closing brace of
/// a break-less `while (1)`, down to the next label at the same depth or a
/// dedent, when it holds no label at all.
///
/// It walks from the end, so a removal only moves lines already handled
/// and the closer indices found first stay valid.
///
/// # Arguments
///
/// * `lines` - The body lines, rewritten in place.
///
/// # Returns
///
/// Whether any run went.
fn drop_unreachable_runs(lines: &mut Vec<String>) -> bool {
    let endless = endless_loop_closers(lines);
    let mut changed = false;
    for k in (0..lines.len()).rev() {
        let ind = indent_of(&lines[k]);
        if !(transfers(&lines[k]) || endless.contains(&k)) {
            continue;
        }
        let mut end = k + 1;
        let mut has_label = false;
        while end < lines.len() {
            let label = is_label(&lines[end]);
            let li = indent_of(&lines[end]);
            if li < ind || (li == ind && label) {
                break;
            }
            has_label |= label;
            end += 1;
        }
        if !has_label && end > k + 1 {
            lines.drain(k + 1..end);
            changed = true;
        }
    }
    changed
}

/// Records a pass that changed the text.
///
/// # Arguments
///
/// * `churn` - The passes that changed it so far this round.
/// * `name` - The pass.
/// * `did` - Whether it changed anything.
///
/// # Returns
///
/// `did`, so the call stands where the bare result stood.
fn note(churn: &mut Vec<&'static str>, name: &'static str, did: bool) -> bool {
    if did {
        churn.push(name);
    }
    did
}

#[cfg(test)]
mod fuel_tests {
    use super::{Pass, Passes, Round, cleanup_passes, flatten_early_exits};

    /// An `if` whose body never falls out turns into an early exit across
    /// blank lines and nested blocks, and one whose block goes on into an
    /// `else` stays.
    ///
    /// # Panics
    ///
    /// When a block is flattened otherwise.
    #[test]
    fn an_if_that_never_falls_out_becomes_an_early_exit() {
        let text = [
            "if (a1 == 0) {",
            "  if (a2 == 0) {",
            "    x = 1;",
            "  }",
            "",
            "  y = 2;",
            "  return 1;",
            "}",
            "return 0;",
        ];
        let mut lines: Vec<String> = text.map(str::to_owned).into();
        assert!(flatten_early_exits(&mut lines));
        assert_eq!(
            lines,
            [
                "if (a1 != 0) {",
                "  return 0;",
                "}",
                "if (a2 == 0) {",
                "  x = 1;",
                "}",
                "",
                "y = 2;",
                "return 1;",
            ]
        );
        let mut kept: Vec<String> = [
            "if (a1 == 0) {",
            "  x = 1;",
            "  y = 2;",
            "  z = 3;",
            "  return 1;",
            "} else {",
            "  return 0;",
            "}",
        ]
        .map(str::to_owned)
        .into();
        assert!(!flatten_early_exits(&mut kept));
    }

    /// A pass that changed nothing is not run again until another pass
    /// changes the text, and one left out never runs.
    #[test]
    #[expect(
        clippy::missing_panics_doc,
        reason = "assertions are the point of a test"
    )]
    fn an_idle_pass_waits_for_a_change() {
        let mut round = Round {
            skip: Passes::NONE.without(Pass::AbsorbElse),
            idle: Passes::NONE,
            churn: Vec::new(),
        };
        let mut lines = vec![String::from("return 0;")];
        let runs = std::cell::Cell::new(0);
        let count = |did: bool| {
            let runs = &runs;
            move |_: &mut Vec<String>| {
                runs.set(runs.get() + 1);
                did
            }
        };
        assert!(!round.run(Pass::MergeChains, &mut lines, count(false)));
        assert!(!round.run(Pass::MergeChains, &mut lines, count(false)));
        assert_eq!(runs.get(), 1);
        assert!(round.run(Pass::FoldTempCopies, &mut lines, count(true)));
        assert!(!round.run(Pass::MergeChains, &mut lines, count(false)));
        assert_eq!(runs.get(), 3);
        assert!(!round.run(Pass::AbsorbElse, &mut lines, count(true)));
        assert_eq!(runs.get(), 3);
        assert_eq!(round.churn, ["fold_temp_copies"]);
    }

    /// The pass budget stops the rewriting where it stands.
    ///
    /// A text that settles only after several passes is written after one
    /// when one is the budget, with a jump it still had a `goto`, and the
    /// same text given exactly the passes it needs settles the same way as
    /// before.
    #[test]
    #[expect(
        clippy::missing_panics_doc,
        reason = "assertions are the point of a test"
    )]
    fn the_pass_budget_stops_the_rewriting_where_it_stands() {
        let body = [
            "if (a1 == 1) goto L_1;",
            "if (a1 == 2) goto L_2;",
            "if (a1 == 3) goto L_3;",
            "rax = sub_4(a1);",
            "goto L_4;",
            "L_1:",
            "rax = sub_1(a1);",
            "goto L_4;",
            "L_2:",
            "rax = sub_2(a1);",
            "goto L_4;",
            "L_3:",
            "rax = sub_3(a1);",
            "goto L_4;",
            "L_4:",
            "return rax;",
        ];
        let lines = || -> Vec<String> { body.iter().map(|l| (*l).to_owned()).collect() };
        let mut settled = lines();
        let passes = cleanup_passes(&mut settled, usize::MAX, None, Passes::NONE).passes;
        assert!(passes >= 3, "{passes} passes: {settled:?}");
        let mut again = lines();
        assert_eq!(
            cleanup_passes(&mut again, passes, None, Passes::NONE).passes,
            passes
        );
        assert_eq!(again, settled);
        let mut one = lines();
        let spent = cleanup_passes(&mut one, 1, None, Passes::NONE);
        assert_eq!(spent.passes, 1);
        assert!(spent.spent(), "{spent:?}");
        assert_ne!(one, settled);
        assert!(one.iter().any(|l| l.contains("goto ")), "{one:?}");
    }
}

#[cfg(test)]
mod dead_tests {
    use super::cleanup_text;

    /// A chain of copies loses only the targets nothing reads.
    ///
    /// `mov rbx,rcx; mov rdi,rcx` at the entry merge with the dead `rcx =
    /// a1;` into one chain, `rcx = rbx = rdi = a1;`: the copy into `rcx` is
    /// dead, and dropping the whole line dropped the copies the loop and the
    /// return read, so `return rdi;` returned a value nothing set.
    #[test]
    #[expect(
        clippy::missing_panics_doc,
        reason = "assertions are the point of a test"
    )]
    fn a_chain_keeps_the_copies_something_reads() {
        let body = concat!(
            "rax = *(uint8_t*)a1;\n",
            "rcx = a1;\n",
            "rbx = a1;\n",
            "rdi = a1;\n",
            "while (rax != 0) {\n",
            "  rax = sub_1(rbx);\n",
            "  rbx = rax;\n",
            "}\n",
            "return rdi;\n",
        );
        let text = cleanup_text(body, None);
        assert!(text.contains("rbx = rdi = a1;"), "{text}");
        assert!(!text.contains("rcx"), "{text}");
    }
}

#[cfg(test)]
mod refold_tests {
    use super::refold_jumps;

    /// Arms a later pass left ending in the same jump, one braced and one
    /// not, fold into one guard, and the header and blank line stay.
    #[test]
    #[expect(
        clippy::missing_panics_doc,
        reason = "assertions are the point of a test"
    )]
    fn arms_left_alike_fold_after_polish() {
        let lines = [
            "// signature: uint64_t f(uint64_t a1, uint64_t a2)",
            "uint64_t var1;",
            "",
            "if (a1 != 0) {",
            "  sub_1(a1);",
            "  if (a2 == 0) goto L_1;",
            "} else {",
            "  sub_2(a1);",
            "  if (a2 == 0) {",
            "    goto L_1;",
            "  }",
            "}",
            "sub_3(a1);",
            "L_1:",
            "return 0;",
            "",
        ];
        let out = refold_jumps(&lines.join("\n"));
        assert!(!out.contains("goto"), "{out}");
        assert!(out.contains("if (a2 != 0) {"), "{out}");
        assert!(
            out.starts_with(
                "// signature: uint64_t f(uint64_t a1, uint64_t a2)\nuint64_t var1;\n\n"
            ),
            "{out}"
        );
    }

    /// A label standing right before a `goto` threads its callers onto the
    /// target label, and a trailing `return;` or empty `default` in a `void`
    /// body is dropped.
    #[test]
    #[expect(
        clippy::missing_panics_doc,
        reason = "assertions are the point of a test"
    )]
    fn a_chained_label_threads_and_void_tail_return_drops() {
        let lines = [
            "if (a1 == 0) {",
            "  if (a2 == 0) {",
            "    sub_1(\"goto L_1;\");",
            "    goto L_1;",
            "  }",
            "  L_1:",
            "  goto L_2;",
            "}",
            "sub_2();",
            "L_2:",
            "return;",
        ];
        let out =
            super::drop_dead_results(&super::cleanup_text(&lines.join("\n"), Some("void")), "rax");
        assert!(out.contains("\"goto L_1;\""), "{out}");
        assert!(!out.contains("L_1:"), "{out}");
        assert!(!out.trim_end().ends_with("return;"), "{out}");
    }
}
