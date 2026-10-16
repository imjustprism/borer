//! Emission: blocks, loops, whiles and switches written as pseudo-C.

use super::*;

/// Emits block `i` and any structured region it heads.
///
/// A block on a cycle entered elsewhere is handed to that entry first, since
/// the loop reads better whole; when the entry's structuring stops short of
/// this block the text is written here after it, because the caller takes
/// the block as written either way and a label nobody wrote is a goto that
/// lands nowhere.
///
/// A call whose result only the block's branch reads is written inside the
/// condition rather than on a line before it ([`call_in_cond`]); a block
/// ending in such a call takes the test it falls into as its own branch
/// ([`call_then_test`]).
///
/// In order: a natural loop headed here ([`try_loop`]); the block's label and
/// lines; a jump-table dispatch as a `switch` ([`try_switch`]) or, when that
/// fails, a switch of gotos; an unconditional jump, which a shared pure
/// return tail reaches from other sites too, whose statements are cloned in
/// place of the `goto` ([`return_tail`]) so the site reads as the `return`
/// it jumps to; a block that simply
/// continues (`goto` to its successor, which the cleanup drops when the text
/// continues there anyway); a condition folded to a constant (a plain
/// `goto`); a branch whose two sides meet at once (the condition decides
/// nothing); a `while`/`for` ([`try_while`]), where statements in the header
/// run before every test of the condition, so they are written again after
/// the body, or the loop becomes `while (1) { header; if (!cond) break; ...}`
/// when the body contains a `continue` that would skip that copy; a loop
/// whose body ends testing whether to go round again (`if (c) break;`, or
/// `if (c) continue;` and then leaving) and continues nowhere else at its
/// own level is `do { ... } while (c);` ([`latch_of`]); an `if`
/// (target side), an inverted `if` (fall-through side), an `if/else` (in
/// the last attempt, arms leaving through several exits still structure
/// when exactly one exit is common to both: it is the continuation and the
/// others stay jumps inside the arms, as in a compare ladder whose last
/// test skips the shared tail to a block an outer guard reaches too; a
/// shared tail both arms copied is dropped only when every predecessor lies
/// inside the arms and neither arm's text still jumps to it); and
/// finally the explicit branch, inverted when the jump target is the next
/// block the text will emit so the text falls through into it. After a
/// structure the text jumps to the join explicitly. `for` sugar applies when
/// `v = init;` sits within the four lines before, the body ends with
/// `v += 1;`, and the condition's left side is exactly `v`.
///
/// # Arguments
///
/// * `ctx` - Per-function state.
/// * `st` - Emission state.
/// * `i` - Block index.
/// * `out` - Receives the text.
/// * `depth` - Structuring nesting depth.
///
/// # Returns
///
/// The next block index to consider (the join of a structure, else `i + 1`).
pub(super) fn emit_block<L: Lifter>(
    ctx: &mut Ctx<'_>,
    st: &mut Emit<'_, L>,
    i: usize,
    out: &mut String,
    depth: usize,
) -> usize {
    let n = st.blocks.len();
    if i >= n || st.emitted[i] {
        return i + 1;
    }
    let mut cyc: Option<(BTreeSet<usize>, usize)> = None;
    if depth < MAX_DEPTH && !st.loops.contains(&i) {
        let found = cycle_of(st, i);
        let recursed = if let Some((body, entry)) = &found
            && *entry != i
            && body.first() == Some(&i)
            && !st.emitted[*entry]
        {
            let next = emit_block(ctx, st, *entry, out, depth);
            if st.emitted[i] {
                return next;
            }
            true
        } else {
            false
        };
        if !recursed {
            cyc = found;
        }
    }
    if let Some(next) = try_loop(ctx, st, i, out, depth, cyc) {
        return next;
    }
    let mut block_out = run_block(ctx, st, i);
    let _ = writeln!(out, "{}", label(st.blocks[i].start));
    let lines_at = out.len();
    for l in &block_out.lines {
        out.push_str(l);
        out.push('\n');
    }
    st.emitted[i] = true;
    let names = ctx.names();

    if st.blocks[i].term == BlockTerm::Indirect {
        if let Some(idx_expr) = &block_out.switch_idx {
            if let Some(t) = block_out
                .switch_target
                .as_ref()
                .and_then(|t| fold_static(ctx.program, t, FOLD_DEPTH))
                .filter(|t| st.index_of(*t).is_some())
                .or_else(|| {
                    const_index(idx_expr).and_then(|k| table_target(ctx.analysis, &st.blocks[i], k))
                })
            {
                let _ = writeln!(out, "{}", jump_to(st, t));
                return i + 1;
            }
            if let Some(next) = try_switch(ctx, st, i, idx_expr, out, depth) {
                return next;
            }
            goto_switch(ctx, st, i, idx_expr, out);
        }
        return i + 1;
    }
    if let Some(t) = block_out.goto {
        if let Some(tail) = return_tail(ctx, st, t) {
            let _ = writeln!(out, "{tail}");
        } else {
            let _ = writeln!(out, "{}", jump_to(st, t));
        }
        return i + 1;
    }
    let mut call = block_out
        .branch
        .as_ref()
        .and_then(|br| call_in_cond(ctx, st, i, &block_out, &br.cond));
    let tested = match &block_out.branch {
        Some(_) => None,
        None => call_then_test(ctx, st, i, &block_out),
    };
    if let Some((s, br, in_cond)) = tested {
        consume(st, i, s, &mut Journal::default());
        call = Some(in_cond);
        block_out.branch = Some(br);
    }
    let Some(br) = block_out.branch else {
        if matches!(st.blocks[i].term, BlockTerm::Fall | BlockTerm::Call)
            && let Some(&s) = st.succs[i].first()
        {
            let _ = writeln!(out, "{}", goto(st.start(s)));
        } else if let Some(t) = falls_outside(ctx, st, i) {
            let _ = writeln!(out, "{}", jump_to(st, t));
        }
        return i + 1;
    };
    if let Some(taken) = br.cond.eval() {
        let dest = if taken { br.target } else { br.fall };
        let _ = writeln!(out, "{}", jump_to(st, dest));
        return i + 1;
    }
    let (Some(t), Some(f)) = (st.index_of(br.target), st.index_of(br.fall)) else {
        let _ = writeln!(
            out,
            "if ({}) {}",
            br.cond.render(&names, false),
            jump_to(st, br.target)
        );
        let _ = writeln!(out, "{}", jump_to(st, br.fall));
        return i + 1;
    };
    if let Some(next) = ladder::try_ladder(ctx, st, i, &br.cond, t, f, out, depth) {
        return next;
    }
    let kept = call
        .as_ref()
        .map_or(block_out.lines.len(), |(kept, _)| *kept);
    let header_lines = block_out.lines.get(..kept).unwrap_or(&[]);
    if kept < block_out.lines.len() {
        out.truncate(lines_at);
        for l in header_lines {
            out.push_str(l);
            out.push('\n');
        }
    }
    let mut journal = Journal::default();
    let t = follow_trampoline(ctx, st, i, t, &mut journal);
    let f = follow_trampoline(ctx, st, i, f, &mut journal);
    let (guard, t, f) = merge_guard(ctx, st, i, (br.cond, call.map(|(_, c)| c)), t, f);
    let t = follow_trampoline(ctx, st, i, t, &mut journal);
    let f = follow_trampoline(ctx, st, i, f, &mut journal);
    if t == f {
        if guard.calls() {
            let _ = writeln!(
                out,
                "if ({}) {{
}}",
                guard.render(&names, Side::Target)
            );
        }
        let _ = writeln!(out, "{}", goto(st.start(t)));
        return i + 1;
    }

    let inside = !st.outside(t) && !st.outside(f);
    let headers: BTreeSet<usize> = [i].into_iter().collect();
    let bases = (depth < MAX_DEPTH && inside).then(|| {
        (
            base_of(st, t, &headers, Some(f)),
            base_of(st, f, &headers, Some(t)),
        )
    });

    if let Some((base_t, base_f)) = &bases
        && let Some((body, exit, body_side)) = try_while_with(st, i, t, f, Some((base_t, base_f)))
    {
        let cond = guard.render(&names, body_side);
        let mut buf = String::new();
        emit_run(
            ctx,
            st,
            &body,
            Some(st.blocks[i].start),
            Some(st.start(exit)),
            &mut buf,
            depth + 1,
        );
        if !header_lines.is_empty() && buf.contains("continue;") {
            out.truncate(lines_at);
            let _ = writeln!(out, "while (1) {{");
            for l in header_lines {
                let _ = writeln!(out, "  {l}");
            }
            let _ = writeln!(
                out,
                "  if ({}) break;",
                guard.render(&names, body_side.other())
            );
            out.push_str(&indent(&buf));
            out.push_str("}\n");
            let _ = writeln!(out, "{}", goto(st.start(exit)));
            return exit;
        }
        for l in header_lines {
            buf.push_str(l);
            buf.push('\n');
        }
        let var = match &guard {
            Guard::One(c, None) => match &c.flags {
                Flags::Cmp(Expr::Var(v), _, _) => Some(names.key(*v)),
                _ => None,
            },
            Guard::One(_, Some(_)) | Guard::Or(..) | Guard::And(..) => None,
        };
        let mut for_sugar = false;
        if let Some(v) = var
            && header_lines.is_empty()
        {
            let inc = format!("{v} += 1;");
            let init_of = format!("{v} = ");
            let body_wo_nl = buf.trim_end_matches('\n');
            let body_last = body_wo_nl.rfind('\n').map_or(0, |at| at + 1);
            let body_has_inc = body_wo_nl[body_last..] == inc;
            let bytes = out.as_bytes();
            let mut line_end = bytes.len();
            if line_end > 0 && bytes[line_end - 1] == b'\n' {
                line_end -= 1;
            }
            let mut splice: Option<(usize, usize, String)> = None;
            for _ in 0..4 {
                if line_end == 0 {
                    break;
                }
                let start = bytes[..line_end]
                    .iter()
                    .rposition(|&b| b == b'\n')
                    .map_or(0, |at| at + 1);
                if let Some(val) = out[start..line_end]
                    .strip_prefix(&init_of)
                    .and_then(|r| r.strip_suffix(';'))
                {
                    splice = Some((start, line_end, val.to_owned()));
                    break;
                }
                if start == 0 {
                    break;
                }
                line_end = start - 1;
            }
            if body_has_inc && let Some((start, end, init)) = splice {
                out.replace_range(start..end + 1, "");
                let body_wo_inc = &buf[..body_wo_nl.len()];
                let _ = writeln!(out, "for ({v} = {init}; {cond}; {v} += 1) {{");
                for l in body_wo_inc.lines() {
                    if !l.is_empty() {
                        out.push_str("  ");
                    }
                    out.push_str(l);
                    out.push('\n');
                }
                out.push_str("}\n");
                for_sugar = true;
            }
        }
        if !for_sugar {
            let _ = writeln!(out, "while ({cond}) {{");
            out.push_str(&indent(&buf));
            out.push_str("}\n");
        }
        let _ = writeln!(out, "{}", goto(st.start(exit)));
        return exit;
    }

    if let Some((base_t, base_f)) = &bases
        && t != f
    {
        for (copy_calls, copy_stop) in [(false, false), (false, true), (true, true)] {
            st.copy_calls = copy_calls;
            st.copy_stop = copy_stop;
            let saved_no_dup = st.no_dup.clone();
            let (then, els) = loop {
                let then = closed_run_with(st, t, &headers, Some(f), Some(base_t));
                let els = closed_run_with(st, f, &headers, Some(t), Some(base_f));
                let owned: BTreeSet<usize> = then
                    .order
                    .iter()
                    .chain(els.order.iter())
                    .copied()
                    .chain([i])
                    .collect();
                let contained = |dups: &BTreeSet<usize>, d: usize| {
                    dups.contains(&d) && st.succs[d].iter().all(|s| dups.contains(s))
                };
                let borrowed: Vec<usize> = then
                    .dups
                    .iter()
                    .chain(els.dups.iter())
                    .copied()
                    .filter(|&d| !st.succs[d].is_empty())
                    .filter(|&d| !contained(&then.dups, d) && !contained(&els.dups, d))
                    .filter(|&d| !st.dup_stack.iter().any(|owner| owner.contains(&d)))
                    .filter(|&d| st.preds[d].iter().any(|p| !owned.contains(p)))
                    .collect();
                if borrowed.is_empty() {
                    break (then, els);
                }
                st.no_dup.extend(borrowed);
            };
            st.no_dup = saved_no_dup;
            st.copy_calls = false;
            st.copy_stop = false;
            let owns = |r: &Region, b: usize| r.order.contains(&b) && !r.dups.contains(&b);
            let leaves = |e: usize| st.outside(e) || st.loops.contains(&e);
            let then_ok = then.closed
                && then.exits.iter().all(|e| *e == f || leaves(*e))
                && !owns(&then, f)
                && !then.order.contains(&i)
                && (!st.emitted[t] || then.dups.contains(&t));
            let els_ok = els.closed
                && !owns(&els, t)
                && !els.order.contains(&i)
                && els.exits.iter().all(|e| *e == t || leaves(*e))
                && (!st.emitted[f] || els.dups.contains(&f))
                && !st.emitted[t];
            let then_is_copy = then.dups.contains(&t);
            let els_is_copy = els.dups.contains(&f);
            let then_first = then_ok && !(then_is_copy && els_ok && !els_is_copy);
            if then_first {
                let mut buf = String::new();
                emit_run(ctx, st, &then, st.start_of(f), None, &mut buf, depth + 1);
                push_if(
                    out,
                    &guard.render(&names, Side::Target),
                    &buf,
                    guard.calls(),
                );
                let _ = writeln!(out, "{}", goto(st.start(f)));
                return f;
            }
            if els_ok {
                let mut buf = String::new();
                emit_run(ctx, st, &els, st.start_of(t), None, &mut buf, depth + 1);
                push_if(out, &guard.render(&names, Side::Fall), &buf, guard.calls());
                let _ = writeln!(out, "{}", goto(st.start(t)));
                return t;
            }
            if then_ok {
                let mut buf = String::new();
                emit_run(ctx, st, &then, st.start_of(f), None, &mut buf, depth + 1);
                push_if(
                    out,
                    &guard.render(&names, Side::Target),
                    &buf,
                    guard.calls(),
                );
                let _ = writeln!(out, "{}", goto(st.start(f)));
                return f;
            }
            let exits_all: BTreeSet<usize> = then.exits.union(&els.exits).copied().collect();
            let joins: BTreeSet<usize> =
                exits_all.iter().copied().filter(|e| !leaves(*e)).collect();
            let common: BTreeSet<usize> = then.exits.intersection(&els.exits).copied().collect();
            let escapes = copy_calls && copy_stop && joins.len() > 1 && common.len() == 1;
            if then.closed
                && els.closed
                && (joins.len() <= 1 || escapes)
                && !owns(&then, f)
                && !owns(&els, t)
                && !then.order.contains(&i)
                && !els.order.contains(&i)
                && !exits_all.contains(&t)
                && !exits_all.contains(&f)
                && (!st.emitted[t] || then_is_copy)
                && (!st.emitted[f] || els_is_copy)
            {
                let join = if escapes { &common } else { &joins }
                    .iter()
                    .next()
                    .copied()
                    .unwrap_or(i + 1);
                let mut then_buf = String::new();
                emit_run(
                    ctx,
                    st,
                    &then,
                    st.start_of(join),
                    None,
                    &mut then_buf,
                    depth + 1,
                );
                let mut else_buf = String::new();
                emit_run(
                    ctx,
                    st,
                    &els,
                    st.start_of(join),
                    None,
                    &mut else_buf,
                    depth + 1,
                );
                for d in then.dups.intersection(&els.dups) {
                    let all_inside = st.preds[*d].iter().all(|p| {
                        (then.order.contains(p) || els.order.contains(p))
                            && (!(then.dups.contains(p) || els.dups.contains(p)) || st.emitted[*p])
                    });
                    let jump = goto(st.blocks[*d].start);
                    let still_jumped = then_buf.contains(&jump) || else_buf.contains(&jump);
                    if all_inside && !still_jumped {
                        st.emitted[*d] = true;
                    }
                }
                if is_dead_body(&else_buf) {
                    push_if(
                        out,
                        &guard.render(&names, Side::Target),
                        &then_buf,
                        guard.calls(),
                    );
                } else if is_dead_body(&then_buf) {
                    push_if(
                        out,
                        &guard.render(&names, Side::Fall),
                        &else_buf,
                        guard.calls(),
                    );
                } else {
                    let _ = writeln!(out, "if ({}) {{", guard.render(&names, Side::Target));
                    out.push_str(&indent(&then_buf));
                    out.push_str("} else {\n");
                    out.push_str(&indent(&else_buf));
                    out.push_str("}\n");
                }
                if !joins.is_empty() || (escapes && !common.is_empty()) {
                    let _ = writeln!(out, "{}", goto(st.start(join)));
                }
                return join;
            }
        }
    }

    let copied_next = |st: &Emit<'_, L>, b: usize| {
        st.dup_stack.last().is_some_and(|d| d.contains(&b))
            && st
                .orders
                .last()
                .is_some_and(|(order, pos)| order.get(pos + 1) == Some(&b))
    };
    for (arm, other, side) in [(t, f, Side::Target), (f, t, Side::Fall)] {
        if copied_next(st, arm) && !copied_next(st, other) {
            let body = copy_chain(ctx, st, arm);
            if body.lines().any(|l| !is_goto(l.trim_start())) {
                push_if(out, &guard.render(&names, side), &body, guard.calls());
                let _ = writeln!(out, "{}", goto(st.start(other)));
                return i + 1;
            }
        }
    }

    let next = st.next_block(i);
    if next == Some(t) && next != Some(f) {
        let _ = writeln!(
            out,
            "if ({}) {}",
            guard.render(&names, Side::Fall),
            goto(st.start(f))
        );
        let _ = writeln!(out, "{}", goto(st.start(t)));
        return i + 1;
    }
    let _ = writeln!(
        out,
        "if ({}) {}",
        guard.render(&names, Side::Target),
        goto(st.start(t))
    );
    let _ = writeln!(out, "{}", goto(st.start(f)));
    i + 1
}

/// Tells whether a copy of block `b` goes on to its one successor with no
/// jump of its own.
///
/// It falls through or returns from a call, or it ends in a branch the
/// lifter proved goes one way only: the copy's lines hold no branch, so
/// unless the text says where it goes, it runs into whatever is written
/// after it (the other side of an `if`, a `return` of someone else's).
///
/// # Arguments
///
/// * `st` - Emission state.
/// * `b` - The copied block.
pub(super) fn runs_on<L: Lifter>(st: &Emit<'_, L>, b: usize) -> bool {
    match st.blocks[b].term {
        BlockTerm::Fall | BlockTerm::Call => true,
        BlockTerm::Cond | BlockTerm::Indirect => st.succs[b].len() == 1,
        BlockTerm::Ret | BlockTerm::Jmp | BlockTerm::Invalid => false,
    }
}

/// Where a block that runs on past its end leaves the function: the address
/// after a block that falls through, or after a call the analysis saw return,
/// when no block of the function starts there.
///
/// Text that ends such a block with nothing reads as falling into whatever
/// the text writes next, a `return` at the end of the body; the jump out,
/// `goto *<va>;`, is what the binary does. A call that never returns
/// ([`crate::analysis::functions::call_ends_path`]) ends its path where it
/// stands, as the structure check reads it: the `goto` after
/// `_CxxThrowException` or a Rust panic would send a reader into padding.
///
/// # Arguments
///
/// * `ctx` - Per-function state: the program and its functions.
/// * `st` - Emission state.
/// * `b` - The block.
///
/// # Returns
///
/// The address, or `None` for a block with a successor in the function, a
/// call that never returns, or any other end.
pub(super) fn falls_outside<L: Lifter>(ctx: &Ctx<'_>, st: &Emit<'_, L>, b: usize) -> Option<u64> {
    if !st.succs.get(b).is_some_and(Vec::is_empty) {
        return None;
    }
    let block = st.blocks.get(b)?;
    match block.term {
        BlockTerm::Fall => Some(block.end),
        BlockTerm::Call
            if crate::analysis::functions::call_ends_path(ctx.program, ctx.analysis, block) =>
        {
            None
        }
        BlockTerm::Call => block.successors.first().copied(),
        BlockTerm::Ret
        | BlockTerm::Jmp
        | BlockTerm::Cond
        | BlockTerm::Indirect
        | BlockTerm::Invalid => None,
    }
    .filter(|t| st.index_of(*t).is_none())
}

/// The text of a copied tail: `start` and the one-way blocks after it that
/// the innermost region copies too, ending with the transfer out of the
/// last.
///
/// # Arguments
///
/// * `ctx` - Per-function state.
/// * `st` - Emission state.
/// * `start` - The copied block the branch enters.
pub(super) fn copy_chain<L: Lifter>(ctx: &mut Ctx<'_>, st: &Emit<'_, L>, start: usize) -> String {
    let mut lines: Vec<String> = Vec::new();
    let mut cur = start;
    let mut seen: BTreeSet<usize> = BTreeSet::new();
    while seen.insert(cur) {
        let copy = run_block(ctx, st, cur);
        lines.extend(copy.lines.iter().cloned());
        let next = copy
            .goto
            .map(|t| st.index_of(t).map_or(t, |n| st.start(n)))
            .or_else(|| {
                runs_on(st, cur)
                    .then(|| st.succs[cur].first().map(|&s| st.start(s)))
                    .flatten()
            });
        let Some(va) = next else {
            if let Some(t) = falls_outside(ctx, st, cur) {
                lines.push(jump_to(st, t));
            }
            break;
        };
        match st.index_of(va) {
            Some(n) if st.dup_stack.last().is_some_and(|d| d.contains(&n)) => cur = n,
            _ => {
                lines.push(goto(va));
                break;
            }
        }
    }
    lines.join(
        "
",
    ) + "
"
}

/// Emits the natural loop headed by `i` as `while (1) { ... }`.
///
/// A block with a back edge whose shape the while-detector cannot express.
/// Gotos to the header become `continue`, gotos to the loop's continuation
/// `break`. Blocks inside the loop's address range that are not part of the
/// loop are allowed only when they dead-end inside it or jump out
/// explicitly; a fall-through past the range would be silently rerouted to
/// the loop top, so it disqualifies the loop. Such a block entered from
/// outside the range (a return the function's head jumps to, a switch arm
/// interleaved with the loop) is not the loop's to emit: it is skipped,
/// left to whoever owns it, and the loop's blocks treat it as one beyond
/// the range. A block nothing reaches (the other side of a branch that
/// folded to a constant) is no text at all and vetoes nothing, and a header
/// whose branch leads into one is a jump, not the `while` test it would
/// otherwise be left to. Exit blocks
/// entered only from
/// the loop whose own region leaves through the one block every exit
/// reaches (the loop's continuation) are written inline in front of their
/// `break`: pass 1 finds that continuation (a shared exit block an exit
/// region would only copy is itself the continuation), pass 2 recomputes the
/// regions stopping at it
/// so it is written once, after the loop. With no single continuation only
/// the natural fall-through block breaks, but an exit region that leaves
/// nowhere (it returns) is still written inline, copying a tail that calls
/// before it returns when that is the only way the region leaves nowhere.
/// The header's label is the loop's entry and goes in front of the loop. A
/// body that ends by testing whether to go round again is a `do`/`while`
/// instead ([`latch_of`]).
///
/// # Arguments
///
/// * `ctx` - Per-function state.
/// * `st` - Emission state.
/// * `i` - The candidate header.
/// * `out` - Receives the text.
/// * `depth` - Structuring nesting depth.
///
/// # Returns
///
/// The loop's continuation block (else the block after its range), or
/// `None` when `i` heads no loop the emitter can express.
pub(super) fn try_loop<L: Lifter>(
    ctx: &mut Ctx<'_>,
    st: &mut Emit<'_, L>,
    i: usize,
    out: &mut String,
    depth: usize,
    cyc: Option<(BTreeSet<usize>, usize)>,
) -> Option<usize> {
    if depth >= MAX_DEPTH || st.loops.contains(&i) {
        return None;
    }
    let (body, entry) = cyc.or_else(|| cycle_of(st, i))?;
    if entry != i {
        return None;
    }
    if st.blocks[i].term == BlockTerm::Cond {
        let (t, f) = (
            st.blocks[i]
                .successors
                .first()
                .and_then(|s| st.index_of(*s)),
            st.blocks[i].successors.get(1).and_then(|s| st.index_of(*s)),
        );
        if let (Some(t), Some(f)) = (t, f)
            && !st.dead[t]
            && !st.dead[f]
            && try_while(st, i, t, f).is_some()
        {
            return None;
        }
    }
    let min = *body.first()?;
    let max = *body.last()?;
    let mut skipped: BTreeSet<usize> = BTreeSet::new();
    loop {
        let more: Vec<usize> = (min..=max)
            .filter(|b| !body.contains(b) && !skipped.contains(b))
            .filter(|&b| {
                st.preds[b]
                    .iter()
                    .any(|&p| p < min || p > max || skipped.contains(&p))
            })
            .collect();
        if more.is_empty() {
            break;
        }
        skipped.extend(more);
    }
    for b in min..=max {
        if body.contains(&b) || skipped.contains(&b) || st.dead[b] {
            continue;
        }
        let falls_out = matches!(st.blocks[b].term, BlockTerm::Fall | BlockTerm::Call)
            && st.succs[b].iter().any(|&s| s > max);
        if st.emitted[b] || falls_out || st.succs[b].iter().any(|&s| s < min) {
            return None;
        }
    }
    let saved_bound = st.bound;
    let saved_skipped = st.skipped.clone();
    st.bound = max + 1;
    st.skipped.extend(skipped.iter().copied());
    st.loops.push(i);
    let order: Vec<usize> = (i..=max)
        .chain(min..i)
        .filter(|b| !skipped.contains(b))
        .collect();
    st.orders.push((order.clone(), 0));
    let mut buf = String::new();
    for (pos, b) in order.iter().copied().enumerate() {
        st.set_pos(pos);
        if !st.emitted[b] {
            emit_block(ctx, st, b, &mut buf, depth + 1);
        }
    }
    st.orders.pop();
    st.loops.pop();
    st.bound = saved_bound;
    st.skipped = saved_skipped;
    let header_goto = goto(st.blocks[i].start);
    let range: BTreeSet<usize> = (min..=max).filter(|b| !skipped.contains(b)).collect();
    let exits: BTreeSet<usize> = range
        .iter()
        .flat_map(|b| st.succs[*b].iter().copied())
        .filter(|s| !range.contains(s))
        .collect();
    let absorbable = |st: &Emit<'_, L>, x: usize, stop: Option<usize>| -> Option<Region> {
        (!st.emitted[x])
            .then(|| closed_run_from(st, x, &range, stop))
            .filter(|r| r.closed && r.order.len() <= ABSORB_MAX_BLOCKS)
    };
    let mut joins: BTreeSet<usize> = BTreeSet::new();
    for &x in &exits {
        match absorbable(st, x, None) {
            Some(r) if !r.dups.contains(&x) => {
                joins.extend(r.exits.iter().copied());
                joins.extend(r.dups.iter().copied());
            }
            _ => {
                joins.insert(x);
            }
        }
    }
    let join = match joins.len() {
        0 => None,
        1 => joins.iter().next().copied(),
        _ => exits.contains(&(max + 1)).then_some(max + 1),
    };
    let mut absorbed: BTreeMap<usize, Region> = BTreeMap::new();
    for &x in &exits {
        if Some(x) == join {
            continue;
        }
        let fits = |r: &Region| {
            (joins.len() <= 1 || r.exits.is_empty()) && (!r.dups.contains(&x) || r.exits.is_empty())
        };
        let region = absorbable(st, x, join).filter(fits).or_else(|| {
            st.copy_calls = true;
            let again = absorbable(st, x, join).filter(|r| r.exits.is_empty());
            st.copy_calls = false;
            again
        });
        if let Some(r) = region {
            absorbed.insert(x, r);
        }
    }
    let join_va = join.map(|j| st.start(j));
    let mut inline: BTreeMap<usize, Vec<String>> = BTreeMap::new();
    let mut lines: Vec<String> = Vec::new();
    let mut has_break = false;
    let mut open: Vec<Scope> = Vec::new();
    let mut open_continue: Vec<Scope> = Vec::new();
    for l in buf.lines() {
        let level = at_loop_level(l, &mut open);
        let at_continue = at_continue_level(l, &mut open_continue);
        if at_continue && let Some(pos) = l.find(&header_goto) {
            lines.push(format!("{}continue;", &l[..pos]));
            continue;
        }
        if !level {
            lines.push(l.to_owned());
            continue;
        }
        let target = goto_address(l).and_then(|va| st.index_of(va));
        let goto_at = l.rfind("goto ").unwrap_or(l.len());
        match target {
            Some(x) if Some(x) == join => {
                has_break = true;
                lines.push(format!("{}break;", &l[..goto_at]));
            }
            Some(x) if absorbed.contains_key(&x) => {
                if !inline.contains_key(&x)
                    && let Some(region) = absorbed.get(&x)
                {
                    let mut text = String::new();
                    emit_run(ctx, st, region, join_va, join_va, &mut text, depth + 1);
                    let mut body_lines: Vec<String> = text.lines().map(str::to_owned).collect();
                    let reaches_join = join.is_some_and(|j| region.exits.contains(&j));
                    if reaches_join && !body_lines.last().is_some_and(|t| transfers(t)) {
                        body_lines.push("break;".to_owned());
                    }
                    inline.insert(x, body_lines);
                }
                let Some(body_lines) = inline.get(&x) else {
                    continue;
                };
                has_break |= body_lines.iter().any(|l| breaks(l.trim()));
                let prefix = &l[..goto_at];
                if prefix.trim().is_empty() {
                    lines.extend(body_lines.iter().map(|t| format!("{prefix}{t}")));
                } else {
                    lines.push(format!("{prefix}{{"));
                    let ind = pad_of(l);
                    lines.extend(body_lines.iter().map(|t| format!("{ind}  {t}")));
                    lines.push(format!("{ind}}}"));
                }
            }
            _ => lines.push(l.to_owned()),
        }
    }
    if lines.last().is_some_and(|l| l.trim() == "continue;") {
        lines.pop();
    }
    let header_label = label(st.blocks[i].start);
    if lines.first().is_some_and(|l| l.trim() == header_label) {
        lines.remove(0);
        out.push_str(&header_label);
        out.push('\n');
    }
    let (opener, body, closer) = match latch_of(&lines, has_break) {
        Some(Latch { cond, at, after }) => {
            let mut closer = format!("}} while ({cond});\n");
            for l in after {
                closer.push_str(l);
                closer.push('\n');
            }
            let mut body: Vec<String> = lines.get(..at).unwrap_or(&[]).to_vec();
            let mut latch: Vec<String> = Vec::new();
            while body.last().is_some_and(|l| is_label(l)) {
                if let Some(l) = body.pop() {
                    latch.push(l);
                }
            }
            for latch_label in &latch {
                let jump = format!("goto {};", label_name(latch_label).unwrap_or(""));
                let mut open: Vec<Scope> = Vec::new();
                for l in &mut body {
                    let level = at_continue_level(l, &mut open);
                    if level && let Some(pos) = l.find(&jump) {
                        *l = format!("{}continue;", &l[..pos]);
                    }
                }
            }
            while body.last().is_some_and(|l| l == "continue;") {
                body.pop();
            }
            body.extend(latch.into_iter().rev());
            ("do {\n", body, closer)
        }
        None => ("while (1) {\n", lines.clone(), "}\n".to_owned()),
    };
    out.push_str(opener);
    for l in &body {
        if !l.is_empty() {
            out.push_str("  ");
        }
        out.push_str(l);
        out.push('\n');
    }
    out.push_str(&closer);
    if has_break && let Some(va) = join_va {
        let _ = writeln!(out, "{}", goto(va));
    }
    Some(join.unwrap_or(max + 1))
}

/// Where a `while (1)` body decides whether to go round again, when the
/// loop reads as `do { ... } while (cond);`.
pub(super) struct Latch<'l> {
    /// The condition under which the loop goes round again.
    pub(super) cond: String,
    /// Index of the line holding the test: the body is the lines before it.
    pub(super) at: usize,
    /// The lines written after `} while (cond);`: what runs once the loop
    /// is left, ending with its transfer when that is a `return`.
    pub(super) after: Vec<&'l str>,
}

/// Finds the test a `while (1)` body ends with, so the loop can be written
/// as a `do`/`while`.
///
/// Two shapes qualify. `BODY; if (c) break;` goes round while `c` fails.
/// `BODY; if (c) continue; TAIL; break;` (or a `return` in place of the
/// `break`) goes round while `c` holds and runs `TAIL` once it does not:
/// `TAIL` moves after the loop, so it must neither break nor continue at
/// the loop's level. Either way `BODY` may not `continue` (in a do-while
/// that tests the condition, where the original skipped it), and when a
/// `TAIL` moves out, `BODY` may not `break` either (it would land on the
/// `TAIL` it skipped). A `TAIL` of labels alone is the latch's exit, so a
/// `break` in `BODY` still lands on the join then, unless the exit is a
/// `return`.
///
/// # Arguments
///
/// * `lines` - The loop body at its own level (nested blocks indented),
///   the trailing `continue;` already dropped.
/// * `has_break` - Whether the body breaks to the loop's join anywhere.
///
/// # Returns
///
/// The latch, or `None` when the loop keeps its `while (1)` form.
pub(super) fn latch_of(lines: &[String], has_break: bool) -> Option<Latch<'_>> {
    let exit_at = (0..lines.len()).rev().find(|&i| !is_label(&lines[i]))?;
    let exit_line = lines.get(exit_at)?;
    let exit = exit_line.trim();
    let body = lines.get(..exit_at)?;
    if exit_at + 1 == lines.len()
        && !exit_line.starts_with(' ')
        && let Some(c) = exit
            .strip_prefix("if (")
            .and_then(|r| r.strip_suffix(") break;"))
        && !continues_at_top(body)
    {
        return Some(Latch {
            cond: invert_condition(c),
            at: exit_at,
            after: Vec::new(),
        });
    }
    if exit != "break;" && !is_return(exit) {
        return None;
    }
    let (at, cond) = body.iter().enumerate().rev().find_map(|(k, l)| {
        let c = l.strip_prefix("if (")?.strip_suffix(") continue;")?;
        Some((k, c))
    })?;
    let head = lines.get(..at)?;
    let tail = lines.get(at + 1..exit_at)?;
    let labels_only = tail.iter().all(|l| is_label(l));
    let fits = if labels_only {
        exit == "break;" || !has_break
    } else {
        !breaks_at_top(tail) && !continues_at_top(tail) && !breaks_at_top(head)
    };
    if !fits || continues_at_top(head) {
        return None;
    }
    let mut after: Vec<&str> = tail.iter().map(String::as_str).collect();
    if exit != "break;" {
        after.push(exit);
    }
    Some(Latch {
        cond: cond.to_owned(),
        at,
        after,
    })
}

/// Tells whether a loop body breaks out of its own loop: a `break` outside
/// every nested loop and switch.
///
/// # Arguments
///
/// * `body` - The body lines, nested blocks indented deeper.
pub(super) fn breaks_at_top(body: &[String]) -> bool {
    let mut nested: Vec<Scope> = Vec::new();
    body.iter()
        .any(|l| at_loop_level(l, &mut nested) && breaks(l.trim()))
}

/// Tells whether a loop body continues its own loop before its end: a
/// `continue` outside every nested loop.
///
/// # Arguments
///
/// * `body` - The body lines, nested loops indented deeper.
pub(super) fn continues_at_top(body: &[String]) -> bool {
    let mut nested: Vec<Scope> = Vec::new();
    body.iter()
        .any(|l| at_continue_level(l, &mut nested) && continues(l.trim()))
}

/// Finds the loop block `i` belongs to.
///
/// The loop is the set of blocks that reach `i` and that `i` reaches
/// without passing an enclosing loop's header, an emitted block or the
/// emission bound; its entry is the one member with a predecessor outside
/// it. Compilers often place a loop's header after part of its body (a
/// `jmp` to the condition at the bottom, the body above it), so the header
/// need not be the lowest block.
///
/// # Arguments
///
/// * `st` - Emission state.
/// * `i` - Any block.
///
/// # Returns
///
/// The loop's blocks and its entry, or `None` when `i` is on no cycle or the
/// cycle has several entries.
pub(super) fn cycle_of<L: Lifter>(st: &Emit<'_, L>, i: usize) -> Option<(BTreeSet<usize>, usize)> {
    let n = st.blocks.len();
    let open = |b: usize| !st.outside(b) && !st.emitted[b] && !st.loops.contains(&b);
    let mut forward = vec![false; n];
    let mut work = vec![i];
    while let Some(b) = work.pop() {
        for &s in &st.succs[b] {
            if open(s) && !forward[s] {
                forward[s] = true;
                work.push(s);
            }
        }
    }
    if !forward[i] {
        return None;
    }
    let mut backward = vec![false; n];
    work.push(i);
    while let Some(b) = work.pop() {
        for &p in &st.preds[b] {
            if open(p) && !backward[p] {
                backward[p] = true;
                work.push(p);
            }
        }
    }
    let body: BTreeSet<usize> = (0..n).filter(|&b| forward[b] && backward[b]).collect();
    let mut entries = body
        .iter()
        .copied()
        .filter(|&b| b == st.entry || st.preds[b].iter().any(|p| !body.contains(p)));
    match (entries.next(), entries.next()) {
        (Some(entry), None) => Some((body, entry)),
        _ => None,
    }
}

/// Structures through a trampoline block.
///
/// A block holding nothing but `jmp X`, entered only from `header`, that
/// writes out nothing `X` lacks is a detour on the way to `X`: `X` is now
/// entered from the header directly (the header's successor edge is
/// rewired too, so a later [`consume`] of the header into its own
/// predecessor re-parents through it) and the trampoline is never emitted.
///
/// # Arguments
///
/// * `ctx` - Per-function state (unused; kept for symmetry with the other structurers).
/// * `st` - Emission state.
/// * `header` - The block whose branch reaches `b`.
/// * `b` - The candidate trampoline.
/// * `journal` - Where the rewiring is recorded.
///
/// # Returns
///
/// The trampoline's target, or `b` itself when it is not a trampoline.
pub(super) fn follow_trampoline<L: Lifter>(
    ctx: &Ctx<'_>,
    st: &mut Emit<'_, L>,
    header: usize,
    b: usize,
    journal: &mut Journal,
) -> usize {
    let block = &st.blocks[b];
    if block.term != BlockTerm::Jmp || st.preds[b].len() != 1 || st.succs[b].len() != 1 {
        return b;
    }
    let target = st.succs[b][0];
    if target == b || st.emitted[b] {
        return b;
    }
    let _ = ctx;
    if st.code[b].len() != 1 {
        return b;
    }
    if !phi_keys(
        &st.in_envs[b],
        &st.succs[b],
        st.in_envs,
        st.live,
        st.processed,
        None,
    )
    .is_empty()
    {
        return b;
    }
    journal.emitted(st, b);
    st.emitted[b] = true;
    journal.preds(st, target);
    for p in &mut st.preds[target] {
        if *p == b {
            *p = header;
        }
    }
    journal.succs(st, header);
    for s in &mut st.succs[header] {
        if *s == b {
            *s = target;
        }
    }
    target
}

/// Tells whether a structured body has no effect (nothing but labels).
///
/// Since the region was closed, no outside goto can target those labels
/// either, so the body can be dropped.
///
/// # Arguments
///
/// * `buf` - The body text.
pub(super) fn is_dead_body(buf: &str) -> bool {
    buf.lines().all(|l| l.trim().is_empty() || is_label(l))
}

/// Emits `if (cond) { body }`, or nothing for a dead body unless the
/// condition calls something, which runs whatever the arm holds.
///
/// # Arguments
///
/// * `out` - Receives the text.
/// * `cond` - The rendered condition.
/// * `body` - The arm's text.
/// * `calls` - Whether the condition calls a function ([`Guard::calls`]).
pub(super) fn push_if(out: &mut String, cond: &str, body: &str, calls: bool) {
    if is_dead_body(body) && !calls {
        return;
    }
    let _ = writeln!(out, "if ({cond}) {{");
    out.push_str(&indent(body));
    out.push_str("}\n");
}

/// Detects a `while` loop headed by `header`.
///
/// Regions are expanded from both branch sides; the one containing a back
/// edge to the header is the body. The body may exit only back to the header
/// (strict loop) or to the header's other branch side (break-style); the
/// other side must not reach the header.
///
/// # Arguments
///
/// * `st` - Emission state.
/// * `header` - The conditional block.
/// * `t` - Its branch target block.
/// * `f` - Its fall-through block.
///
/// # Returns
///
/// `(body region, exit block, the side the body is on)`, or `None`.
pub(super) fn try_while<L: Lifter>(
    st: &Emit<'_, L>,
    header: usize,
    t: usize,
    f: usize,
) -> Option<(Region, usize, Side)> {
    try_while_with(st, header, t, f, None)
}

/// [`try_while`] with the two arms' bases computed already ([`base_of`]
/// from `t` stopping at `f`, and from `f` stopping at `t`), when the caller
/// has them.
///
/// # Arguments
///
/// * `st` - Emission state.
/// * `header` - The conditional block.
/// * `t` - Its branch target block.
/// * `f` - Its fall-through block.
/// * `bases` - The target side's base and the fall-through side's.
pub(super) fn try_while_with<L: Lifter>(
    st: &Emit<'_, L>,
    header: usize,
    t: usize,
    f: usize,
    bases: Option<(&Base, &Base)>,
) -> Option<(Region, usize, Side)> {
    let headers: BTreeSet<usize> = [header].into_iter().collect();
    let base_for = |start: usize| bases.map(|(bt, bf)| if start == t { bt } else { bf });
    for (start, side, stop_at) in [(t, Side::Target, Some(f)), (f, Side::Fall, Some(t))] {
        if start == header {
            continue;
        }
        let region = closed_run_with(st, start, &headers, stop_at, base_for(start));
        let back = region.order.iter().any(|b| st.succs[*b].contains(&header));
        if !back || !region.closed {
            continue;
        }
        let other = match side {
            Side::Target => f,
            Side::Fall => t,
        };
        let stray = region.exits.iter().any(|e| *e != header && *e != other);
        if !stray && !region.order.contains(&other) && other != header {
            let other_region = closed_run_with(st, other, &headers, Some(start), base_for(other));
            let other_back = other_region
                .order
                .iter()
                .any(|b| st.succs[*b].contains(&header));
            if !other_back && !other_region.order.contains(&header) {
                return Some((region, other, side));
            }
        }
    }
    None
}

/// Most bodies a `switch` may have.
///
/// The bodies are what a reader reads, so this is the size that matters.
pub(super) const SWITCH_ARMS_MAX: usize = 64;

/// Most values a `switch` may dispatch on.
///
/// A compiler that folds many values onto few bodies puts a byte table in
/// front of the jump table, and the values it maps are the ones the source
/// wrote; listing seventy of them across fifteen bodies is what the code
/// says, where switching on the byte table's own index would say nothing a
/// reader could use.
pub(super) const SWITCH_VALUES_MAX: usize = 512;

/// Emits a `switch` for a jump-table dispatch block.
///
/// One arm per distinct target, in first-appearance order, with every case
/// number listed; each arm is a closed region emitted in flow order (an arm
/// entered from elsewhere too contributes only its first block). The exit
/// shared by every arm is where the switch ends: gotos to it become `break`
/// and the text jumps there after the switch.
///
/// # Arguments
///
/// * `ctx` - Per-function state (the jump tables).
/// * `st` - Emission state.
/// * `i` - The dispatch block.
/// * `idx_expr` - The switch index expression.
/// * `out` - Receives the text.
/// * `depth` - Structuring nesting depth.
///
/// # Returns
///
/// The block after the switch, or `None` when the table is missing, empty,
/// reaches more than [`SWITCH_ARMS_MAX`] distinct bodies, or holds more
/// than [`SWITCH_VALUES_MAX`] values.
pub(super) fn try_switch<L: Lifter>(
    ctx: &mut Ctx<'_>,
    st: &mut Emit<'_, L>,
    i: usize,
    idx_expr: &Expr,
    out: &mut String,
    depth: usize,
) -> Option<usize> {
    let block = &st.blocks[i];
    let site = *ctx
        .analysis
        .jump_tables
        .range(block.start..block.end)
        .next()
        .map(|(k, _)| k)?;
    let targets = ctx.analysis.jump_tables.get(&site)?;
    if targets.is_empty() || targets.len() > SWITCH_VALUES_MAX {
        return None;
    }
    let arms: Vec<Arm> = table_arms(targets)
        .into_iter()
        .filter_map(|(target, ns)| {
            Some(Arm {
                body: st.index_of(target)?,
                labels: case_labels(&ns),
            })
        })
        .collect();
    if arms.len() > SWITCH_ARMS_MAX {
        return None;
    }
    let names = ctx.names();
    let idx_expr = match idx_expr {
        Expr::Sext(e, _) => e.as_ref(),
        other => other,
    };
    let switch_expr = idx_expr.render(&names);
    let headers: BTreeSet<usize> = [i].into_iter().collect();
    Some(emit_switch(
        ctx,
        st,
        &headers,
        &switch_expr,
        &arms,
        None,
        out,
        depth,
    ))
}

/// Emits a `switch` whose arms are given: each a body block with its case
/// labels, and a default body when there is one.
///
/// Each arm is a closed region emitted in flow order (an open one
/// contributes only its first block). A body written already, or entered
/// from code after the dispatch that no arm holds (a loop's tail one case
/// skips to, reached by every other case's continuation), is the switch's
/// continuation, not its to write: its arm is a jump to it. So is a body
/// an earlier arm runs into and has written by the time its own arm comes
/// up: an empty arm there would break out of the switch instead. The switch
/// ends at the exit most arms leave through, a jump arm's target counting
/// as an exit: gotos to it become `break` and the text jumps there after
/// the switch, while an arm leaving elsewhere keeps its goto. A default
/// body that is that exit is no arm: the switch falls out into it.
///
/// # Arguments
///
/// * `ctx` - Per-function state.
/// * `st` - Emission state.
/// * `headers` - The blocks that dispatch: the jump-table block, or a
///   compare tree's blocks; the first is the one whose text this follows.
/// * `switch_expr` - The rendered value switched on.
/// * `arms` - The bodies with their `case N:` labels.
/// * `default` - The block every other value reaches.
/// * `out` - Receives the text.
/// * `depth` - Structuring nesting depth.
///
/// # Returns
///
/// The block after the switch.
#[expect(clippy::too_many_arguments, reason = "the structurer's shape")]
pub(super) fn emit_switch<L: Lifter>(
    ctx: &mut Ctx<'_>,
    st: &mut Emit<'_, L>,
    headers: &BTreeSet<usize>,
    switch_expr: &str,
    arms: &[Arm],
    default: Option<usize>,
    out: &mut String,
    depth: usize,
) -> usize {
    /// An arm with the region it writes, or none for an arm that is a
    /// jump to the switch's continuation.
    struct SwitchArm {
        /// The body and its labels.
        arm: Arm,
        /// The closed region the body heads, when the switch writes it.
        region: Option<Region>,
    }
    /// The region an arm's body is, and the exits it had before an open
    /// one was cut down to its first block.
    fn arm_region<L: Lifter>(
        st: &Emit<'_, L>,
        headers: &BTreeSet<usize>,
        bi: usize,
    ) -> (Region, BTreeSet<usize>) {
        let mut region = closed_run_from(st, bi, headers, None);
        let exits = region.exits.clone();
        if !region.closed {
            region.order = vec![bi];
            region.dups.clear();
        }
        (region, exits)
    }
    let i = headers.iter().next().copied().unwrap_or(0);
    let bodies: Vec<Arm> = arms
        .iter()
        .cloned()
        .chain(default.map(|d| Arm {
            body: d,
            labels: vec!["default:".to_owned()],
        }))
        .collect();
    let prelim: Vec<(Region, BTreeSet<usize>)> = bodies
        .iter()
        .map(|arm| arm_region(st, headers, arm.body))
        .collect();
    let held: BTreeSet<usize> = prelim
        .iter()
        .flat_map(|(r, _)| r.order.iter().copied())
        .collect();
    let continuation = |st: &Emit<'_, L>, b: usize| {
        st.emitted[b]
            || st.preds[b]
                .iter()
                .any(|p| !headers.contains(p) && !held.contains(p) && *p > i)
    };
    let mut votes: BTreeMap<usize, usize> = BTreeMap::new();
    let mut regions: Vec<SwitchArm> = Vec::new();
    for (arm, (region, exits)) in bodies.into_iter().zip(prelim) {
        if continuation(st, arm.body) {
            *votes.entry(arm.body).or_insert(0) += 1;
            regions.push(SwitchArm { arm, region: None });
            continue;
        }
        for e in exits {
            *votes.entry(e).or_insert(0) += 1;
        }
        regions.push(SwitchArm {
            arm,
            region: Some(region),
        });
    }
    let join = votes
        .iter()
        .max_by(|a, b| a.1.cmp(b.1).then(b.0.cmp(a.0)))
        .map(|(b, _)| *b);
    if let Some(d) = default
        && Some(d) == join
        && regions
            .last()
            .is_some_and(|s| s.arm.body == d && s.region.is_none())
    {
        regions.pop();
    }
    let join_start = join.and_then(|j| st.start_of(j));
    let _ = writeln!(out, "switch ({switch_expr}) {{");
    for SwitchArm { arm, region } in &regions {
        let labels = arm.labels.join(" ");
        let Some(region) = region
            .as_ref()
            .filter(|r| !st.emitted[arm.body] || r.dups.contains(&arm.body))
        else {
            if Some(arm.body) == join {
                let _ = writeln!(out, "{labels} break;");
            } else {
                let _ = writeln!(out, "{labels} {}", jump_to(st, st.start(arm.body)));
            }
            continue;
        };
        let _ = writeln!(out, "{labels} {{");
        let mut buf = String::new();
        emit_run(ctx, st, region, join_start, join_start, &mut buf, depth + 1);
        if !buf.lines().last().is_some_and(transfers) {
            buf.push_str("break;\n");
        }
        out.push_str(&indent(&buf));
        out.push_str("}\n");
    }
    out.push_str("}\n");
    if let Some(js) = join_start {
        let _ = writeln!(out, "{}", goto(js));
    }
    join.unwrap_or(i + 1)
}

/// Emits a region's blocks in order, recursing into structured children.
///
/// A copied tail ([`Region::dups`]) is placed where the text reaches it:
/// the region's first block is entered by the header's branch, a later copy
/// replaces the jump to the shared block, and anywhere else the arm that
/// consumed its predecessor already holds one while the original keeps
/// serving every other path. A final goto to `join_start` is dropped; inside
/// a loop body, gotos to the exit become `break` (also inside
/// `if (c) goto L_exit;`) and gotos to the join `continue` when the join is
/// the loop's header. A switch arm, or an exit region a loop absorbed, joins
/// at its own exit: there a goto to it nested in a switch the region opens
/// stays a goto, since `continue` would run a loop no one wrote and `break`
/// would leave only the inner switch.
///
/// # Arguments
///
/// * `ctx` - Per-function state.
/// * `st` - Emission state.
/// * `region` - The region to emit.
/// * `join_start` - Address of the block the region continues at, `None`
///   when the text ends with the region.
/// * `loop_exit` - Inside a loop body, the address of the loop's exit.
/// * `out` - Receives the text.
/// * `depth` - Structuring nesting depth.
///
/// A jump to the loop's exit becomes `break` and one to its header
/// `continue`, but only where the line stands in this loop and not in one
/// the body opens itself ([`at_loop_level`]).
pub(super) fn emit_run<L: Lifter>(
    ctx: &mut Ctx<'_>,
    st: &mut Emit<'_, L>,
    region: &Region,
    join_start: Option<u64>,
    loop_exit: Option<u64>,
    out: &mut String,
    depth: usize,
) {
    let mut kept: Vec<String> = Vec::new();
    let mut order = region.order.clone();
    if let Some(j) = join_start.and_then(|va| st.index_of(va))
        && !order.contains(&j)
    {
        order.push(j);
    }
    st.orders.push((order, 0));
    st.dup_stack.push(region.dups.clone());
    for (pos, &b) in region.order.iter().enumerate() {
        st.set_pos(pos);
        if region.dups.contains(&b) {
            let jump = goto(st.blocks[b].start);
            let jumped = kept.last().is_some_and(|l| l.trim() == jump);
            if pos != 0 && !jumped {
                continue;
            }
            if jumped {
                kept.pop();
            }
            let copy = run_block(ctx, st, b);
            kept.extend(copy.lines.iter().cloned());
            if let Some(t) = copy.goto {
                kept.push(jump_to(st, t));
            } else if runs_on(st, b)
                && let Some(&s) = st.succs[b].first()
            {
                kept.push(goto(st.start(s)));
            } else if let Some(t) = falls_outside(ctx, st, b) {
                kept.push(jump_to(st, t));
            }
            continue;
        }
        if st.emitted[b] {
            continue;
        }
        let mut buf = String::new();
        emit_block(ctx, st, b, &mut buf, depth);
        kept.extend(buf.lines().map(str::to_owned));
    }
    st.orders.pop();
    st.dup_stack.pop();
    let join_goto = join_start.map(goto);
    if let Some(j) = &join_goto
        && kept.last().is_some_and(|l| l.trim() == j)
    {
        kept.pop();
    }
    if let Some(exit_start) = loop_exit {
        let break_goto = goto(exit_start);
        let mut open: Vec<Scope> = Vec::new();
        let mut open_continue: Vec<Scope> = Vec::new();
        for l in &mut kept {
            let level = at_loop_level(l, &mut open);
            let at_continue = at_continue_level(l, &mut open_continue);
            if level && let Some(pos) = l.find(&break_goto) {
                *l = format!("{}break;", &l[..pos]);
            } else if at_continue
                && join_start != Some(exit_start)
                && let Some(j) = &join_goto
                && let Some(pos) = l.find(j)
            {
                *l = format!("{}continue;", &l[..pos]);
            }
        }
    }
    for l in kept {
        out.push_str(&l);
        out.push('\n');
    }
}
