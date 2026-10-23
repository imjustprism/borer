//! Conditional assignments written as the statements a source spells.
//!
//! A compiler turns `if (c) x = k;` into a conditional move that keeps the
//! old value otherwise (`cmov`, an IT block), which reads back as `x = c ?
//! k : x;`: a choice that is no choice on one side, where the source wrote
//! an `if`. The other way round, a truth value a source computes as `x = a
//! && b;` compiles to the branches of an `if`/`else` that store `1` and `0`,
//! which reads back as two arms that each only store a constant.

use super::*;

/// Rewrites the conditional assignments of a function as the statements
/// their sources spell.
///
/// `x = c ? k : x;` is `if (c) { x = k; }` and `x = c ? x : k;` is the
/// same under the inverted test ([`kept_select`]); an `if`/`else` over a
/// short-circuit test whose arms store `1` and `0` in one variable is that
/// variable set to the test ([`truth_diamond`]); an `if` nested alone in
/// an `if` behind values only its test reads is one `&&` chain
/// ([`and_chain`]); an `else` that stores a default and then repeats the
/// first arm under a second test is one `||` ([`or_default`]); an `if`
/// whose arms store two different names is that choice ([`named_choice`]);
/// a select between a value and that value with one bit updated, under the
/// opposite test, is the `if` of that bit ([`complement_bits`]); and a
/// byte-wide flag a chain compares with zero is the flag itself
/// ([`quiet_flags`]).
///
/// # Arguments
///
/// * `text` - A decompiled function.
///
/// # Returns
///
/// The text with those assignments rewritten, or unchanged.
pub(super) fn select_statements(text: &str) -> String {
    let mut lines: Vec<String> = text.lines().map(str::to_owned).collect();
    let mut changed = false;
    let mut k = 0;
    while k < lines.len() {
        if let Some(rewritten) = lines.get(k).and_then(|l| kept_select(l)) {
            let n = rewritten.len();
            lines.splice(k..=k, rewritten);
            changed = true;
            k += n;
            continue;
        }
        if clamp_hoist(&mut lines, k) {
            changed = true;
            k += 3;
            continue;
        }
        if hoist_break_copy(&mut lines, k)
            || and_chain(&mut lines, k)
            || redundant_if_return(&mut lines, k)
            || preassigned_if_else(&mut lines, k)
            || or_default(&mut lines, k)
            || named_choice(&mut lines, k)
            || complement_bits(&mut lines, k)
        {
            changed = true;
            continue;
        }
        if dup_merge(&mut lines, k) {
            changed = true;
            k = k.saturating_sub(1);
            continue;
        }
        changed |= truth_diamond(&mut lines, k);
        k += 1;
    }
    let flags = byte_names(&lines);
    for line in lines
        .iter_mut()
        .filter(|l| !l.trim_start().starts_with("//"))
    {
        if let Some(quiet) = quiet_flags(line, &flags) {
            *line = quiet;
            changed = true;
        }
    }
    if !changed {
        return text.to_owned();
    }
    let mut out = lines.join("\n");
    out.push('\n');
    out
}

/// The names the function declares a byte wide: `uint8_t` and `bool`
/// locals and parameters, and the `g8_` globals.
///
/// # Arguments
///
/// * `lines` - The function.
fn byte_names(lines: &[String]) -> BTreeSet<String> {
    let mut out = BTreeSet::new();
    for line in lines {
        let t = line.trim();
        let t = t.strip_prefix("// signature: ").unwrap_or(t);
        for word in ["uint8_t ", "bool "] {
            for (at, _) in t.match_indices(word) {
                if t.get(..at).is_some_and(|h| h.ends_with(is_ident_char)) {
                    continue;
                }
                let rest = t.get(at + word.len()..).unwrap_or("");
                let list_end = if t.contains('(') {
                    rest.find([',', ')']).unwrap_or(rest.len())
                } else {
                    rest.find(';').unwrap_or(rest.len())
                };
                for name in rest.get(..list_end).unwrap_or("").split(", ") {
                    if is_ident(name.trim()) {
                        out.insert(name.trim().to_owned());
                    }
                }
            }
        }
        out.extend(
            tokens(t)
                .filter(|w| w.starts_with("g8_"))
                .map(str::to_owned),
        );
    }
    out
}

/// Writes the zero tests on byte-wide truth values that stand as operands
/// of a short-circuit chain as the values themselves: `f != 0 && g == 0`
/// as `f && !g`.
///
/// The two spellings test the same, and a flag a source tests in a chain
/// is spelled bare there; compared with zero, each operand reads as a
/// comparison of its own. A line with a string or character literal is
/// left alone, since the text inside the quotes is data, not a test.
///
/// # Arguments
///
/// * `line` - One line.
/// * `flags` - The byte-wide names ([`byte_names`]).
///
/// # Returns
///
/// The line rewritten, or `None` when no such test is in it.
fn quiet_flags(line: &str, flags: &BTreeSet<String>) -> Option<String> {
    if !(line.contains(" && ") || line.contains(" || ")) || line.contains(['"', '\'']) {
        return None;
    }
    let mut out = line.to_owned();
    let mut changed = false;
    for name in flags {
        for (test, neg) in [(" != 0", ""), (" == 0", "!")] {
            let pat = format!("{name}{test}");
            let mut from = 0;
            while let Some(at) = out.get(from..).and_then(|r| r.find(&pat)).map(|k| k + from) {
                let before = out.get(..at).unwrap_or("");
                let after = out.get(at + pat.len()..).unwrap_or("");
                let open = before.ends_with('(')
                    && !before.get(..before.len() - 1).is_some_and(|h| {
                        h.ends_with(|c: char| is_ident_char(c) || c == ')' || c == ']')
                    });
                let left = before.ends_with("&& ") || before.ends_with("|| ");
                let right = after.starts_with(" &&") || after.starts_with(" ||");
                let closes = after.starts_with(')');
                if (left && (right || closes)) || (open && right) {
                    out.replace_range(at..at + pat.len(), &format!("{neg}{name}"));
                    changed = true;
                    from = at + neg.len() + name.len();
                } else {
                    from = at + pat.len();
                }
            }
        }
    }
    changed.then_some(out)
}

/// The `if` a conditional assignment that keeps its variable on one side
/// stands for: `x = c ? k : x;` as `if (c) {`, `x = k;`, `}`.
///
/// A narrow conditional move into a wide variable masks what it keeps as
/// well as what it moves, `x = (c ? k : x) & 0xffffffff;`; the mask then
/// follows the `if`, on both paths as before.
///
/// # Arguments
///
/// * `line` - One line.
///
/// # Returns
///
/// The three lines, or `None` when the line is no such assignment.
fn kept_select(line: &str) -> Option<Vec<String>> {
    if line.trim_start().starts_with("//") {
        return None;
    }
    let (lhs, rhs) = plain_assignment(line)?;
    let masked = rhs.rsplit_once(") & ").filter(|(head, mask)| {
        parse_const(mask).is_some() && opening_paren(rhs, head.len()) == Some(0)
    });
    let (choice, mask) = match masked {
        Some((head, mask)) => (rhs.get(..=head.len())?, Some(mask)),
        None => (rhs, None),
    };
    let (cond, yes, no) = ternary(choice)?;
    let (cond, value) = if no == lhs && yes != lhs {
        (cond.to_owned(), yes)
    } else if yes == lhs && no != lhs {
        (invert_condition(cond), no)
    } else {
        return None;
    };
    let pad = " ".repeat(indent_of(line));
    let mut out = vec![
        format!("{pad}if ({cond}) {{"),
        format!("{pad}  {lhs} = {value};"),
        format!("{pad}}}"),
    ];
    if let Some(mask) = mask {
        out.push(format!("{pad}{lhs} = {lhs} & {mask};"));
    }
    Some(out)
}

/// The prefixes of the names the frame's slots go by: a write to one can
/// reach a buffer whose address the function hands on.
const FRAME: [&str; 3] = ["local_", "arg_", "home_"];

/// Writes a choice that keeps a variable on one side, inside a larger
/// statement, as the `if` that sets the variable first: `y = (x < 2 ? 2 :
/// x) << 28;` as `if (x < 2) { x = 2; } y = x << 28;`.
///
/// That is a clamp a source wrote before the variable's one use. It holds
/// when the variable is one the function declares, not a named constant
/// such as `NAN`, and is read nowhere but in the choice, so its new value
/// reaches no one else; the statement and the test call nothing, so the
/// test runs as early unseen; no `&&`, `||` or other choice before it in
/// the statement can skip it, so hoisting it reads nothing the statement
/// might not; no loop or label surrounds the line, so the
/// test runs once, against what it saw before; and the variable is no
/// frame slot of a function that takes a slot's address or calls anything
/// after the line, since a slot whose address escapes can be read as part
/// of a buffer. A `return` keeps its choice: a value chosen to
/// be returned is a source's `?:`.
///
/// # Arguments
///
/// * `lines` - The body lines.
/// * `k` - The line of the statement.
///
/// # Returns
///
/// Whether the statement was rewritten.
fn clamp_hoist(lines: &mut Vec<String>, k: usize) -> bool {
    let Some(line) = lines.get(k).filter(|l| l.trim().ends_with(';')) else {
        return false;
    };
    let t = line.trim();
    if t.starts_with("//")
        || t.starts_with("for (")
        || t.starts_with("return")
        || t.starts_with('}')
        || impure(t)
        || lines.iter().any(|l| is_label(l))
    {
        return false;
    }
    let code = |l: &&String| !l.trim_start().starts_with("//");
    let frame_addressed = lines
        .iter()
        .filter(code)
        .any(|l| FRAME.iter().any(|f| l.contains(&format!("&{f}"))))
        || lines.iter().skip(k + 1).filter(code).any(|l| impure(l));
    let pad = indent_of(line);
    let looped = (0..k).rev().try_fold(pad, |level, o| {
        let l = lines.get(o)?;
        if l.trim().is_empty() || indent_of(l) >= level {
            return Some(level);
        }
        let o = l.trim();
        let loop_head = ["while (", "for (", "do {"]
            .iter()
            .any(|p| o.starts_with(p));
        (!loop_head).then(|| indent_of(l))
    });
    if looped.is_none() {
        return false;
    }
    let Some((open, close, cond, value, v)) =
        t.char_indices()
            .filter(|&(_, c)| c == ')')
            .find_map(|(close, _)| {
                let open = opening_paren(t, close)?;
                if t.get(..open)
                    .is_some_and(|h| h.ends_with(|c: char| is_ident_char(c) || c == ']'))
                {
                    return None;
                }
                let (cond, yes, no) = ternary(t.get(open + 1..close)?)?;
                let named = |s: &str| is_ident(s) && s.starts_with(|c: char| !c.is_ascii_digit());
                let (cond, value, v) = if named(no) && yes != no {
                    (cond.to_owned(), yes, no)
                } else if named(yes) && yes != no {
                    (invert_condition(cond), no, yes)
                } else {
                    return None;
                };
                let span = t.get(open..=close)?;
                let elsewhere = word_positions(t, v).len() != word_positions(span, v).len()
                    || mentions_ident(value, v)
                    || (frame_addressed && FRAME.iter().any(|f| v.starts_with(f)))
                    || lines.iter().enumerate().any(|(j, l)| {
                        j != k
                            && mentions_ident(l, v)
                            && !declares(l)
                            && !l.trim_start().starts_with("//")
                    });
                let declared = lines.iter().any(|l| declares(l) && mentions_ident(l, v));
                let guarded = t
                    .get(..open)
                    .is_some_and(|p| p.contains("&&") || p.contains("||") || p.contains('?'));
                (!elsewhere
                    && declared
                    && !guarded
                    && plain_assignment(t).is_none_or(|(lhs, _)| lhs != v))
                .then(|| (open, close, cond, value.to_owned(), v.to_owned()))
            })
    else {
        return false;
    };
    let pad_s = " ".repeat(pad);
    let rest = format!(
        "{pad_s}{}{v}{}",
        t.get(..open).unwrap_or(""),
        t.get(close + 1..).unwrap_or("")
    );
    let rewritten = vec![
        format!("{pad_s}if ({cond}) {{"),
        format!("{pad_s}  {v} = {value};"),
        format!("{pad_s}}}"),
        rest,
    ];
    lines.splice(k..=k, rewritten);
    true
}

/// The test and the two values of a conditional expression, when the
/// whole expression is one (inside one pair of brackets or none).
///
/// # Arguments
///
/// * `rhs` - An expression.
fn ternary(rhs: &str) -> Option<(&str, &str, &str)> {
    let mut e = rhs.trim();
    while let Some(inner) = e.strip_prefix('(').and_then(|r| r.strip_suffix(')')) {
        if opening_paren(e, e.len() - 1) != Some(0) {
            break;
        }
        e = inner.trim();
    }
    let mut depth = 0i32;
    let mut quote: Option<char> = None;
    let mut escaped = false;
    let mut question: Option<usize> = None;
    let mut pending = 0usize;
    for (i, c) in e.char_indices() {
        if let Some(q) = quote {
            match c {
                _ if escaped => escaped = false,
                '\\' => escaped = true,
                _ if c == q => quote = None,
                _ => {}
            }
            continue;
        }
        match c {
            '"' | '\'' => quote = Some(c),
            '(' | '[' => depth += 1,
            ')' | ']' => depth -= 1,
            '?' if depth == 0 => {
                if question.is_none() {
                    question = Some(i);
                } else {
                    pending += 1;
                }
            }
            ':' if depth == 0 && question.is_some() => {
                if pending == 0 {
                    let q = question?;
                    return Some((
                        e.get(..q)?.trim(),
                        e.get(q + 1..i)?.trim(),
                        e.get(i + 1..)?.trim(),
                    ));
                }
                pending -= 1;
            }
            _ => {}
        }
    }
    None
}

/// Rewrites the `if (a && b) { x = 1; } else { x = 0; }` at line `k` as
/// `x = a && b;`.
///
/// The test must be a short-circuit chain: a lone comparison stored as a
/// truth value compiles to a `setcc`, not to branches, so arms storing `1`
/// and `0` behind one comparison are an `if` the source wrote. Statements
/// both arms open with go in front of the `if` when they assign, without a
/// call, a private variable ([`private`]) the test does not read: the test
/// calls nothing and reads none of them, and no pointer it reads through
/// reaches them, so running them first changes nothing it sees.
///
/// # Arguments
///
/// * `lines` - The body lines.
/// * `k` - The line of the `if`.
///
/// # Returns
///
/// Whether the `if` was rewritten.
fn truth_diamond(lines: &mut Vec<String>, k: usize) -> bool {
    let Some(open) = lines.get(k) else {
        return false;
    };
    let pad = indent_of(open);
    let Some(cond) = if_opener(open.trim()).map(str::to_owned) else {
        return false;
    };
    if !(cond.contains(" && ") || cond.contains(" || ")) || impure(&cond) {
        return false;
    }
    let Some(mid) = loops::closing(lines, k, pad)
        .filter(|&m| lines.get(m).is_some_and(|l| l.trim() == "} else {"))
    else {
        return false;
    };
    let Some(close) =
        loops::closing(lines, mid, pad).filter(|&c| lines.get(c).is_some_and(|l| l.trim() == "}"))
    else {
        return false;
    };
    let then = lines.get(k + 1..mid).unwrap_or(&[]);
    let other = lines.get(mid + 1..close).unwrap_or(&[]);
    let (Some((t_last, t_head)), Some((o_last, o_head))) = (then.split_last(), other.split_last())
    else {
        return false;
    };
    let heads_hoist = t_head == o_head
        && t_head.iter().all(|l| {
            indent_of(l) == pad + 2
                && plain_assignment(l).is_some_and(|(v, r)| {
                    private(lines, v) && !impure(r) && !mentions_ident(&cond, v)
                })
        });
    let (Some((v, a)), Some((w, b))) = (plain_assignment(t_last), plain_assignment(o_last)) else {
        return false;
    };
    let value = match (a, b) {
        ("1", "0") => cond,
        ("0", "1") => invert_condition(&cond),
        _ => return false,
    };
    if !heads_hoist || v != w || indent_of(t_last) != pad + 2 || indent_of(o_last) != pad + 2 {
        return false;
    }
    let pad_s = " ".repeat(pad);
    let rewritten: Vec<String> = t_head
        .iter()
        .map(|l| format!("{pad_s}{}", l.trim()))
        .chain(std::iter::once(format!("{pad_s}{v} = {value};")))
        .collect();
    lines.splice(k..=close, rewritten);
    true
}

/// Rewrites the `if (a) { t = e; if (b) { B } }` at line `k` as `if (a &&
/// b) { B }`, with `e` put in for `t` in `b`.
///
/// A compiler lays out `a && b` and an `if` nested in an `if` alike, and a
/// value only the second test reads is loaded between the two tests either
/// way; read back, the load is a statement that splits the chain. Each
/// such statement assigns, without a call, a private variable
/// ([`private`]) read by a second test that calls nothing, so the value
/// cannot change between the two, and that no other line reads
/// or writes and that no other such statement's value reads, so writing
/// its value into the test in its place computes the same. With no such
/// statement the nesting is the structurer's own choice, and kept; so is
/// a second test that only reads such a value's truth, a computed flag
/// (the bit test a compiler makes of a `switch`) rather than a condition.
///
/// # Arguments
///
/// * `lines` - The body lines.
/// * `k` - The line of the outer `if`.
///
/// # Returns
///
/// Whether the two tests became one.
fn and_chain(lines: &mut Vec<String>, k: usize) -> bool {
    let Some((pad, a)) = lines
        .get(k)
        .and_then(|l| Some((indent_of(l), if_opener(l.trim())?.to_owned())))
    else {
        return false;
    };
    let Some(close) =
        loops::closing(lines, k, pad).filter(|&c| lines.get(c).is_some_and(|l| l.trim() == "}"))
    else {
        return false;
    };
    let Some(m) = (k + 1..close).find(|&j| {
        lines
            .get(j)
            .is_some_and(|l| !l.trim().is_empty() && plain_assignment(l).is_none())
    }) else {
        return false;
    };
    let Some(b) = lines
        .get(m)
        .filter(|l| indent_of(l) == pad + 2)
        .and_then(|l| if_opener(l.trim()))
        .map(str::to_owned)
    else {
        return false;
    };
    if loops::closing(lines, m, pad + 2) != Some(close - 1)
        || lines.get(close - 1).is_none_or(|l| l.trim() != "}")
    {
        return false;
    }
    let temps: Vec<(String, String)> = lines
        .get(k + 1..m)
        .unwrap_or(&[])
        .iter()
        .filter_map(|l| {
            plain_assignment(l)
                .filter(|(v, r)| {
                    indent_of(l) == pad + 2
                        && private(lines, v)
                        && (!impure(r)
                            || (*r == "__errno_location()" && word_positions(&b, v).len() == 1))
                })
                .map(|(v, r)| (v.to_owned(), r.to_owned()))
        })
        .collect();
    let truth_of_temp = temps.iter().any(|(v, _)| {
        [
            format!("{v} != 0"),
            format!("{v} == 0"),
            v.clone(),
            format!("!{v}"),
        ]
        .contains(&b)
    });
    if temps.is_empty() || temps.len() != m - k - 1 || truth_of_temp || impure(&b) {
        return false;
    }
    let only_here = temps.iter().all(|(v, _)| {
        mentions_ident(&b, v)
            && !mentions_ident(&a, v)
            && temps.iter().all(|(_, r)| !mentions_ident(r, v))
            && lines
                .iter()
                .enumerate()
                .filter(|&(j, l)| !(k < j && j <= m) && mentions_ident(l, v))
                .all(|(_, l)| declares(l))
    });
    if !only_here {
        return false;
    }
    let b = temps.iter().rev().fold(b, |b, (v, r)| {
        let simple = r == "__errno_location()"
            || r.chars()
                .all(|c| is_ident_char(c) || c == '-' || c == '>' || c == '.');
        rename_word(&b, v, &if simple { r.clone() } else { format!("({r})") })
    });
    let pad_s = " ".repeat(pad);
    let [ta, tb] = [&a, &b].map(|c| {
        if c.contains(" || ") || c.contains(" ? ") {
            format!("({c})")
        } else {
            c.clone()
        }
    });
    let head = format!("{pad_s}if ({ta} && {tb}) {{");
    let body = lines
        .get(m + 1..close - 1)
        .unwrap_or(&[])
        .iter()
        .map(|l| l.get(2..).unwrap_or(l.trim_start()).to_owned());
    let rewritten: Vec<String> = std::iter::once(head)
        .chain(body)
        .chain(std::iter::once(format!("{pad_s}}}")))
        .collect();
    lines.splice(k..=close, rewritten);
    true
}

/// Hoists a plain copy out of `if (c) { x = y; break; } x = y;` so the copy
/// runs once before `if (c) { break; }`.
///
/// # Arguments
///
/// * `lines` - The body lines.
/// * `k` - The line of the `if`.
///
/// # Returns
///
/// Whether the copy was hoisted.
fn hoist_break_copy(lines: &mut Vec<String>, k: usize) -> bool {
    let Some(open) = lines.get(k) else {
        return false;
    };
    let pad = indent_of(open);
    let Some(cond) = if_opener(open.trim()).map(str::to_owned) else {
        return false;
    };
    let Some((lhs, rhs)) = lines
        .get(k + 1)
        .filter(|l| indent_of(l) == pad + 2)
        .and_then(|l| plain_assignment(l))
        .map(|(a, b)| (a.to_owned(), b.to_owned()))
    else {
        return false;
    };
    let matches_tail = lines
        .get(k + 2)
        .is_some_and(|l| indent_of(l) == pad + 2 && l.trim() == "break;")
        && lines
            .get(k + 3)
            .is_some_and(|l| indent_of(l) == pad && l.trim() == "}")
        && lines
            .get(k + 4)
            .is_some_and(|l| indent_of(l) == pad && l.trim() == format!("{lhs} = {rhs};"));
    if !matches_tail
        || !is_ident(&lhs)
        || !is_ident(&rhs)
        || lhs == rhs
        || !private(lines, &lhs)
        || changes_state(&cond)
        || mentions_ident(&cond, &lhs)
    {
        return false;
    }
    let pad_s = " ".repeat(pad);
    let rewritten = [
        format!("{pad_s}{lhs} = {rhs};"),
        format!("{pad_s}if ({cond}) {{"),
        format!("{pad_s}  break;"),
        format!("{pad_s}}}"),
    ];
    lines.splice(k..=k + 4, rewritten);
    true
}

/// Drops a `return` at the end of an `if` block when the line right after
/// the `if` is the identical `return`.
///
/// # Arguments
///
/// * `lines` - The body lines.
/// * `k` - The line of the `if`.
///
/// # Returns
///
/// Whether the inner `return` was dropped.
fn redundant_if_return(lines: &mut Vec<String>, k: usize) -> bool {
    let Some(open) = lines.get(k) else {
        return false;
    };
    let pad = indent_of(open);
    if if_opener(open.trim()).is_none() {
        return false;
    }
    let Some(close) =
        loops::closing(lines, k, pad).filter(|&c| lines.get(c).is_some_and(|l| l.trim() == "}"))
    else {
        return false;
    };
    if close < k + 3 {
        return false;
    }
    let Some(ret) = lines
        .get(close - 1)
        .filter(|l| {
            indent_of(l) == pad + 2 && l.trim().starts_with("return ") && l.trim().ends_with(';')
        })
        .map(|l| l.trim().to_owned())
    else {
        return false;
    };
    let followed = lines
        .get(close + 1)
        .is_some_and(|l| indent_of(l) == pad && l.trim() == ret);
    let plain_prefix = lines.get(k + 1..close - 1).is_some_and(|s| {
        !s.is_empty()
            && s.iter().all(|l| {
                let t = l.trim();
                indent_of(l) == pad + 2
                    && !is_label(l)
                    && !transfers(t)
                    && !t.contains('{')
                    && !t.contains('}')
            })
    });
    if !followed || !plain_prefix {
        return false;
    }
    lines.remove(close - 1);
    true
}

/// Folds a default assignment `v = init;` before a multi-statement `if`
/// whose body ends by overwriting `v = other;` into the `else` arm.
///
/// # Arguments
///
/// * `lines` - The body lines.
/// * `k` - The line of the initial assignment.
///
/// # Returns
///
/// Whether the assignment moved into an `else` arm.
fn preassigned_if_else(lines: &mut Vec<String>, k: usize) -> bool {
    let (Some(init_line), Some(if_line)) = (lines.get(k), lines.get(k + 1)) else {
        return false;
    };
    let pad = indent_of(init_line);
    if indent_of(if_line) != pad {
        return false;
    }
    let Some((v, init)) = plain_assignment(init_line)
        .filter(|(_, r)| !impure(r) && plain_value(r))
        .map(|(a, b)| (a.to_owned(), b.to_owned()))
    else {
        return false;
    };
    let local_unaliased = private(lines, &v)
        || (lines
            .iter()
            .any(|l| declares(l) && !l.contains("//") && mentions_ident(l, &v))
            && !lines
                .iter()
                .any(|l| !l.trim_start().starts_with("//") && l.contains(&format!("&{v}"))));
    let Some(cond) = if_opener(if_line.trim()).map(str::to_owned) else {
        return false;
    };
    let Some(close) = loops::closing(lines, k + 1, pad)
        .filter(|&c| lines.get(c).is_some_and(|l| l.trim() == "}"))
    else {
        return false;
    };
    if !local_unaliased || close < k + 4 || changes_state(&cond) || mentions_ident(&cond, &v) {
        return false;
    }
    let Some((v2, other)) = lines
        .get(close - 1)
        .filter(|l| indent_of(l) == pad + 2)
        .and_then(|l| plain_assignment(l))
    else {
        return false;
    };
    let prefix_ok = v2 == v
        && !mentions_ident(other, &v)
        && lines.get(k + 2..close - 1).is_some_and(|s| {
            !s.is_empty()
                && s.iter().all(|l| {
                    let t = l.trim();
                    indent_of(l) == pad + 2
                        && !is_label(l)
                        && !transfers(t)
                        && !t.contains('{')
                        && !t.contains('}')
                        && !mentions_ident(t, &v)
                })
        });
    if !prefix_ok {
        return false;
    }
    let pad_s = " ".repeat(pad);
    let mut rewritten: Vec<String> = lines.get(k + 1..close).unwrap_or(&[]).to_vec();
    rewritten.push(format!("{pad_s}}} else {{"));
    rewritten.push(format!("{pad_s}  {v} = {init};"));
    rewritten.push(format!("{pad_s}}}"));
    lines.splice(k..=close, rewritten);
    true
}

/// Merges a cloned arm of a nested `if`/`else` back into a short-circuit
/// condition on the outer `if`.
///
/// # Arguments
///
/// * `lines` - The body lines.
/// * `k` - The line of the outer `if`.
///
/// # Returns
///
/// Whether a cloned arm was merged.
fn dup_merge(lines: &mut Vec<String>, k: usize) -> bool {
    let Some(open) = lines.get(k) else {
        return false;
    };
    let pad = indent_of(open);
    let Some(a) = if_opener(open.trim()).map(str::to_owned) else {
        return false;
    };
    let Some(mid) = loops::closing(lines, k, pad)
        .filter(|&m| lines.get(m).is_some_and(|l| l.trim() == "} else {"))
    else {
        return false;
    };
    let Some(close) =
        loops::closing(lines, mid, pad).filter(|&c| lines.get(c).is_some_and(|l| l.trim() == "}"))
    else {
        return false;
    };
    let pad_s = " ".repeat(pad);
    let dedent = |s: &[String]| -> Vec<String> {
        s.iter()
            .map(|l| l.strip_prefix("  ").unwrap_or(l).to_owned())
            .collect()
    };
    if let Some(b) = lines
        .get(k + 1)
        .filter(|l| indent_of(l) == pad + 2)
        .and_then(|l| if_opener(l.trim()))
        .map(str::to_owned)
    {
        let e = lines.get(mid + 1..close).unwrap_or(&[]);
        if loops::closing(lines, k + 1, pad + 2) == Some(mid - 1)
            && lines.get(mid - 1).is_some_and(|l| l.trim() == "}")
            && same_arm_lines(lines.get(k + 2..mid - 1).unwrap_or(&[]), e)
        {
            let mut out = vec![format!("{pad_s}if (!({a}) || ({b})) {{")];
            out.extend(e.iter().cloned());
            out.push(format!("{pad_s}}}"));
            lines.splice(k..=close, out);
            return true;
        }
        if let Some(im) = loops::closing(lines, k + 1, pad + 2)
            .filter(|&m| lines.get(m).is_some_and(|l| l.trim() == "} else {"))
            && loops::closing(lines, im, pad + 2) == Some(mid - 1)
            && lines.get(mid - 1).is_some_and(|l| l.trim() == "}")
        {
            let x = lines.get(k + 2..im).unwrap_or(&[]);
            let y = lines.get(im + 1..mid - 1).unwrap_or(&[]);
            if same_arm_lines(y, e) && !x.iter().any(|l| is_label(l)) {
                let mut out = vec![format!("{pad_s}if (({a}) && ({b})) {{")];
                out.extend(dedent(x));
                out.push(format!("{pad_s}}} else {{"));
                out.extend(e.iter().cloned());
                out.push(format!("{pad_s}}}"));
                lines.splice(k..=close, out);
                return true;
            }
        }
    }
    false
}

/// Tells whether two arm slices hold the exact same statements, one nested
/// two spaces deeper than the other, with no labels.
///
/// # Arguments
///
/// * `inner` - The arm of the inner `if`.
/// * `outer` - The arm of the outer `if`.
fn same_arm_lines(inner: &[String], outer: &[String]) -> bool {
    !inner.is_empty()
        && inner.len() == outer.len()
        && !inner.iter().any(|l| is_label(l))
        && inner
            .iter()
            .zip(outer)
            .all(|(i, o)| indent_of(i) == indent_of(o) + 2 && i.trim() == o.trim())
}

/// Rewrites `if (a) { x = p; } else { x = q; if (b) { x = p; } }` at line
/// `k` as `x = q; if (a || b) { x = p; }`.
///
/// A compiler lays that `||` out as the first test storing `p` and the
/// miss storing `q` before the second test stores `p` again. `x` is
/// private ([`unaliased`]), and `a`, `b`, `p` and `q` call nothing and do
/// not read `x`, so storing `q` on the way into the test changes no value
/// the test or `p` reads. `a`, `b`, `p` and `q` are plain values: no
/// memory operand and no address. `q` now runs when `a` is true, and the
/// store is visible to any later read of those bytes, including a test
/// that reaches them through another slot's address. A comment that names
/// `&x` is not a use of that address.
///
/// # Arguments
///
/// * `lines` - The body lines.
/// * `k` - The line of the outer `if`.
///
/// # Returns
///
/// Whether the two tests became one.
fn or_default(lines: &mut Vec<String>, k: usize) -> bool {
    let Some((pad, a, x, p, q, b)) = or_arms(lines, k) else {
        return false;
    };
    if !readable(&a, &x)
        || !readable(&b, &x)
        || !readable(&p, &x)
        || !readable(&q, &x)
        || !plain_value(&a)
        || !plain_value(&b)
        || !plain_value(&p)
        || !plain_value(&q)
    {
        return false;
    }
    let pad_s = " ".repeat(pad);
    let term = |c: &str| {
        if c.contains('?') {
            format!("({c})")
        } else {
            c.to_owned()
        }
    };
    let rewritten = [
        format!("{pad_s}{x} = {q};"),
        format!("{pad_s}if ({} || {}) {{", term(&a), term(&b)),
        format!("{pad_s}  {x} = {p};"),
        format!("{pad_s}}}"),
    ];
    let end = loops::closing(lines, k, pad).and_then(|mid| loops::closing(lines, mid, pad));
    let Some(end) = end else {
        return false;
    };
    lines.splice(k..=end, rewritten);
    true
}

/// The pieces of an `if (a) { x = p; } else { x = q; if (b) { x = p; } }`.
///
/// # Arguments
///
/// * `lines` - The body lines.
/// * `k` - The line of the outer `if`.
///
/// # Returns
///
/// The indentation, the two tests, the variable and the two values.
fn or_arms(lines: &[String], k: usize) -> Option<(usize, String, String, String, String, String)> {
    let open = lines.get(k)?;
    let pad = indent_of(open);
    let a = if_opener(open.trim())?.to_owned();
    let mid = loops::closing(lines, k, pad)
        .filter(|&m| lines.get(m).is_some_and(|l| l.trim() == "} else {"))?;
    let end = loops::closing(lines, mid, pad)
        .filter(|&c| lines.get(c).is_some_and(|l| l.trim() == "}"))?;
    let (x, p) = only_assign(lines, k + 1..mid, pad + 2)?;
    let inner = (mid + 1..end).find(|&j| {
        lines
            .get(j)
            .is_some_and(|l| !l.trim().is_empty() && !l.trim().starts_with("//"))
    })?;
    let stored = lines.get(inner)?;
    let (y, q) = plain_assignment(stored).filter(|_| indent_of(stored) == pad + 2)?;
    if y != x {
        return None;
    }
    let nxt = (inner + 1..end).find(|&j| {
        lines
            .get(j)
            .is_some_and(|l| !l.trim().is_empty() && !l.trim().starts_with("//"))
    })?;
    let b = lines
        .get(nxt)
        .filter(|l| indent_of(l) == pad + 2)
        .and_then(|l| if_opener(l.trim()))?
        .to_owned();
    if loops::closing(lines, nxt, pad + 2) != Some(end - 1) {
        return None;
    }
    let (z, p2) = only_assign(lines, nxt + 1..end - 1, pad + 4)?;
    if z != x || p2 != p || !unaliased(lines, &x) {
        return None;
    }
    Some((pad, a, x, p, q.to_owned(), b))
}

/// Tells whether `name` is a value only this function stores, ignoring
/// comments.
///
/// The same names as [`private`]. An escape note (`// note: &local_c
/// escapes`) names the frame's floor slot even when no statement takes
/// that address, and a comment is not a second reader of the store this
/// fold moves. A code line that contains `&name` still keeps the `if`.
///
/// # Arguments
///
/// * `lines` - The body lines.
/// * `name` - The assigned name.
fn unaliased(lines: &[String], name: &str) -> bool {
    let slot = name.starts_with("local_") || name.starts_with("home_");
    let needle = format!("&{name}");
    let taken = lines.iter().any(|l| {
        let t = l.trim_start();
        !t.starts_with("//") && l.contains(&needle)
    });
    vars::is_var_name(name) || is_register_name(name) || (slot && !taken)
}

/// Rewrites `if (c) { x = a; } else { x = b; }` at line `k`, when `a` and
/// `b` are names, as `x = c ? a : b;`.
///
/// The arms store nothing but a name, and `x` is private ([`private`]), so
/// the choice and the two `if` arms write the same name into `x`. The two
/// names must be declared with one type: a `?:` converts its arms to a
/// common type before the store, which is a different value when the arms
/// differ. A test that calls something, or an arm that is not one name,
/// stays an `if`: that is the shape a source wrote as a statement.
///
/// # Arguments
///
/// * `lines` - The body lines.
/// * `k` - The line of the `if`.
///
/// # Returns
///
/// Whether the `if` became a choice.
fn named_choice(lines: &mut Vec<String>, k: usize) -> bool {
    let Some(open) = lines.get(k) else {
        return false;
    };
    let pad = indent_of(open);
    let Some(cond) = if_opener(open.trim()) else {
        return false;
    };
    if cond.contains('?') || cond.contains(',') || impure(cond) {
        return false;
    }
    let Some(mid) = loops::closing(lines, k, pad)
        .filter(|&m| lines.get(m).is_some_and(|l| l.trim() == "} else {"))
    else {
        return false;
    };
    let Some(end) =
        loops::closing(lines, mid, pad).filter(|&c| lines.get(c).is_some_and(|l| l.trim() == "}"))
    else {
        return false;
    };
    let Some((x, a)) = only_assign(lines, k + 1..mid, pad + 2) else {
        return false;
    };
    let Some((y, b)) = only_assign(lines, mid + 1..end, pad + 2) else {
        return false;
    };
    let name =
        |w: &str| w.starts_with(|c: char| c.is_ascii_alphabetic() || c == '_') && is_ident(w);
    let same_type =
        decl_type(lines, &a).is_some_and(|ta| decl_type(lines, &b).as_ref() == Some(&ta));
    if x != y
        || !name(&a)
        || !name(&b)
        || a == b
        || a == x
        || b == x
        || !same_type
        || !private(lines, &x)
        || mentions_ident(cond, &x)
    {
        return false;
    }
    let pad_s = " ".repeat(pad);
    lines.splice(k..=end, [format!("{pad_s}{x} = {cond} ? {a} : {b};")]);
    true
}

/// The one assignment at indentation `pad` in `span`, when the span holds
/// nothing else.
///
/// # Arguments
///
/// * `lines` - The body lines.
/// * `span` - The lines inside one arm.
/// * `pad` - The indentation of that arm.
///
/// # Returns
///
/// The variable and the value, or `None` when the arm is not one assignment.
fn only_assign(
    lines: &[String],
    span: std::ops::Range<usize>,
    pad: usize,
) -> Option<(String, String)> {
    let mut found = None;
    for line in lines.get(span)? {
        if line.trim().is_empty() || line.trim().starts_with("//") {
            continue;
        }
        let (v, r) = plain_assignment(line).filter(|_| indent_of(line) == pad)?;
        if found.is_some() {
            return None;
        }
        found = Some((v.to_owned(), r.to_owned()));
    }
    found
}

/// The declared type of `name`, from a local line or a parameter.
///
/// `FILE *stdout` and `uint64_t var1, var2` both yield the type in front
/// of the name. A `// signature:` line is read too, because a parameter
/// often has no local declaration of its own. A list that puts a star on
/// a later name is skipped, and so is a name with no declaration: the
/// choice then stays an `if`. Two declarations that disagree also stay
/// an `if`.
///
/// # Arguments
///
/// * `lines` - The function text.
/// * `name` - The stored name.
///
/// # Returns
///
/// The type text, or `None` when no single declaration names it.
fn decl_type(lines: &[String], name: &str) -> Option<String> {
    let mut found = None;
    for line in lines {
        let trimmed = line.trim();
        let raw = trimmed.strip_prefix("// signature:").map_or_else(
            || trimmed.split("//").next().unwrap_or("").trim(),
            str::trim,
        );
        if let Some(ty) = decl_type_on(raw, name) {
            if found.as_ref().is_some_and(|got| got != &ty) {
                return None;
            }
            found = Some(ty);
        }
    }
    found
}

/// The type `raw` gives `name`, when `raw` is one declaration or the body
/// of one signature.
///
/// # Arguments
///
/// * `raw` - One line. A comment is already removed, and a signature is
///   the text after `// signature:`.
/// * `name` - The name to look up.
///
/// # Returns
///
/// The type text, or `None` when this line does not declare `name`.
fn decl_type_on(raw: &str, name: &str) -> Option<String> {
    let sig = raw.trim();
    if let (Some(open), Some(close)) = (sig.find('('), sig.rfind(')'))
        && close > open
    {
        for param in sig[open + 1..close].split(',') {
            if let Some(ty) = declarator_type(param.trim(), name) {
                return Some(ty);
            }
        }
        return None;
    }
    if !sig.ends_with(';') || sig.contains('=') || sig.contains('(') {
        return None;
    }
    let body = sig.trim_end_matches(';').trim();
    if body.contains(',') {
        let mut parts = body.split(',');
        let first = parts.next().unwrap_or("");
        let ty = declarator_type(first.trim(), name);
        let base = first.trim().rsplit_once(' ').map(|(h, _)| h.trim())?;
        if !base.is_empty() && !base.contains('*') {
            for extra in parts {
                if extra.trim() == name {
                    return Some(norm_ty(base));
                }
            }
        }
        return ty;
    }
    declarator_type(body, name)
}

/// The type in one declarator, when its last word is `name`.
///
/// # Arguments
///
/// * `piece` - One declarator, such as `FILE *stdout` or `int32_t a1`.
/// * `name` - The name that must end the piece.
///
/// # Returns
///
/// The type text, or `None` when the piece does not end in `name`.
fn declarator_type(piece: &str, name: &str) -> Option<String> {
    let piece = piece.trim();
    let name_at = piece
        .rfind(|c: char| !is_ident_char(c))
        .map_or(0, |i| i + 1);
    if piece.get(name_at..)? != name {
        return None;
    }
    let ty = norm_ty(piece[..name_at].trim());
    (!ty.is_empty()).then_some(ty)
}

/// Collapses whitespace and the space before `*` so `FILE*`, `FILE *` and
/// `FILE  *` match.
///
/// # Arguments
///
/// * `ty` - The type text.
///
/// # Returns
///
/// The type with one space between words and before every `*`.
fn norm_ty(ty: &str) -> String {
    ty.split_whitespace()
        .collect::<Vec<_>>()
        .join(" ")
        .replace('*', " *")
        .split_whitespace()
        .collect::<Vec<_>>()
        .join(" ")
}

/// A temporary that chooses a value or that value with one bit set or
/// cleared, under the opposite comparison, is the `if` a source writes.
///
/// `r = (c != k ? (c == k ? base & ~bit : base) | bit : (c == k ? base &
/// ~bit : base)); base = r;` is `if (c != k) { base |= bit; } else { base
/// &= ~bit; }`. The mask may sit on the outside instead, `(c != k ? (c ==
/// k ? base | bits : base) & ~bits : ...)`, which tests the other way. The
/// temporary is dropped when no other line reads it.
///
/// # Arguments
///
/// * `lines` - The function.
/// * `k` - Index of the temporary's assignment.
///
/// # Returns
///
/// Whether the two lines were replaced.
fn complement_bits(lines: &mut Vec<String>, k: usize) -> bool {
    let Some(line) = lines.get(k) else {
        return false;
    };
    if line.trim_start().starts_with("//") {
        return false;
    }
    let Some((temp, rhs)) = plain_assignment(line) else {
        return false;
    };
    let (cond, yes, no) = ternary(rhs).unwrap_or(("", "", ""));
    let Some((or_out, extra, inner)) = outer_update(yes, no) else {
        return false;
    };
    let Some((q, arm_a, arm_b)) = ternary(inner) else {
        return false;
    };
    if invert_condition(cond) != q || changes_state(cond) {
        return false;
    }
    let Some((base, operand, inner_or)) = applied_arm(arm_a, arm_b) else {
        return false;
    };
    let Some(store) = lines.get(k + 1).and_then(|l| any_assignment(l)) else {
        return false;
    };
    if store.1 != temp || store.0 != base {
        return false;
    }
    let (then_op, else_op, else_operand) = match (or_out, inner_or) {
        (true, false) if complements(extra, operand) => ("|=", "&=", operand),
        (false, true) if masked_not(extra, operand) => ("&=", "|=", operand),
        _ => return false,
    };
    let Some(ty) = decl_type(lines, temp).filter(|t| integer_type(t)) else {
        return false;
    };
    if temp_lives(lines, k, temp)
        || base.contains('?')
        || mentions_ident(base, temp)
        || address_taken(lines, temp)
    {
        return false;
    }
    let pad = " ".repeat(indent_of(line));
    let body = format!("{pad}  ");
    let then_s = cast_update(&ty, base, then_op, extra);
    let else_s = cast_update(&ty, base, else_op, else_operand);
    let rewritten = vec![
        format!("{pad}if ({cond}) {{"),
        format!("{body}{then_s}"),
        format!("{pad}}} else {{"),
        format!("{body}{else_s}"),
        format!("{pad}}}"),
    ];
    lines.splice(k..=k + 1, rewritten);
    true
}

/// The outer update of a complementary select: the inner choice, whether
/// the true side applies `|`, and the operand it applies.
///
/// # Arguments
///
/// * `yes` - The true side of the outer choice.
/// * `no` - The false side, which is the inner choice.
fn outer_update<'a>(yes: &'a str, no: &'a str) -> Option<(bool, &'a str, &'a str)> {
    if yes.is_empty() {
        return None;
    }
    let bare = unparen(no);
    for (op, is_or) in [(" | ", true), (" & ", false)] {
        let Some((left, right)) = split_last_op(yes, op) else {
            continue;
        };
        if unparen(left) == bare {
            return Some((is_or, right, no));
        }
    }
    None
}

/// The plain base and the bit operand when one arm is the other with `|`
/// or `&` applied.
///
/// # Arguments
///
/// * `arm_a` - The true side of the inner choice.
/// * `arm_b` - The false side.
///
/// # Returns
///
/// The base, the operand, and whether the true side is the updated one
/// with `|` rather than `&`.
fn applied_arm<'a>(arm_a: &'a str, arm_b: &'a str) -> Option<(&'a str, &'a str, bool)> {
    let base = unparen(arm_b);
    let (operand, is_or) = applied(arm_a, base)?;
    Some((base, operand, is_or))
}

/// `base OP operand` when `expr` is that update of `base`.
///
/// # Arguments
///
/// * `expr` - One arm.
/// * `base` - The plain value.
///
/// # Returns
///
/// The operand and whether the operator is `|`.
fn applied<'a>(expr: &'a str, base: &str) -> Option<(&'a str, bool)> {
    for (op, is_or) in [(" | ", true), (" & ", false)] {
        if let Some((left, right)) = split_last_op(expr, op)
            && unparen(left) == base
        {
            return Some((right, is_or));
        }
    }
    None
}

/// Tells whether two constants are complements in 32 bits.
///
/// # Arguments
///
/// * `bit` - The bits the true side sets.
/// * `mask` - The mask the false side keeps.
fn complements(bit: &str, mask: &str) -> bool {
    let Some(bit) = parse_const(bit) else {
        return false;
    };
    let Some(mask) = parse_const(mask) else {
        return false;
    };
    bit <= 0xffff_ffff && mask <= 0xffff_ffff && bit ^ mask == 0xffff_ffff
}

/// Tells whether `mask` is `bits` inverted in 32 bits, as `bits ^ 0xffffffff`.
///
/// # Arguments
///
/// * `mask` - The mask text.
/// * `bits` - The bits the other side sets.
fn masked_not(mask: &str, bits: &str) -> bool {
    let mask = unparen(mask);
    mask == format!("{bits} ^ 0xffffffff")
}

/// Strips one matching pair of parentheses, repeatedly.
///
/// # Arguments
///
/// * `expr` - An expression.
fn unparen(expr: &str) -> &str {
    let mut e = expr.trim();
    while let Some(inner) = e.strip_prefix('(').and_then(|r| r.strip_suffix(')')) {
        if opening_paren(e, e.len() - 1) != Some(0) {
            break;
        }
        e = inner.trim();
    }
    e
}

/// The rightmost `op` at bracket depth zero.
///
/// # Arguments
///
/// * `expr` - An expression.
/// * `op` - The operator with its spaces, ` | ` or ` & `.
fn split_last_op<'a>(expr: &'a str, op: &str) -> Option<(&'a str, &'a str)> {
    let mut depth = 0i32;
    let mut quote: Option<char> = None;
    let mut escaped = false;
    let mut found: Option<usize> = None;
    for (i, c) in expr.char_indices() {
        if let Some(q) = quote {
            match c {
                _ if escaped => escaped = false,
                '\\' => escaped = true,
                _ if c == q => quote = None,
                _ => {}
            }
            continue;
        }
        match c {
            '"' | '\'' => quote = Some(c),
            '(' | '[' => depth += 1,
            ')' | ']' => depth -= 1,
            _ if depth == 0 && expr.get(i..).is_some_and(|r| r.starts_with(op)) => found = Some(i),
            _ => {}
        }
    }
    let at = found?;
    Some((expr.get(..at)?.trim(), expr.get(at + op.len()..)?.trim()))
}

/// An assignment whose left side may be a field, not only a name.
///
/// # Arguments
///
/// * `line` - One line.
fn any_assignment(line: &str) -> Option<(&str, &str)> {
    let t = line.trim().strip_suffix(';')?;
    let (left, right) = t.split_once(" = ")?;
    if left.contains('=') || right.contains(" = ") {
        return None;
    }
    Some((left.trim(), right.trim()))
}

/// Tells whether some line has taken the address of a stack slot.
///
/// A later read can use the saved pointer and never write the slot's name.
///
/// # Arguments
///
/// * `lines` - The function.
/// * `name` - The temporary.
fn address_taken(lines: &[String], name: &str) -> bool {
    (name.starts_with("local_") || name.starts_with("home_"))
        && lines.iter().any(|l| l.contains(&format!("&{name}")))
}

/// Tells whether line `k` sits in a `while`, `for` or `do`.
///
/// The next iteration can read a temporary the lines after this one never
/// name. Dropping its assignment would change that read.
///
/// # Arguments
///
/// * `lines` - The function.
/// * `k` - The line to place.
fn inside_loop(lines: &[String], k: usize) -> bool {
    let mut depth = 0i32;
    let mut loops: Vec<(i32, bool)> = Vec::new();
    for (i, line) in lines.iter().enumerate().take(k + 1) {
        if line.trim_start().starts_with("//") {
            continue;
        }
        if loop_header(line) {
            loops.push((depth, false));
        }
        let next = depth + brace_delta(line);
        for lp in &mut loops {
            if next > lp.0 {
                lp.1 = true;
            }
        }
        depth = next;
        if i == k {
            break;
        }
        loops.retain(|lp| depth > lp.0 || !lp.1);
    }
    !loops.is_empty()
}

/// Tells whether a line opens a loop.
///
/// # Arguments
///
/// * `line` - One line.
fn loop_header(line: &str) -> bool {
    let t = line.trim_start();
    ["while", "for", "do"].iter().any(|word| {
        t.strip_prefix(word)
            .is_some_and(|rest| rest.is_empty() || rest.starts_with(|c: char| !is_ident_char(c)))
    })
}

/// How many braces a line opens minus how many it closes.
///
/// Braces inside a string do not count.
///
/// # Arguments
///
/// * `line` - One line.
fn brace_delta(line: &str) -> i32 {
    let mut depth = 0i32;
    let mut quote: Option<char> = None;
    let mut escaped = false;
    for c in line.chars() {
        if let Some(q) = quote {
            match c {
                _ if escaped => escaped = false,
                '\\' => escaped = true,
                _ if c == q => quote = None,
                _ => {}
            }
            continue;
        }
        match c {
            '"' | '\'' => quote = Some(c),
            '{' => depth += 1,
            '}' => depth -= 1,
            _ => {}
        }
    }
    depth
}

/// Tells whether evaluating `expr` can change state.
///
/// A call runs twice in the nested choice and once in the `if`. An
/// increment does the same.
///
/// # Arguments
///
/// * `expr` - A condition.
fn changes_state(expr: &str) -> bool {
    impure(expr) || expr.contains("++") || expr.contains("--")
}

/// Tells whether `ty` is an integer a bit update can be stored as.
///
/// # Arguments
///
/// * `ty` - A declared type.
fn integer_type(ty: &str) -> bool {
    matches!(
        ty,
        "bool"
            | "char"
            | "signed char"
            | "unsigned char"
            | "int8_t"
            | "uint8_t"
            | "short"
            | "unsigned short"
            | "int16_t"
            | "uint16_t"
            | "int"
            | "unsigned"
            | "unsigned int"
            | "long"
            | "unsigned long"
            | "int32_t"
            | "uint32_t"
            | "long long"
            | "unsigned long long"
            | "int64_t"
            | "uint64_t"
    )
}

/// One store that keeps the conversion the temporary's type applied.
///
/// `uint32_t r = base | bit; base = r` clears bits above 32. `base |= bit`
/// keeps them.
///
/// # Arguments
///
/// * `ty` - The temporary's type.
/// * `base` - The stored location.
/// * `op` - `|=` or `&=`.
/// * `operand` - The bit or the mask.
fn cast_update(ty: &str, base: &str, op: &str, operand: &str) -> String {
    let bin = if op == "|=" { "|" } else { "&" };
    format!("{base} = ({ty})({base} {bin} {operand});")
}

/// Tells whether a line after the store reads `temp` before a replacement
/// that every later path executes.
///
/// An assignment inside a brace does not count. `if (a3) { r3 = a4; }`
/// leaves `r3` holding the earlier value when `a3` is false. A line
/// inside a loop counts too: the next iteration can read the temporary
/// from above this assignment.
///
/// # Arguments
///
/// * `lines` - The function.
/// * `k` - Index of the temporary's assignment. The next line is its store.
/// * `temp` - The temporary.
fn temp_lives(lines: &[String], k: usize, temp: &str) -> bool {
    if inside_loop(lines, k) {
        return true;
    }
    let mut depth = 0i32;
    for line in lines.iter().skip(k + 2) {
        if line.trim_start().starts_with("//") {
            continue;
        }
        if depth == 0
            && let Some((lhs, rhs)) = plain_assignment(line)
            && lhs == temp
            && !mentions_ident(rhs, temp)
        {
            return false;
        }
        if mentions_ident(line, temp) {
            return true;
        }
        depth += brace_delta(line);
    }
    false
}

/// Tells whether an expression calls nothing and does not read `var`.
///
/// # Arguments
///
/// * `expr` - The expression.
/// * `var` - The variable the rewrite stores early.
fn readable(expr: &str, var: &str) -> bool {
    !impure(expr) && !expr.contains('?') && !mentions_ident(expr, var)
}

/// Tells whether `expr` is a value the early default store cannot change
/// and that cannot fault when moved ahead of its test.
///
/// A memory operand or an address can name the same bytes as the slot the
/// fold stores, through another local. A plain value cannot.
///
/// # Arguments
///
/// * `expr` - One test or one stored value.
fn plain_value(expr: &str) -> bool {
    !expr.contains('*') && !expr.contains('[') && !expr.contains('&') && !expr.contains("->")
}

/// Tells whether a line only declares names: a type and a list, no value,
/// call or jump.
///
/// # Arguments
///
/// * `line` - One line.
fn declares(line: &str) -> bool {
    let t = line.trim();
    t.ends_with(';')
        && t.contains(' ')
        && !t.contains('=')
        && !t.contains('(')
        && !["return", "goto ", "break", "continue"]
            .iter()
            .any(|w| t.starts_with(w))
}

/// Tells whether a name is a value only this function's text holds.
///
/// That is a numbered variable, a register, or a stack slot whose address
/// no line takes. A global, a parameter or a slot something points at is
/// storage another reader may see, so a rewrite that moves or drops a
/// store to it can change what that reader sees.
///
/// # Arguments
///
/// * `lines` - The body lines.
/// * `name` - The assigned name.
fn private(lines: &[String], name: &str) -> bool {
    let slot = name.starts_with("local_") || name.starts_with("home_");
    vars::is_var_name(name)
        || is_register_name(name)
        || (slot && !lines.iter().any(|l| l.contains(&format!("&{name}"))))
}

#[cfg(test)]
#[expect(
    clippy::missing_panics_doc,
    reason = "assertions are the point of a test"
)]
mod tests {
    //! The rewrites on hand-written text, each beside a case that keeps its
    //! form.

    use super::select_statements;

    /// A conditional move that keeps its variable on one side is an `if`;
    /// one that picks between two other values stays a choice.
    #[test]
    fn a_kept_select_is_an_if() {
        assert_eq!(
            select_statements("  var2 = var3 == 0 ? 0 : var2;\n"),
            "  if (var3 == 0) {\n    var2 = 0;\n  }\n"
        );
        assert_eq!(
            select_statements("x = (a1 < 2 ? x : 2);\n"),
            "if (a1 >= 2) {\n  x = 2;\n}\n"
        );
        assert_eq!(
            select_statements("x = (a1 == 0 ? 0 : x) & 0xffffffff;\n"),
            "if (a1 == 0) {\n  x = 0;\n}\nx = x & 0xffffffff;\n"
        );
        let picked = "x = a1 < 2 ? a2 : 2;\n";
        assert_eq!(select_statements(picked), picked);
        let nested = "x = (a1 < 2 ? 1 : 2) + x;\n";
        assert_eq!(select_statements(nested), nested);
    }

    /// A clamp of a variable read only there is the `if` before its use;
    /// read again later, or inside a loop, it stays a choice.
    #[test]
    fn a_clamp_before_its_one_use_is_an_if() {
        let text =
            "uint32_t arg_0, r3;\n\nr3 = a1 | ((arg_0 < 2 ? 2 : arg_0) << 0x1c);\nreturn r3;\n";
        assert_eq!(
            select_statements(text),
            "uint32_t arg_0, r3;\n\nif (arg_0 < 2) {\n  arg_0 = 2;\n}\nr3 = a1 | (arg_0 << 0x1c);\nreturn r3;\n"
        );
        let read = text.replace("return r3;", "return r3 + arg_0;");
        assert_eq!(select_statements(&read), read);
        let looped = "uint32_t arg_0, r3;\n\nwhile (a1 != 0) {\n  r3 = a1 | ((a2 < 2 ? 2 : arg_0) << 0x1c);\n}\nreturn r3;\n";
        assert_eq!(select_statements(looped), looped);
    }

    /// An `if` nested alone in an `if`, behind values only its test reads,
    /// is one test; a value read after it keeps the two apart.
    #[test]
    fn nested_tests_are_one_chain() {
        let text = "uint64_t var2, rbx;\n\nif (sub_1(rbx) == 0) {\n  var2 = rbx->field_0x0;\n  if (*(uint8_t*)(var2 + 8) == 61) {\n    sub_2(rbx);\n  }\n}\nreturn 0;\n";
        assert_eq!(
            select_statements(text),
            "uint64_t var2, rbx;\n\nif (sub_1(rbx) == 0 && *(uint8_t*)(rbx->field_0x0 + 8) == 61) {\n  sub_2(rbx);\n}\nreturn 0;\n"
        );
        let read = text.replace("return 0;", "return var2;");
        assert_eq!(select_statements(&read), read);
        let flag = text.replace("*(uint8_t*)(var2 + 8) == 61", "var2 != 0");
        assert_eq!(select_statements(&flag), flag);
    }

    /// A byte-wide flag compared with zero in a chain is the flag; a wider
    /// value, or a flag outside a chain, keeps its comparison.
    #[test]
    fn flags_in_a_chain_are_bare() {
        let text = "uint8_t local_11;\nuint64_t rax;\n\nwhile (rax != 0 && local_11 != 0) {\n  rax = sub_1(rax);\n}\nif (g8_71f3 == 0 || (local_11 != 0)) {\n  return local_11 != 0;\n}\nreturn 0;\n";
        assert_eq!(
            select_statements(text),
            "uint8_t local_11;\nuint64_t rax;\n\nwhile (rax != 0 && local_11) {\n  rax = sub_1(rax);\n}\nif (!g8_71f3 || (local_11 != 0)) {\n  return local_11 != 0;\n}\nreturn 0;\n"
        );
    }

    /// Arms that store `1` and `0` behind a short-circuit test are the
    /// test's truth value, after the statements both arms open with; behind
    /// one comparison they stay an `if`.
    #[test]
    fn a_truth_diamond_is_a_truth_value() {
        let text = "if (a2 <= a1 || *(uint8_t*)(a2 - 1) != 10) {\n  local_18 = var1;\n  var1 = 0;\n} else {\n  local_18 = var1;\n  var1 = 1;\n}\nreturn var1;\n";
        assert_eq!(
            select_statements(text),
            "local_18 = var1;\nvar1 = a2 > a1 && *(uint8_t*)(a2 - 1) == 10;\nreturn var1;\n"
        );
        let lone = "if (a2 <= a1) {\n  var1 = 0;\n} else {\n  var1 = 1;\n}\nreturn var1;\n";
        assert_eq!(select_statements(lone), lone);
        let read = text.replace("local_18 = var1;", "a1 = var1;");
        assert_eq!(select_statements(&read), read);
        let global = text.replace("local_18 = var1;", "g32_1000 = 1;");
        assert_eq!(select_statements(&global), global);
        let quoted = "uint8_t g8_1000;

puts(\"a && g8_1000 == 0 || b\");
return 0;
";
        assert_eq!(select_statements(quoted), quoted);
        let pointed = format!(
            "sub_9(&local_18);
{text}"
        );
        assert_eq!(select_statements(&pointed), pointed);
    }

    /// A store to a global between two tests stays a store: another
    /// function may read it, so it is no temporary to fold into the test.
    #[test]
    fn a_global_store_between_tests_stays() {
        let text = "if (a1 != 0) {
  g32_1000 = *(uint32_t*)a2;
  if (g32_1000 == 61) {
    sub_2();
  }
}
return 0;
";
        assert_eq!(select_statements(text), text);
        let called = "uint32_t var1;

if (a2 != 0) {
  var1 = *(uint32_t*)a1;
  if (sub_3(a1) == var1) {
    sub_2();
  }
}
return 0;
";
        assert_eq!(select_statements(called), called);
    }

    /// An `else` that stores a default and then the first arm's value under
    /// a second test is one `||`. A call in that default stays two tests,
    /// because the call would then run when the first test is true.
    #[test]
    fn an_or_of_two_stores_is_one_test() {
        let text = "uint32_t local_c;\n\nif (a1 == 0x40011000) {\n  local_c = g32_20000004;\n} else {\n  local_c = g32_20000000;\n  if (a1 == 0x40011400) {\n    local_c = g32_20000004;\n  }\n}\n*(uint32_t*)(a1 + 8) = local_c;\n";
        assert_eq!(
            select_statements(text),
            "uint32_t local_c;\n\nlocal_c = g32_20000000;\nif (a1 == 0x40011000 || a1 == 0x40011400) {\n  local_c = g32_20000004;\n}\n*(uint32_t*)(a1 + 8) = local_c;\n"
        );
        let called = text.replace("local_c = g32_20000000;", "local_c = sub_1();");
        assert_eq!(select_statements(&called), called);
        let global = text.replace("local_c", "g32_10");
        assert_eq!(select_statements(&global), global);
        let noted = format!(
            "// note: &local_c escapes; locals from there up are reloaded after calls\n{text}"
        );
        let noted_out = format!(
            "// note: &local_c escapes; locals from there up are reloaded after calls\n{}",
            select_statements(text)
        );
        assert_eq!(select_statements(&noted), noted_out);
        let aliased = text.replace("uint32_t local_c;", "uint32_t local_c;\nsub_9(&local_c);");
        assert_eq!(select_statements(&aliased), aliased);
        let guarded = "uint32_t local_c;\n\nif (a1 == 0) {\n  local_c = 1;\n} else {\n  local_c = *(uint32_t*)a1;\n  if (a2 != 0) {\n    local_c = 1;\n  }\n}\nreturn local_c;\n";
        assert_eq!(select_statements(guarded), guarded);
        let alias = "uint32_t local_c;\nuint32_t local_58;\n\nif (((uint32_t*)&local_58)[a1] == 1) {\n  local_c = 2;\n} else {\n  local_c = 0;\n  if (a2 != 0) {\n    local_c = 2;\n  }\n}\nreturn local_c;\n";
        assert_eq!(select_statements(alias), alias);
    }

    /// Arms that store two different names of one type are a choice. An arm
    /// that computes a value, or two names of different types, stays an
    /// `if`, which is the statement a source wrote.
    #[test]
    fn two_names_in_an_if_are_a_choice() {
        let text = "uint64_t var1;\nFILE *stdout; // @ 0x7160\nFILE *stderr; // @ 0x71a0\n\nif (a1 == 0) {\n  var1 = stdout;\n} else {\n  var1 = stderr;\n}\nfprintf(var1, s);\n";
        assert_eq!(
            select_statements(text),
            "uint64_t var1;\nFILE *stdout; // @ 0x7160\nFILE *stderr; // @ 0x71a0\n\nvar1 = a1 == 0 ? stdout : stderr;\nfprintf(var1, s);\n"
        );
        let mixed = "uint64_t var1;\nint32_t narrow;\nuint32_t wide;\n\nif (c) {\n  var1 = narrow;\n} else {\n  var1 = wide;\n}\nreturn var1;\n";
        assert_eq!(select_statements(mixed), mixed);
        let mixed_sig = "// signature: void f(int32_t narrow, uint32_t wide)\nuint64_t var1;\n\nif (c) {\n  var1 = narrow;\n} else {\n  var1 = wide;\n}\nreturn var1;\n";
        assert_eq!(select_statements(mixed_sig), mixed_sig);
        let same_sig = "// signature: void f(FILE* stdout, FILE *stderr)\nuint64_t var1;\n\nif (a1 == 0) {\n  var1 = stdout;\n} else {\n  var1 = stderr;\n}\nreturn var1;\n";
        assert_eq!(
            select_statements(same_sig),
            "// signature: void f(FILE* stdout, FILE *stderr)\nuint64_t var1;\n\nvar1 = a1 == 0 ? stdout : stderr;\nreturn var1;\n"
        );
        let bare = "\nif (a1 == 0) {\n  var1 = stdout;\n} else {\n  var1 = stderr;\n}\n";
        assert_eq!(select_statements(bare), bare);
        let expr = "uint32_t r1;\n\nif (a1 == 0) {\n  r1 = a1 + a2;\n} else {\n  r1 = a1 + a3;\n}\nreturn r1;\n";
        assert_eq!(select_statements(expr), expr);
    }

    /// A select between a field and that field with one bit updated, under
    /// the opposite comparison, is the `if` of the bit. A later read of the
    /// temporary keeps the select.
    #[test]
    fn a_complementary_bit_is_an_if() {
        let text = "uint32_t r3;\n\nr3 = (a2 != 8 ? (a2 == 8 ? a1->field_0xc & 0xffffefff : a1->field_0xc) | 0x1000 : (a2 == 8 ? a1->field_0xc & 0xffffefff : a1->field_0xc));\na1->field_0xc = r3;\n";
        assert_eq!(
            select_statements(text),
            "uint32_t r3;\n\nif (a2 != 8) {\n  a1->field_0xc = (uint32_t)(a1->field_0xc | 0x1000);\n} else {\n  a1->field_0xc = (uint32_t)(a1->field_0xc & 0xffffefff);\n}\n"
        );
        let clear = "uint32_t r1;\n\nr1 = (a2 != 1 ? (a2 == 1 ? a1->field_0x4 | a4 : a1->field_0x4) & (a4 ^ 0xffffffff) : (a2 == 1 ? a1->field_0x4 | a4 : a1->field_0x4));\na1->field_0x4 = r1;\nr1 = 0;\n";
        assert_eq!(
            select_statements(clear),
            "uint32_t r1;\n\nif (a2 != 1) {\n  a1->field_0x4 = (uint32_t)(a1->field_0x4 & (a4 ^ 0xffffffff));\n} else {\n  a1->field_0x4 = (uint32_t)(a1->field_0x4 | a4);\n}\nr1 = 0;\n"
        );
        let live = "uint32_t r3;\n\nr3 = (a2 != 8 ? (a2 == 8 ? a1->field_0xc & 0xffffefff : a1->field_0xc) | 0x1000 : (a2 == 8 ? a1->field_0xc & 0xffffefff : a1->field_0xc));\na1->field_0xc = r3;\nreturn r3;\n";
        assert_eq!(select_statements(live), live);
        let branched = "uint32_t r3;\n\nr3 = (a2 != 8 ? (a2 == 8 ? a1->field_0xc & 0xffffefff : a1->field_0xc) | 0x1000 : (a2 == 8 ? a1->field_0xc & 0xffffefff : a1->field_0xc));\na1->field_0xc = r3;\nif (a3) {\n  r3 = a4;\n}\nreturn r3;\n";
        assert_eq!(select_statements(branched), branched);
        let called = "uint32_t r3;\n\nr3 = (next() != 8 ? (next() == 8 ? a1->field_0xc & 0xffffefff : a1->field_0xc) | 0x1000 : (next() == 8 ? a1->field_0xc & 0xffffefff : a1->field_0xc));\na1->field_0xc = r3;\n";
        assert_eq!(select_statements(called), called);
        let spun = "uint32_t r3;\n\nwhile (a3) {\n  consume(r3);\n  r3 = (a2 != 8 ? (a2 == 8 ? a1->field_0xc & 0xffffefff : a1->field_0xc) | 0x1000 : (a2 == 8 ? a1->field_0xc & 0xffffefff : a1->field_0xc));\n  a1->field_0xc = r3;\n}\n";
        assert_eq!(select_statements(spun), spun);
        let indexed = "uint32_t r3;\n\nr3 = (a2 != 8 ? (a2 == 8 ? table[r3] & 0xffffefff : table[r3]) | 0x1000 : (a2 == 8 ? table[r3] & 0xffffefff : table[r3]));\ntable[r3] = r3;\n";
        assert_eq!(select_statements(indexed), indexed);
        let escaped = "uint32_t local_c;\n\nescape(&local_c);\nlocal_c = (a2 != 8 ? (a2 == 8 ? a1->field_0xc & 0xffffefff : a1->field_0xc) | 0x1000 : (a2 == 8 ? a1->field_0xc & 0xffffefff : a1->field_0xc));\na1->field_0xc = local_c;\n";
        assert_eq!(select_statements(escaped), escaped);
        let wide = "uint64_t r3;\n\nr3 = (a2 != 8 ? (a2 == 8 ? a1->field_0xc & 0xffffefff : a1->field_0xc) | 0x1000 : (a2 == 8 ? a1->field_0xc & 0xffffefff : a1->field_0xc));\na1->field_0xc = r3;\n";
        assert_eq!(
            select_statements(wide),
            "uint64_t r3;\n\nif (a2 != 8) {\n  a1->field_0xc = (uint64_t)(a1->field_0xc | 0x1000);\n} else {\n  a1->field_0xc = (uint64_t)(a1->field_0xc & 0xffffefff);\n}\n"
        );
    }

    /// Break copies, redundant return guards, preassigned `if`/`else` stores,
    /// and duplicated `else` arms fold into their single-statement forms.
    #[test]
    fn break_copies_and_split_branches_fold() {
        let break_copy = "if (a1 == 0) {\n  var1 = a2;\n  break;\n}\nvar1 = a2;\n";
        assert_eq!(
            select_statements(break_copy),
            "var1 = a2;\nif (a1 == 0) {\n  break;\n}\n"
        );
        let red_ret = "if (a1 != 0) {\n  sub_1(a1);\n  return 0;\n}\nreturn 0;\n";
        assert_eq!(
            select_statements(red_ret),
            "if (a1 != 0) {\n  sub_1(a1);\n}\nreturn 0;\n"
        );
        let pre_if = "var1 = 0;\nif (a1 != 0) {\n  sub_1(a1);\n  var1 = a2;\n}\nreturn var1;\n";
        assert_eq!(
            select_statements(pre_if),
            "if (a1 != 0) {\n  sub_1(a1);\n  var1 = a2;\n} else {\n  var1 = 0;\n}\nreturn var1;\n"
        );
        let dup = "if (a1 != 0) {\n  if (a2 > 0 && a2 < 9) {\n    g32_1000 = a2;\n  } else {\n    sub_1(a1);\n  }\n} else {\n  sub_1(a1);\n}\n";
        assert_eq!(
            select_statements(dup),
            "if ((a1 != 0) && (a2 > 0 && a2 < 9)) {\n  g32_1000 = a2;\n} else {\n  sub_1(a1);\n}\n"
        );
    }
}
