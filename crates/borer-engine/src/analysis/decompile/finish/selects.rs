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
/// ([`and_chain`]); and a byte-wide flag a chain compares with zero is the
/// flag itself ([`quiet_flags`]).
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
        if and_chain(&mut lines, k) {
            changed = true;
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
/// comparison of its own.
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
    if !(line.contains(" && ") || line.contains(" || ")) {
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
/// when the variable is read nowhere but in the choice, so its new value
/// reaches no one else; the statement and the test call nothing, so the
/// test runs as early unseen; no loop or label surrounds the line, so the
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
                (!elsewhere && plain_assignment(t).is_none_or(|(lhs, _)| lhs != v))
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
/// call, a variable the test does not read: the test calls nothing and
/// reads none of them, so running them first changes nothing it sees.
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
                && plain_assignment(l).is_some_and(|(v, r)| !impure(r) && !mentions_ident(&cond, v))
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
/// such statement assigns, without a call, a variable no other line reads
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
    let Some(open) = lines.get(k) else {
        return false;
    };
    let pad = indent_of(open);
    let Some(a) = if_opener(open.trim()).map(str::to_owned) else {
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
                .filter(|(_, r)| indent_of(l) == pad + 2 && !impure(r))
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
    if temps.is_empty() || temps.len() != m - k - 1 || truth_of_temp {
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
        let simple = r
            .chars()
            .all(|c| is_ident_char(c) || c == '-' || c == '>' || c == '.');
        rename_word(&b, v, &if simple { r.clone() } else { format!("({r})") })
    });
    let term = |c: &str| {
        if c.contains(" || ") || c.contains(" ? ") {
            format!("({c})")
        } else {
            c.to_owned()
        }
    };
    let pad_s = " ".repeat(pad);
    let head = format!("{pad_s}if ({} && {}) {{", term(&a), term(&b));
    let body: Vec<String> = lines
        .get(m + 1..close - 1)
        .unwrap_or(&[])
        .iter()
        .map(|l| l.get(2..).unwrap_or(l.trim_start()).to_owned())
        .collect();
    let rewritten: Vec<String> = std::iter::once(head)
        .chain(body)
        .chain(std::iter::once(format!("{pad_s}}}")))
        .collect();
    lines.splice(k..=close, rewritten);
    true
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
    }
}
